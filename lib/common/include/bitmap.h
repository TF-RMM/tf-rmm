/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 * SPDX-FileCopyrightText: Copyright (c) 2025 NVIDIA CORPORATION & AFFILIATES. All rights reserved.
 */

#ifndef BITMAP_H
#define BITMAP_H

#include <errno.h>
#include <sizes.h>
#include <stdbool.h>

/*
 * Returns the index of the first bit set in @bitmap from @start inclusive.
 * The index is zero-based from LSB (0) to MSB (63).
 * When no such bits are set, returns BITS_PER_UL (64).
 */
static inline unsigned long bitmap_find_next_set_bit(unsigned long bitmap,
						     unsigned long start)
{
	if (start < BITS_PER_UL) {
		bitmap &= ~0UL << start;
		if (bitmap != 0UL) {
			return (unsigned long)(__builtin_ffsl((long)bitmap) - 1);
		}
	}
	return BITS_PER_UL;
}

#define bitmap_for_each_set_bit(_bit, _bitmap, _max)		\
	for ((_bit) = find_next_set_bit((_bitmap), 0);		\
	     (_bit) < (_max);					\
	     (_bit) = find_next_set_bit((_bitmap), (_bit) + 1))

/*
 * Returns the index of the first bit clear in @bitmap from @start inclusive.
 * The index is zero-based from LSB (0) to MSB (63).
 * When no such bits are set, returns BITS_PER_UL (64).
 */
static inline unsigned long bitmap_find_next_clear_bit(unsigned long bitmap,
						       unsigned long start)
{
	if (start < BITS_PER_UL) {
		bitmap &= ~0UL << start;
		if (bitmap != ~0UL) {
			return (unsigned long)(__builtin_ctzl((long)~bitmap));
		}
	}
	return BITS_PER_UL;
}

/*
 * Sets or clears the @bitpos bit in the @bitmap array,
 * which consists of @nums elements of type unsigned long.
 * The boolean @set parameter specifies whether the bit should be
 * set (true) or cleared (false).
 * If the bit is already in the requested state, or if @bitpos is
 * outside the bounds of the @bitmap array, the function returns an error.
 * The caller is responsible for ensuring that the bitmap array
 * is properly locked.
 */
static inline int bitmap_update(unsigned long *bitmap,
				unsigned int bitpos,
				unsigned int nums,
				bool set)
{
	if (bitpos < (nums * BITS_PER_UL)) {
		unsigned int idx = bitpos / BITS_PER_UL;
		unsigned int bit = bitpos % BITS_PER_UL;
		unsigned long mask = (1UL << bit);
		bool bit_clr = (bitmap[idx] & mask) == 0UL;

		/* Ensure that the bit is set/cleared */
		if (bit_clr == set) {
			bitmap[idx] ^= mask;
			return 0;
		}
	}

	return -EINVAL;
}

#endif /* BITMAP_H */
