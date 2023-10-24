/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef BITMAP_H
#define BITMAP_H

#include <sizes.h>

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

#endif /* BITMAP_H */
