/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef ATOMICS_H
#define ATOMICS_H

#include <stdbool.h>
#include <stdint.h>

/*
 * Atomically adds @val to the 64-bit value stored at memory location @loc.
 */
static inline void atomic_add_64(uint64_t *loc, uint64_t val)
{
	*loc += val;
}

/*
 * Atomically adds @val to the 64-bit value stored at memory location @loc.
 * Returns the old value.
 */
static inline uint64_t atomic_load_add_64(uint64_t *loc, uint64_t val)
{
	uint64_t old_val = *loc;

	*loc += val;
	return old_val;
}

/*
 * Atomically adds @val to the 64-bit value stored at memory location @loc.
 * Stores to memory with release semantics.
 * Returns the old value.
 */
static inline uint64_t atomic_load_add_release_64(uint64_t *loc, uint64_t val)
{
	uint64_t old_val = *loc;

	*loc += val;
	return old_val;
}

/*
 * Atomically adds @val to the 16-bit value stored at memory location @loc.
 */
static inline void atomic_add_16(uint16_t *loc, uint16_t val)
{
	*loc += val;
}

/*
 * Atomically adds @val to the 16-bit value stored at memory location @loc.
 * Returns the old value.
 */
static inline uint16_t atomic_load_add_16(uint16_t *loc, uint16_t val)
{
	uint16_t old_val = *loc;

	*loc += val;
	return old_val;
}

/*
 * Atomically adds @val to the 16-bit value stored at memory location @loc.
 * Stores to memory with release semantics.
 * Returns the old value.
 */
static inline uint16_t atomic_load_add_release_16(uint16_t *loc, uint16_t val)
{
	uint16_t old_val = *loc;

	*loc += val;
	return old_val;
}

/*
 * Atomically set bit @bit in value pointed to by @val with release semantics.
 */
static inline void atomic_bit_set_release_64(uint64_t *loc, unsigned int bit)
{
	uint64_t mask = (1UL << bit);

	*loc |= mask;
}

/*
 * Atomically clear bit @bit in value pointed to by @loc with release semantics.
 */
static inline void atomic_bit_clear_release_64(uint64_t *loc, unsigned int bit)
{
	uint64_t mask = ~((uint64_t)(1UL << bit));

	*loc &= mask;
}

/*
 * Test bit @bit in value pointed to by @loc with acquire semantics.
 */
static inline bool atomic_test_bit_acquire_64(uint64_t *loc, unsigned int bit)
{
	uint64_t val = *loc;
	uint64_t mask = (1UL << bit);

	return ((val & mask) != 0UL);
}

/*
 * Atomically set bit @bit in value pointed to by @val
 * with acquire and release semantics.
 * Return True if the previous state of @bit was 1, False otherwise.
 */
static inline bool atomic_bit_set_acquire_release_64(uint64_t *loc, unsigned int bit)
{
	uint64_t mask = (1UL << bit);
	uint16_t old_val = *loc & mask;

	*loc |= mask;
	return (old_val != 0UL);
}

/*
 * Atomically performs exclusive-OR with @val on the 16-bit value stored at memory
 * location @loc and stores the result back to memory.
 * Returns the old value.
 */
static inline uint16_t atomic_eor_16(uint16_t *loc, uint16_t val)
{
	uint16_t old_val = *loc;

	*loc ^= val;
	return old_val;
}

#endif /* ATOMICS_H */
