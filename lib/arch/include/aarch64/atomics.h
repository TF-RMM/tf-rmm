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
	(void)__atomic_fetch_add(loc, val, __ATOMIC_RELAXED);
}

/*
 * Atomically adds @val to the 64-bit value stored at memory location @loc.
 * Stores to memory with release semantics.
 * Returns the old value.
 */
static inline uint64_t atomic_load_add_release_64(uint64_t *loc, uint64_t val)
{
	return __atomic_fetch_add(loc, val, __ATOMIC_RELEASE);
}

/*
 * Atomically adds @val to the 64-bit value stored at memory location @loc.
 * Stores to memory with acquire and release semantics.
 * Returns the old value.
 */
static inline uint64_t atomic_load_add_acquire_release_64(uint64_t *loc,
							   uint64_t val)
{
	return __atomic_fetch_add(loc, val, __ATOMIC_ACQ_REL);
}

/*
 * Atomically adds @val to the 16-bit value stored at memory location @loc.
 */
static inline void atomic_add_16(uint16_t *loc, uint16_t val)
{
	(void)__atomic_fetch_add(loc, val, __ATOMIC_RELAXED);
}

/*
 * Atomically adds @val to the 16-bit value stored at memory location @loc.
 * Returns the old value.
 */
static inline uint16_t atomic_load_add_16(uint16_t *loc, uint16_t val)
{
	return __atomic_fetch_add(loc, val, __ATOMIC_RELAXED);
}

/*
 * Atomically adds @val to the 64-bit value stored at memory location @loc.
 * Returns the old value.
 */
static inline uint64_t atomic_load_add_64(uint64_t *loc, uint64_t val)
{
	return __atomic_fetch_add(loc, val, __ATOMIC_RELAXED);
}

/*
 * Atomically adds @val to the 16-bit value stored at memory location @loc.
 * Stores to memory with release semantics.
 * Returns the old value.
 */
static inline uint16_t atomic_load_add_release_16(uint16_t *loc, uint16_t val)
{
	return __atomic_fetch_add(loc, val, __ATOMIC_RELEASE);
}

/*
 * Atomically adds @val to the 8-bit value stored at memory location @loc.
 * Returns the old value.
 */
static inline uint8_t atomic_load_add_8(uint8_t *loc, uint8_t val)
{
	return __atomic_fetch_add(loc, val, __ATOMIC_RELAXED);
}

/*
 * Atomically adds @val to the 8-bit value stored at memory location @loc.
 * Stores to memory with release semantics.
 * Returns the old value.
 */
static inline uint8_t atomic_load_add_release_8(uint8_t *loc, uint8_t val)
{
	return __atomic_fetch_add(loc, val, __ATOMIC_RELEASE);
}

/*
 * Atomically set bit @bit in value pointed to by @loc with release semantics.
 */
static inline void atomic_bit_set_release_64(uint64_t *loc, unsigned int bit)
{
	uint64_t mask = (1ULL << bit);

	(void)__atomic_fetch_or(loc, mask, __ATOMIC_RELEASE);
}

/*
 * Atomically clear bit @bit in value pointed to by @loc with release semantics.
 */
static inline void atomic_bit_clear_release_64(uint64_t *loc, unsigned int bit)
{
	uint64_t mask = (1ULL << bit);

	(void)__atomic_fetch_and(loc, ~mask, __ATOMIC_RELEASE);
}

/*
 * Test bit @bit in value pointed to by @loc with acquire semantics.
 */
static inline bool atomic_test_bit_acquire_64(uint64_t *loc, unsigned int bit)
{
	uint64_t val = __atomic_load_n(loc, __ATOMIC_ACQUIRE);
	uint64_t mask = (1ULL << bit);

	return ((val & mask) != 0UL);
}

/*
 * Atomically set bit @bit in value pointed to by @loc
 * with acquire and release semantics.
 * Return True if the previous state of @bit was 1, False otherwise.
 */
static inline bool atomic_bit_set_acquire_release_64(uint64_t *loc, unsigned int bit)
{
	uint64_t mask = (1ULL << bit);
	uint64_t val = __atomic_fetch_or(loc, mask, __ATOMIC_ACQ_REL);

	return ((val & mask) != 0UL);
}

/*
 * Atomic compare-and-swap with acquire and release semantics.
 * If *loc == expected, atomically sets *loc = desired and returns true.
 * Otherwise, returns false.
 */
static inline bool atomic_cas_acquire_release_64(uint64_t *loc,
						 uint64_t expected,
						 uint64_t desired)
{
	return __atomic_compare_exchange_n(loc, &expected, desired, false,
					   __ATOMIC_ACQ_REL,
					   __ATOMIC_ACQUIRE);
}

/*
 * Atomically performs exclusive-OR with @val on the 16-bit value stored at memory
 * location @loc and stores the result back to memory.
 * Returns the old value.
 */
static inline uint16_t atomic_eor_16(uint16_t *loc, uint16_t val)
{
	return __atomic_fetch_xor(loc, val, __ATOMIC_RELAXED);
}

/*
 * Atomically performs exclusive-OR with @val on the 8-bit value stored at memory
 * location @loc and stores the result back to memory.
 * Returns the old value.
 */
static inline uint8_t atomic_eor_8(uint8_t *loc, uint8_t val)
{
	return __atomic_fetch_xor(loc, val, __ATOMIC_RELAXED);
}

#endif /* ATOMICS_H */
