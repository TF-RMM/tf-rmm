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
	/* To avoid misra-c2012-2.7 warnings */
	(void)loc;
	(void)val;

	asm volatile(
	"	stadd %[val], %[loc]\n"
	: [loc] "+Q" (*loc)
	: [val] "r" (val)
	: "memory");
}

/*
 * Atomically adds @val to the 64-bit value stored at memory location @loc.
 * Stores to memory with release semantics.
 * Returns the old value.
 */
static inline uint64_t atomic_load_add_release_64(uint64_t *loc, uint64_t val)
{
	uint64_t old_val;

	/* To avoid misra-c2012-2.7 warnings */
	(void)loc;
	(void)val;

	asm volatile(
	"	ldaddl %[val], %[old_val], %[loc]\n"
	: [loc] "+Q" (*loc),
	  [old_val] "=r" (old_val)
	: [val] "r" (val)
	: "memory");

	return old_val;
}

/*
 * Atomically adds @val to the 16-bit value stored at memory location @loc.
 */
static inline void atomic_add_16(uint16_t *loc, uint16_t val)
{
	/* To avoid misra-c2012-2.7 warnings */
	(void)loc;
	(void)val;

	asm volatile(
	"	staddh %w[val], %[loc]\n"
	: [loc] "+Q" (*loc)
	: [val] "r" (val)
	: "memory");
}

/*
 * Atomically adds @val to the 16-bit value stored at memory location @loc.
 * Returns the old value.
 */
static inline uint16_t atomic_load_add_16(uint16_t *loc, uint16_t val)
{
	uint16_t old_val;

	/* To avoid misra-c2012-2.7 warnings */
	(void)loc;
	(void)val;

	asm volatile(
	"	ldaddh %w[val], %w[old_val], %[loc]\n"
	: [loc] "+Q" (*loc),
	  [old_val] "=r" (old_val)
	: [val] "r" (val)
	: "memory");

	return old_val;
}

/*
 * Atomically adds @val to the 64-bit value stored at memory location @loc.
 * Returns the old value.
 */
static inline uint64_t atomic_load_add_64(uint64_t *loc, uint64_t val)
{
	uint64_t old_val;

	/* To avoid misra-c2012-2.7 warnings */
	(void)loc;
	(void)val;

	asm volatile(
	"	ldadd %[val], %[old_val], %[loc]\n"
	: [loc] "+Q" (*loc),
	  [old_val] "=r" (old_val)
	: [val] "r" (val)
	: "memory");

	return old_val;
}

/*
 * Atomically adds @val to the 16-bit value stored at memory location @loc.
 * Stores to memory with release semantics.
 * Returns the old value.
 */
static inline uint16_t atomic_load_add_release_16(uint16_t *loc, uint16_t val)
{
	uint16_t old_val;

	/* To avoid misra-c2012-2.7 warnings */
	(void)loc;
	(void)val;

	asm volatile(
	"	ldaddlh %w[val], %w[old_val], %[loc]\n"
	: [loc] "+Q" (*loc),
	  [old_val] "=r" (old_val)
	: [val] "r" (val)
	: "memory");

	return old_val;
}

/*
 * Atomically set bit @bit in value pointed to by @loc with release semantics.
 */
static inline void atomic_bit_set_release_64(uint64_t *loc, unsigned int bit)
{
	uint64_t mask = (1ULL << bit);

	/* To avoid misra-c2012-2.7 warnings */
	(void)loc;
	(void)bit;

	asm volatile(
	"	stsetl %[mask], %[loc]\n"
	: [loc] "+Q" (*loc)
	: [mask] "r" (mask)
	: "memory"
	);
}

/*
 * Atomically clear bit @bit in value pointed to by @loc with release semantics.
 */
static inline void atomic_bit_clear_release_64(uint64_t *loc, unsigned int bit)
{
	uint64_t mask = (1ULL << bit);

	/* To avoid misra-c2012-2.7 warnings */
	(void)loc;
	(void)bit;

	asm volatile(
	"	stclrl %[mask], %[loc]\n"
	: [loc] "+Q" (*loc)
	: [mask] "r" (mask)
	: "memory"
	);
}

/*
 * Test bit @bit in value pointed to by @loc with acquire semantics.
 */
static inline bool atomic_test_bit_acquire_64(uint64_t *loc, unsigned int bit)
{
	uint64_t val;
	uint64_t mask = (1ULL << bit);

	/* To avoid misra-c2012-2.7 warnings */
	(void)loc;
	(void)bit;

	asm volatile(
	"	ldar %[val], %[loc]\n"
	: [val] "=r" (val)
	: [loc] "Q" (*loc)
	: "memory"
	);

	return ((val & mask) != 0UL);
}

/*
 * Atomically set bit @bit in value pointed to by @loc
 * with acquire and release semantics.
 * Return True if the previous state of @bit was 1, False otherwise.
 */
static inline bool atomic_bit_set_acquire_release_64(uint64_t *loc, unsigned int bit)
{
	uint64_t val;
	uint64_t mask = (1ULL << bit);

	/* To avoid misra-c2012-2.7 warnings */
	(void)loc;
	(void)bit;

	asm volatile(
	"	ldsetal %[mask], %[val], %[loc]\n"
	: [loc] "+Q" (*loc),
	  [val] "=r" (val)
	: [mask] "r" (mask)
	: "memory"
	);

	return ((val & mask) != 0UL);
}

/*
 * Atomically performs exclusive-OR with @val on the 16-bit value stored at memory
 * location @loc and stores the result back to memory.
 * Returns the old value.
 */
static inline uint16_t atomic_eor_16(uint16_t *loc, uint16_t val)
{
	uint16_t old_val;

	/* To avoid misra-c2012-2.7 warnings */
	(void)loc;
	(void)val;

	asm volatile(
	"	ldeorh %w[val], %w[old_val], %[loc]\n"
	: [loc] "+Q" (*loc),
	  [old_val] "=r" (old_val)
	: [val] "r" (val)
	: "memory"
	);

	return old_val;
}

#endif /* ATOMICS_H */
