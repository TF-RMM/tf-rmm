/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef SPINLOCK_H
#define SPINLOCK_H

#include <assert.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <utils_def.h>

/* Trivial spinlock implementations using compiler atomic builtins. */

/* 32-bit spinlock */
typedef struct {
	unsigned int val;
} spinlock_t;

/*
 * Try to acquire @l without waiting, with acquire memory ordering.
 *
 * @l must be non-NULL and its 32-bit lock word @l->val naturally aligned.
 * Return true with the lock owned by the caller, or false if already held.
 */
__attribute__((__always_inline__))
static inline bool spinlock_try_acquire(spinlock_t *l)
{
	unsigned int expected = 0U;

	assert(l != NULL);
	assert(ALIGNED((uintptr_t)&l->val, sizeof(l->val)));

	return __atomic_compare_exchange_n(&l->val, &expected, 1U, false,
					   __ATOMIC_ACQUIRE,
					   __ATOMIC_RELAXED);
}

/*
 * Wait until @l is observed unlocked without acquiring it.
 *
 * @l must be non-NULL and its 32-bit lock word @l->val naturally aligned.
 * Return after a relaxed observation of an unlocked value, with the local
 * exclusive monitor cleared.
 */
__attribute__((__always_inline__))
static inline void spinlock_wait(spinlock_t *l)
{
	unsigned int value;

	/* To avoid misra-c2012-2.7 warnings */
	(void)l;

	assert(l != NULL);
	assert(ALIGNED((uintptr_t)&l->val, sizeof(l->val)));

	/*
	 * Establish an exclusive reservation before waiting so that the
	 * releasing PE's store generates an event and wakes this PE.
	 */
	/* cppcheck-suppress misra-c2012-17.3 */
	asm volatile(
	"1:	ldxr	%w[value], %[lock]\n"
	"	cbz	%w[value], 2f\n"
	"	wfe\n"
	"	b	1b\n"
	"2:	clrex\n"
	: [value] "=&r" (value)
	: [lock] "Q" (l->val)
	: "memory"
	);
}

/*
 * Acquire @l with acquire ordering, waiting while another PE holds it.
 *
 * @l must be non-NULL and its 32-bit lock word @l->val naturally aligned.
 * Return with the lock owned by the caller.
 */
__attribute__((__always_inline__))
static inline void spinlock_acquire(spinlock_t *l)
{
	assert(l != NULL);
	assert(ALIGNED((uintptr_t)&l->val, sizeof(l->val)));

	do {
		/* Avoid issuing a CAS while the lock is observed as held. */
		spinlock_wait(l);
	} while (!spinlock_try_acquire(l));
}

/*
 * Release caller-owned @l, publishing protected updates with release ordering.
 *
 * @l must be non-NULL and its 32-bit lock word @l->val naturally aligned.
 */
__attribute__((__always_inline__))
static inline void spinlock_release(spinlock_t *l)
{
	assert(l != NULL);
	assert(ALIGNED((uintptr_t)&l->val, sizeof(l->val)));

	__atomic_store_n(&l->val, 0U, __ATOMIC_RELEASE);
}

#endif /* SPINLOCK_H */
