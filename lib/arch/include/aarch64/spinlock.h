/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef SPINLOCK_H
#define SPINLOCK_H

#include <stdbool.h>

/* Trivial spinlock implementations using compiler atomic builtins. */

/* 32-bit spinlock */
typedef struct {
	unsigned int val;
} spinlock_t;

/* Try to acquire @l without waiting, with acquire memory ordering. */
__attribute__((__always_inline__))
static inline bool spinlock_try_acquire(spinlock_t *l)
{
	unsigned int expected = 0U;

	return __atomic_compare_exchange_n(&l->val, &expected, 1U, false,
					   __ATOMIC_ACQUIRE,
					   __ATOMIC_RELAXED);
}

/* Wait until @l is observed unlocked without acquiring it. */
__attribute__((__always_inline__))
static inline void spinlock_wait(spinlock_t *l)
{
	/* To avoid misra-c2012-2.7 warnings */
	(void)l;
	unsigned int value;

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
	"2:\n"
	: [value] "=&r" (value)
	: [lock] "Q" (l->val)
	: "memory"
	);
}

__attribute__((__always_inline__))
static inline void spinlock_acquire(spinlock_t *l)
{
	do {
		/* Avoid issuing a CAS while the lock is observed as held. */
		spinlock_wait(l);
	} while (!spinlock_try_acquire(l));
}

__attribute__((__always_inline__))
static inline void spinlock_release(spinlock_t *l)
{
	__atomic_store_n(&l->val, 0U, __ATOMIC_RELEASE);
}

#endif /* SPINLOCK_H */
