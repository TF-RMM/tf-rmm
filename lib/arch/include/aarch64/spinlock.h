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

__attribute__((__always_inline__))
static inline void spinlock_acquire(spinlock_t *l)
{
	unsigned int expected = 0U;

	while (!__atomic_compare_exchange_n(&l->val, &expected, 1U, false,
					    __ATOMIC_ACQUIRE,
					    __ATOMIC_RELAXED)) {
		expected = 0U;
	}
}

__attribute__((__always_inline__))
static inline void spinlock_release(spinlock_t *l)
{
	__atomic_store_n(&l->val, 0U, __ATOMIC_RELEASE);
}

#endif /* SPINLOCK_H */
