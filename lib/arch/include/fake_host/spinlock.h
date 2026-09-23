/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef SPINLOCK_H
#define SPINLOCK_H

#include <assert.h>
#include <host_harness.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <utils_def.h>

typedef struct spinlock_s {
	unsigned int val;
} spinlock_t;

/*
 * Try to acquire @l without waiting, with acquire memory ordering.
 *
 * @l must be non-NULL and its 32-bit lock word @l->val naturally aligned.
 * Return true with the lock owned by the caller, or false if already held.
 */
static inline bool spinlock_try_acquire(spinlock_t *l)
{
	assert(l != NULL);
	assert(ALIGNED((uintptr_t)&l->val, sizeof(l->val)));

	return host_spinlock_try_acquire(l);
}

/*
 * Wait until a relaxed load observes @l unlocked, without acquiring it.
 *
 * @l must be non-NULL and its 32-bit lock word @l->val naturally aligned.
 * The fake-host implementation does not model PE wait events.
 */
static inline void spinlock_wait(spinlock_t *l)
{
	assert(l != NULL);
	assert(ALIGNED((uintptr_t)&l->val, sizeof(l->val)));

	host_spinlock_wait(l);
}

/*
 * Acquire @l with acquire ordering in the single-thread host.
 *
 * @l must be non-NULL and its 32-bit lock word @l->val naturally aligned.
 * The lock must initially be free; contention cannot make progress here.
 * Return with the lock owned by the caller.
 */
static inline void spinlock_acquire(spinlock_t *l)
{
	assert(l != NULL);
	assert(ALIGNED((uintptr_t)&l->val, sizeof(l->val)));

	host_spinlock_acquire(l);
}

/*
 * Release caller-owned @l, publishing protected updates with release ordering.
 *
 * @l must be non-NULL and its 32-bit lock word @l->val naturally aligned.
 */
static inline void spinlock_release(spinlock_t *l)
{
	assert(l != NULL);
	assert(ALIGNED((uintptr_t)&l->val, sizeof(l->val)));

	host_spinlock_release(l);
}

#endif /* SPINLOCK_H */
