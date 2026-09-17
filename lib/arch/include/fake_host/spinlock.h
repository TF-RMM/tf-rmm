/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef SPINLOCK_H
#define SPINLOCK_H

#include <host_harness.h>

typedef struct spinlock_s {
	unsigned int val;
} spinlock_t;

/* Try to acquire @l without waiting. */
static inline bool spinlock_try_acquire(spinlock_t *l)
{
	return host_spinlock_try_acquire(l);
}

/* Wait until @l is observed unlocked without acquiring it. */
static inline void spinlock_wait(spinlock_t *l)
{
	host_spinlock_wait(l);
}

static inline void spinlock_acquire(spinlock_t *l)
{
	host_spinlock_acquire(l);
}

static inline void spinlock_release(spinlock_t *l)
{
	host_spinlock_release(l);
}

#endif /* SPINLOCK_H */
