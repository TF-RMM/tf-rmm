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

static inline void spinlock_acquire(spinlock_t *l)
{
	host_spinlock_acquire(l);
}

static inline void spinlock_release(spinlock_t *l)
{
	host_spinlock_release(l);
}

typedef struct byte_spinlock_s {
	unsigned char val;
} byte_spinlock_t;

static inline void byte_spinlock_acquire(byte_spinlock_t *l)
{
	host_byte_spinlock_acquire(l);
}

static inline void byte_spinlock_release(byte_spinlock_t *l)
{
	host_byte_spinlock_release(l);
}

#endif /* SPINLOCK_H */
