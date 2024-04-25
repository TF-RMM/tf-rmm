/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef GRANULE_LOCK_H
#define GRANULE_LOCK_H

#include <assert.h>
#include <granule_types.h>

static inline void granule_bitlock_acquire(struct granule *g)
{
	/*
	 * The fake_host architecture is single threaded and we do not expect
	 * the lock to be already acquired in properly implemented locking
	 * sequence.
	 */
	assert((g->descriptor & GRN_LOCK_BIT) == 0);
	g->descriptor |= GRN_LOCK_BIT;
}

static inline void granule_bitlock_release(struct granule *g)
{
	g->descriptor &= ~GRN_LOCK_BIT;
}

#endif /* GRANULE_LOCK_H */
