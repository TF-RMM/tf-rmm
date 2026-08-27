/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef GRANULE_LOCK_H
#define GRANULE_LOCK_H

#include <bitlock.h>
#include <granule_types.h>
#include <stdbool.h>

/* Try to acquire @g without waiting. */
static inline bool granule_bitlock_try_acquire(struct granule *g)
{
	return bitlock_try_acquire_16(&g->descriptor, GRN_LOCK_SHIFT);
}

/*
 * Wait without acquiring @g until it is unlocked or leaves @expected_state.
 * The caller must keep @g's descriptor stable throughout the wait.
 */
static inline void granule_bitlock_wait(struct granule *g,
				       unsigned char expected_state)
{
	uint16_t mask = (uint16_t)(GRN_LOCK_BIT | STATE_MASK);
	uint16_t value = (uint16_t)(GRN_LOCK_BIT |
				((unsigned int)expected_state << GRN_STATE_SHIFT));

	bitlock_wait_while_16(&g->descriptor, mask, value);
}

static inline void granule_bitlock_acquire(struct granule *g)
{
	bitlock_acquire_16(&g->descriptor, GRN_LOCK_SHIFT);
}

static inline void granule_bitlock_release(struct granule *g)
{
	bitlock_release_16(&g->descriptor, GRN_LOCK_SHIFT);
}

/* Try to acquire device @g without waiting. */
static inline bool dev_granule_bitlock_try_acquire(struct dev_granule *g)
{
	return bitlock_try_acquire_8(&g->descriptor, DEV_GRN_LOCK_SHIFT);
}

/*
 * Wait without acquiring device @g until it is unlocked or leaves
 * @expected_state. The caller must keep @g's descriptor stable throughout.
 */
static inline void dev_granule_bitlock_wait(struct dev_granule *g,
					   unsigned char expected_state)
{
	uint8_t mask = (uint8_t)(DEV_GRN_LOCK_BIT | DEV_STATE_MASK);
	uint8_t value = (uint8_t)(DEV_GRN_LOCK_BIT |
			    ((unsigned int)expected_state << DEV_GRN_STATE_SHIFT));

	bitlock_wait_while_8(&g->descriptor, mask, value);
}

static inline void dev_granule_bitlock_acquire(struct dev_granule *g)
{
	bitlock_acquire_8(&g->descriptor, DEV_GRN_LOCK_SHIFT);
}

static inline void dev_granule_bitlock_release(struct dev_granule *g)
{
	bitlock_release_8(&g->descriptor, DEV_GRN_LOCK_SHIFT);
}

#endif /* GRANULE_LOCK_H */
