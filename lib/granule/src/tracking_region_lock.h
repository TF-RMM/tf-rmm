/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef TRACKING_REGION_LOCK_H
#define TRACKING_REGION_LOCK_H

#include <tracking_region_pvt.h>

/*
 * This function acquires @tr's read lock and returns with it held. While
 * held, writers cannot change the region's tracking state or its active
 * coarse/fine representation.
 *
 * Caller requirements:
 * - When looking up and locking a struct granule or struct dev_granule,
 *   retain this read lock until the selected object's lock is acquired
 *   or the lookup fails. This prevents a tracking transition from replacing
 *   the object between lookup and locking.
 * - For a tracking-state query, retain it until the state has been read.
 * - Release it with tracking_region_read_unlock().
 */
static inline void tracking_region_read_lock(struct tracking_region *tr)
{
	rwlock_read_acquire(&tr->lock);
}

/* Release one read lock previously acquired for @tr. */
static inline void tracking_region_read_unlock(struct tracking_region *tr)
{
	rwlock_read_release(&tr->lock);
}

/* Return false without retaining the gate if any reader or writer is active. */
static inline bool tracking_region_write_try_lock(struct tracking_region *tr)
{
	return rwlock_write_try_acquire(&tr->lock);
}

/*
 * This function waits until @tr's write lock is acquired and returns with
 * it held. Between attempts, it does not retain the reader gate, allowing
 * existing readers to complete nested lookups.
 *
 * Caller requirements:
 * - Do not wait for granule locks while holding this write lock.
 * - Release the write lock with tracking_region_write_unlock().
 * - For tracking-representation changes, use
 *   tracking_region_write_try_lock() and try to acquire the source granule
 *   locks. Release all acquired locks on contention.
 */
static inline void tracking_region_write_lock(struct tracking_region *tr)
{
	rwlock_write_acquire(&tr->lock);
}

/* Publish the writer's updates and admit subsequent granule lookups. */
static inline void tracking_region_write_unlock(struct tracking_region *tr)
{
	rwlock_write_release(&tr->lock);
}

/*
 * Return a diagnostic snapshot of the region's writer bit. Callers must
 * establish their own locking contract; this does not prove PE ownership.
 */
static inline bool tracking_region_is_write_locked(
					const struct tracking_region *tr)
{
	return rwlock_is_write_locked(&tr->lock);
}

#endif /* TRACKING_REGION_LOCK_H */
