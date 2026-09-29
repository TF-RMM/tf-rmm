/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef DEV_GRANULE_H
#define DEV_GRANULE_H

#include <assert.h>
#include <atomics.h>
#include <dev_type.h>
#include <errno.h>
#include <granule_lock.h>
#include <memory.h>
#include <smc-rmi.h>
#include <stdbool.h>
#include <utils_def.h>

/* Maximum value defined by the 'refcount' field width in struct dev_granule */
#define DEV_REFCOUNT_MAX	(unsigned char)	\
					((U(1) << DEV_GRN_REFCOUNT_WIDTH) - U(1))

/* dev_granule bit-field access macros */
#define DEV_LOCKED(g)	\
	((SCA_READ8(&(g)->descriptor) & DEV_GRN_LOCK_BIT) != 0U)

#define DEV_REFCOUNT(g)	\
	(SCA_READ8(&(g)->descriptor) & DEV_REFCOUNT_MASK)

#define DEV_STATE(g)	\
	(unsigned char)EXTRACT(DEV_GRN_STATE, SCA_READ8(&(g)->descriptor))

/*
 * Return refcount value using atomic read.
 */
static inline unsigned char dev_granule_refcount_read(struct dev_granule *g)
{
	assert(g != NULL);

	/* cppcheck-suppress misra-c2012-17.3 */
	return DEV_REFCOUNT(g);
}

/*
 * Return refcount value using atomic read with acquire semantics.
 *
 * Must be called with dev_granule lock held.
 */
static inline unsigned char dev_granule_refcount_read_acquire(struct dev_granule *g)
{
	/* cppcheck-suppress misra-c2012-17.3 */
	assert((g != NULL) && DEV_LOCKED(g));

	/* cppcheck-suppress misra-c2012-17.3 */
	return SCA_READ8_ACQUIRE(&g->descriptor) & DEV_REFCOUNT_MASK;
}

/*
 * Sanity-check unlocked dev_granule invariants.
 * This check is performed just after acquiring the lock and/or just before
 * releasing the lock.
 *
 * These invariants must hold for any dev_granule which is unlocked.
 *
 * These invariants may not hold transiently while a dev_granule is locked (e.g.
 * when transitioning to/from delegated state).
 *
 * Note: this function is purely for debug/documentation purposes, and is not
 * intended as a mechanism to ensure correctness.
 */
static inline void __dev_granule_assert_unlocked_invariants(struct dev_granule *g,
							    unsigned char state)
{
	(void)g;

	switch (state) {
	case DEV_GRANULE_STATE_NS:
		/* cppcheck-suppress misra-c2012-17.3 */
		assert(DEV_REFCOUNT(g) == 0U);
		break;
	case DEV_GRANULE_STATE_DELEGATED:
		/* cppcheck-suppress misra-c2012-17.3 */
		assert(DEV_REFCOUNT(g) == 0U);
		break;
	case DEV_GRANULE_STATE_PARTIAL:
		/* cppcheck-suppress misra-c2012-17.3 */
		assert(DEV_REFCOUNT(g) == 0U);
		break;
	case DEV_GRANULE_STATE_MAPPED:
		/* Every representable refcount is valid for a mapped granule. */
		break;
	default:
		/* Unknown dev_granule type */
		assert(false);
	}
}

/*
 * Return the state of unlocked dev_granule.
 * This function should be used only for NS dev_granules where RMM performs NS
 * specific operations on the granule.
 */
static inline unsigned char dev_granule_unlocked_state(struct dev_granule *g)
{
	assert(g != NULL);

	/* NOLINTNEXTLINE(clang-analyzer-core.NullDereference) */
	/* cppcheck-suppress misra-c2012-17.3 */
	return DEV_STATE(g);
}

/* Must be called with dev_granule lock held */
static inline unsigned char dev_granule_get_state(struct dev_granule *g)
{
	/* cppcheck-suppress misra-c2012-17.3 */
	assert((g != NULL) && DEV_LOCKED(g));

	/* NOLINTNEXTLINE(clang-analyzer-core.NullDereference) */
	/* cppcheck-suppress misra-c2012-17.3 */
	return DEV_STATE(g);
}

/* Must be called with dev_granule lock held */
static inline void dev_granule_set_state(struct dev_granule *g, unsigned char state)
{
	unsigned char val;

	/* cppcheck-suppress misra-c2012-17.3 */
	assert((g != NULL) && DEV_LOCKED(g));

	/* NOLINTNEXTLINE(clang-analyzer-core.NullDereference) */
	val = g->descriptor & DEV_STATE_MASK;

	/* cppcheck-suppress misra-c2012-10.3 */
	val ^= state << DEV_GRN_STATE_SHIFT;

	/*
	 * Atomically EOR val while keeping the bits for refcount and
	 * bitlock as 0 which would preserve their values in memory.
	 */
	(void)atomic_eor_8(&g->descriptor, val);
}

/*
 * Acquire @g only while its state matches @expected_state.
 *
 * The caller must keep the dev_granule stable and obey the state, address and
 * RTT hierarchy ordering rules for all locks it already holds. Independently
 * supplied expected states are permitted when acquired in that order.
 *
 * Check the state before acquisition and throughout contention, so an
 * unexpected state cannot introduce a lock-order inversion. Recheck after
 * acquiring the lock to close the race with the unlocked read.
 *
 * Return true with @g locked in @expected_state, or false without holding
 * its lock on a state mismatch. The caller must release any earlier locks
 * when abandoning a collection after a mismatch.
 */
static inline bool dev_granule_lock_on_state_match(struct dev_granule *g,
						unsigned char expected_state)
{
	assert(g != NULL);

	for (;;) {
		if (DEV_STATE(g) != expected_state) {
			return false;
		}
		if (dev_granule_bitlock_try_acquire(g)) {
			if (dev_granule_get_state(g) != expected_state) {
				dev_granule_bitlock_release(g);
				return false;
			}

			__dev_granule_assert_unlocked_invariants(g,
							 expected_state);
			return true;
		}

		/*
		 * Another PE may acquire the lock after a state change
		 * before we observe the unlock. Include state in the wait
		 * condition so the DEV_STATE(g) check above can reject a
		 * mismatch even if the lock has already been taken again.
		 */
		dev_granule_bitlock_wait(g, expected_state);
	}
}

/*
 * Acquire @g through a protected reference, returning with its lock held.
 *
 * The caller must keep the dev_granule stable and establish the locking order
 * independently of its current state. Wait unconditionally so an in-progress
 * transition to @expected_state can finish, then assert that state and check
 * its invariants. A state mismatch after acquisition is a programming error.
 */
static inline void dev_granule_lock(struct dev_granule *g,
					unsigned char expected_state)
{
	dev_granule_bitlock_acquire(g);

	assert(dev_granule_get_state(g) == expected_state);
	__dev_granule_assert_unlocked_invariants(g, expected_state);
}

static inline void dev_granule_unlock(struct dev_granule *g)
{
	__dev_granule_assert_unlocked_invariants(g, dev_granule_get_state(g));
	dev_granule_bitlock_release(g);
}

/* Transtion state to @new_state and unlock the dev_granule */
static inline void dev_granule_unlock_transition(struct dev_granule *g,
						 unsigned char new_state)
{
	dev_granule_set_state(g, new_state);
	dev_granule_unlock(g);
}

/*
 * Find and lock one dev_granule in the active fine or coarse representation.
 * @addr must be Granule aligned; @g, @type and @tracking_size must be non-NULL.
 * On RMI_SUCCESS, *@g is locked in @expected_state, *@type reports its coherency
 * type and *@tracking_size reports GRANULE_SIZE for fine tracking or the
 * configured region size for coarse tracking. The region read lock covers
 * size discovery through dev_granule locking so the returned size describes
 * the locked representation.
 *
 * For range operations, the caller must use the returned size to validate
 * alignment, range extent and any S2TT block before changing dev_granule state.
 * Return an encoded RMI_ERROR_TRACKING containing @addr when the region has no
 * usable representation, RMI_BLOCKED for a pending tracking SRO, or
 * RMI_ERROR_INPUT for an invalid address or Granule-state mismatch. On failure,
 * leave *@g NULL; *@type and *@tracking_size are unspecified.
 *
 * An SRO caller must yield and retry on RMI_BLOCKED without waiting while
 * holding other Granule locks. On success the caller owns only *@g's lock.
 * Keep it through processing and any state change to exclude tracking
 * transitions and transition claims.
 */
unsigned long tr_find_lock_active_dev_granule(
					unsigned long addr,
					unsigned char expected_state,
					struct dev_granule **g,
					enum dev_coh_type *type,
					unsigned long *tracking_size);

/*
 * Lock the longest run of fine dev_granules beginning at @addr that are all in
 * @expected_state and have one coherency type. The run is bounded by @end_addr,
 * the current tracking region, a memory-bank or coherency boundary, or the
 * first dev_granule in another state. @count receives the number of locked
 * dev_granules and @type receives their coherency type. The caller owns the
 * locks for the returned PA range. Each state is validated before lock
 * acquisition and revalidated after contention.
 * Returns an encoded tracking-aware RMI result.
 */
unsigned long tr_find_lock_fine_dev_granule_run(
					unsigned long addr,
					unsigned long end_addr,
					unsigned char expected_state,
					enum dev_coh_type *type,
					unsigned long *count);

/*
 * Lock a dev_granule for a range in either @source_state or @target_state.
 * The states must differ and all output pointers must be non-NULL.
 * On RMI_SUCCESS, @g is locked, @tracking_size identifies the active
 * representation, and @in_target reports whether it is in @target_state. The
 * caller must hold no Granule lock. Return the tracking-aware lookup error with
 * no lock held on failure; the outputs are then unspecified. Lookup validates
 * the device coherency type, which is not otherwise needed by this operation.
 */
unsigned long granule_range_lock_device(unsigned long addr,
					unsigned char source_state,
					unsigned char target_state,
					struct dev_granule **g,
					unsigned long *tracking_size,
					bool *in_target);

/*
 * Publish delegation progress for a locked run of fine dev_granules.
 * The caller owns @locked_count consecutive NS dev_granules starting at aligned
 * @addr, with @delegated_count <= @locked_count. Change the delegated prefix to
 * DELEGATED. Change the remaining dev_granules to PARTIAL if @incomplete, or
 * leave them NS otherwise. Release every dev_granule lock in ascending PA order
 * without acquiring a region reader. The caller must retain ownership of any
 * PARTIAL dev_granules until their PAS transition completes or rolls back.
 */
void granule_range_delegate_fine_dev_unlock(unsigned long addr,
					    unsigned long locked_count,
					    unsigned long delegated_count,
					    bool incomplete);

/*
 * Refcount field occupies LSB bits of struct dev_granule,
 * and functions which modify its value can operate directly on
 * the whole 8-bit word without masking, provided that the result
 * doesn't exceed DEV_REFCOUNT_MAX or set to negative number.
 */

/*
 * Atomically increments the reference counter of the granule by @val.
 *
 * Must be called with granule lock held.
 */
static inline void dev_granule_refcount_inc(struct dev_granule *g,
					    unsigned char val)
{
	uint8_t old_refcount __unused;

	/* cppcheck-suppress misra-c2012-17.3 */
	assert((g != NULL) && DEV_LOCKED(g));
	old_refcount = atomic_load_add_8(&g->descriptor, val) &
							DEV_REFCOUNT_MASK;
	assert((old_refcount + val) <= DEV_REFCOUNT_MAX);
}

/*
 * Atomically increments the reference counter of the granule.
 *
 * Must be called with granule lock held.
 */
static inline void atomic_dev_granule_get(struct dev_granule *g)
{
	dev_granule_refcount_inc(g, 1U);
}

/*
 * Atomically increments the reference counter of the dev_granule by @val.
 *
 * Must be called with dev_granule lock held.
 */
static inline void dev_granule_refcount_dec(struct dev_granule *g, unsigned char val)
{
	uint8_t old_refcount __unused;

	/* cppcheck-suppress misra-c2012-17.3 */
	assert((g != NULL) && DEV_LOCKED(g));

	/* coverity[misra_c_2012_rule_10_1_violation:SUPPRESS] */
	old_refcount = atomic_load_add_8(&g->descriptor, (uint8_t)(-val)) &
							DEV_REFCOUNT_MASK;
	assert(old_refcount >= val);
}

/*
 * Atomically decrements the reference counter of the dev_granule.
 *
 * Must be called with dev_granule lock held.
 */
static inline void atomic_dev_granule_put(struct dev_granule *g)
{
	dev_granule_refcount_dec(g, 1U);
}

/*
 * Atomically decrements the reference counter of the dev_granule.
 * Stores to memory with release semantics.
 */
static inline void atomic_dev_granule_put_release(struct dev_granule *g)
{
	uint8_t old_refcount __unused;

	assert(g != NULL);
	old_refcount = atomic_load_add_release_8(&g->descriptor,
					(uint8_t)(-1)) & DEV_REFCOUNT_MASK;
	assert(old_refcount != 0U);
}

/*
 * Returns 'true' if dev_granule is locked, 'false' otherwise
 *
 * This function is only meant to be used for verification and testing,
 * and this functionlaity is not required for RMM operations.
 */
static inline bool is_dev_granule_locked(struct dev_granule *g)
{
	assert(g != NULL);

	/* cppcheck-suppress misra-c2012-17.3 */
	return DEV_LOCKED(g);
}

#endif /* DEV_GRANULE_H */
