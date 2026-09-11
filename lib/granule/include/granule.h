/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef GRANULE_H
#define GRANULE_H

#include <assert.h>
#include <atomics.h>
#include <errno.h>
#include <granule_lock.h>
#include <memory.h>
#include <smc-rmi.h>
#include <stdbool.h>
#include <utils_def.h>

#ifndef CBMC
/* Maximum number of entries in an RTT */
#define RTT_REFCOUNT_MAX	(unsigned short)	\
					(GRANULE_SIZE / sizeof(uint64_t))

/* Maximum number of 64-byte STEs in a granule-sized PSMMU L2 Stream Table */
#define PSMMU_ST_L2_REFCOUNT_MAX	(unsigned short)(GRANULE_SIZE / U(64))

/* Maximum value defined by the 'refcount' field width in struct granule */
#define REFCOUNT_MAX		(unsigned short)	\
					((U(1) << GRN_REFCOUNT_WIDTH) - U(1))
#else /* CBMC */
#define RTT_REFCOUNT_MAX		((unsigned short)2)
#define PSMMU_ST_L2_REFCOUNT_MAX	((unsigned short)2)
#define REFCOUNT_MAX			((unsigned short)2)
#endif /* CBMC */

/* RTT_REFCOUNT_MAX can't exceed REFCOUNT_MAX */
COMPILER_ASSERT(RTT_REFCOUNT_MAX <= REFCOUNT_MAX);

/* PSMMU_ST_L2_REFCOUNT_MAX can't exceed REFCOUNT_MAX */
COMPILER_ASSERT(PSMMU_ST_L2_REFCOUNT_MAX <= REFCOUNT_MAX);

/* Granule bit-field access macros */
#define LOCKED(g)	\
	((SCA_READ16(&(g)->descriptor) & GRN_LOCK_BIT) != 0U)

#define REFCOUNT(g)	\
	(SCA_READ16(&(g)->descriptor) &	REFCOUNT_MASK)

#define STATE(g)	\
	(unsigned char)EXTRACT(GRN_STATE, SCA_READ16(&(g)->descriptor))

/*
 * Return refcount value using atomic read.
 */
static inline unsigned short granule_refcount_read(struct granule *g)
{
	assert(g != NULL);
	return REFCOUNT(g);
}

/*
 * Return refcount value using atomic read with acquire semantics.
 *
 * Must be called with granule lock held.
 */
static inline unsigned short granule_refcount_read_acquire(struct granule *g)
{
	assert((g != NULL) && LOCKED(g));
	return SCA_READ16_ACQUIRE(&g->descriptor) & REFCOUNT_MASK;
}

/*
 * Sanity-check unlocked granule invariants.
 * This check is performed just after acquiring the lock and/or just before
 * releasing the lock.
 *
 * These invariants must hold for any granule which is unlocked.
 *
 * These invariants may not hold transiently while a granule is locked (e.g.
 * when transitioning to/from delegated state).
 *
 * Note: this function is purely for debug/documentation purposes, and is not
 * intended as a mechanism to ensure correctness.
 */
static inline void __granule_assert_unlocked_invariants(struct granule *g,
							unsigned char state)
{
	(void)g;

	switch (state) {
	case GRANULE_STATE_NS:
		assert(REFCOUNT(g) == 0U);
		break;
	case GRANULE_STATE_DELEGATED:
		assert(REFCOUNT(g) == 0U);
		break;
	case GRANULE_STATE_PARTIAL:
		assert(REFCOUNT(g) == 0U);
		break;
	case GRANULE_STATE_RD:
		/*
		 * Refcount is used to check if RD and associated granules can
		 * be freed because they're no longer referenced by any other
		 * object. Refcount number is always less or equal to
		 * REFCOUNT_MAX value.
		 */
		break;
	case GRANULE_STATE_REC:
		assert(REFCOUNT(g) <= 1U);
		break;
	case GRANULE_STATE_DATA:
		assert(REFCOUNT(g) < MAX_TOTAL_PLANES);
		break;
	case GRANULE_STATE_RTT:
		/* Refcount cannot be greater than number of entries in an RTT */
		assert(REFCOUNT(g) <= RTT_REFCOUNT_MAX);
		break;
	case GRANULE_STATE_REC_AUX:
		assert(REFCOUNT(g) == 0U);
		break;
	case GRANULE_STATE_PDEV:
		assert(REFCOUNT(g) <= 1U);
		break;
	case GRANULE_STATE_PDEV_AUX:
		assert(REFCOUNT(g) == 0U);
		break;
	case GRANULE_STATE_VDEV:
		assert(REFCOUNT(g) <= 1U);
		break;
	case GRANULE_STATE_VDEV_AUX:
		assert(REFCOUNT(g) == 0U);
		break;
	case GRANULE_STATE_INTERNAL:
		assert(REFCOUNT(g) == 0U);
		break;
	case GRANULE_STATE_PSMMU_ST_L2:
		assert(REFCOUNT(g) <= PSMMU_ST_L2_REFCOUNT_MAX);
		break;
	case GRANULE_STATE_RD_AUX:
		assert(REFCOUNT(g) == 0U);
		break;
	default:
		/* Unknown granule type */
		assert(false);
	}
}

/*
 * Return the state of unlocked granule.
 * This function should be used only for NS granules where RMM performs NS
 * specific operations on the granule.
 */
static inline unsigned char granule_unlocked_state(struct granule *g)
{
	assert(g != NULL);

	/* NOLINTNEXTLINE(clang-analyzer-core.NullDereference) */
	return STATE(g);
}

/* Must be called with granule lock held */
static inline unsigned char granule_get_state(struct granule *g)
{
	assert((g != NULL) && LOCKED(g));

	/* NOLINTNEXTLINE(clang-analyzer-core.NullDereference) */
	return STATE(g);
}

/* Must be called with granule lock held */
static inline void __granule_set_state(struct granule *g, unsigned char state)
{
	unsigned short val;

	assert((g != NULL) && LOCKED(g));

	/* NOLINTNEXTLINE(clang-analyzer-core.NullDereference) */
	val = g->descriptor & STATE_MASK;

	/* cppcheck-suppress misra-c2012-10.3 */
	val ^= (unsigned short)state << GRN_STATE_SHIFT;

	/*
	 * Atomically EOR val while keeping the bits for refcount and
	 * bitlock as 0 which would preserve their values in memory.
	 */
	(void)atomic_eor_16(&g->descriptor, val);
}

/*
 * Acquire @g only while its state matches @expected_state.
 *
 * The caller must keep the granule stable and obey the state, address and
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
static inline bool granule_lock_on_state_match(struct granule *g,
						unsigned char expected_state)
{
	assert(g != NULL);

	for (;;) {
		if (STATE(g) != expected_state) {
			return false;
		}
		if (granule_bitlock_try_acquire(g)) {
			if (granule_get_state(g) != expected_state) {
				granule_bitlock_release(g);
				return false;
			}

			__granule_assert_unlocked_invariants(g, expected_state);
			return true;
		}

		/*
		 * Another PE may acquire the lock after a state change
		 * before we observe the unlock. Include state in the wait
		 * condition so the STATE(g) check above can reject a
		 * mismatch even if the lock has already been taken again.
		 */
		granule_bitlock_wait(g, expected_state);
	}
}

/*
 * Acquire @g through a protected reference, returning with its lock held.
 *
 * The caller must keep the granule stable and establish the locking order
 * independently of its current state. Wait unconditionally so an in-progress
 * transition to @expected_state can finish, then assert that state and check
 * its invariants. A state mismatch after acquisition is a programming error.
 */
static inline void granule_lock(struct granule *g,
				unsigned char expected_state)
{
	granule_bitlock_acquire(g);

	assert(granule_get_state(g) == expected_state);
	__granule_assert_unlocked_invariants(g, expected_state);
}

static inline void granule_unlock(struct granule *g)
{
	__granule_assert_unlocked_invariants(g, granule_get_state(g));
	granule_bitlock_release(g);
}

/*
 * Transition to @new_state and unlock @g.
 *
 * A transition to DELEGATED is valid only from NS, after a synchronous EL3
 * transition, or from PARTIAL when an SRO publishes completed EL3 progress.
 */
static inline void granule_unlock_transition(struct granule *g,
					     unsigned char new_state)
{
	/*
	 * Restrict this function for transitions to non-delegated states.
	 * NS and PARTIAL are the only states which can enter DELEGATED.
	 */
	assert((new_state != GRANULE_STATE_DELEGATED) ||
	       (granule_get_state(g) == GRANULE_STATE_NS) ||
	       (granule_get_state(g) == GRANULE_STATE_PARTIAL));

	__granule_set_state(g, new_state);
	granule_unlock(g);
}

/*
 * Return the PA represented by fine granule @g. The caller must supply a valid
 * fine granule and keep its representation alive. No locks are acquired; an
 * invalid granule violates this contract and is asserted.
 */
unsigned long tr_granule_addr(const struct granule *g);

/*
 * Return the fine granule for conventional @addr. The caller must supply a
 * Granule-aligned address in a configured conventional bank and keep the fine
 * representation alive. No locks are acquired; an invalid address violates
 * this contract and is asserted.
 */
struct granule *tr_addr_to_granule(unsigned long addr);

/*
 * Find and lock a granule for @addr in @expected_state. @tracking_size selects
 * the coarse or fine representation. The tracking-region read lock stabilizes
 * selection until the granule lock is acquired. Return RMI_ERROR_INPUT for an
 * invalid address, size or Granule state, RMI_BLOCKED for a pending tracking
 * SRO, or encoded RMI_ERROR_TRACKING for an inactive representation.
 * The caller may perform further lookups while holding the returned granule,
 * provided that Granule locks follow the documented state and address order.
 */
unsigned long tr_find_lock_granule(unsigned long addr,
				   unsigned long tracking_size,
				   unsigned char expected_state,
				   struct granule **g);

/*
 * Find and lock one granule in the active fine or coarse representation.
 * @addr must be Granule aligned; @g and @tracking_size must be non-NULL.
 * On RMI_SUCCESS, *@g is locked in @expected_state and *@tracking_size reports
 * GRANULE_SIZE for fine tracking or the configured region size for coarse
 * tracking. The region read lock covers size discovery through granule
 * locking so the returned size describes the locked representation.
 *
 * For range operations, the caller must use the returned size to validate
 * alignment, range extent and any S2TT block before changing granule state.
 * Return an encoded RMI_ERROR_TRACKING containing @addr when the region has no
 * usable representation, RMI_BLOCKED for a pending tracking SRO, or
 * RMI_ERROR_INPUT for an invalid address or Granule-state mismatch. On failure,
 * leave *@g NULL and *@tracking_size unspecified.
 *
 * An SRO caller must yield and retry on RMI_BLOCKED without waiting while
 * holding other Granule locks. On success the caller owns only *@g's lock.
 * Keep it through processing and any state change to exclude tracking
 * transitions and transition claims.
 */
unsigned long tr_find_lock_active_granule(unsigned long addr,
					  unsigned char expected_state,
					  struct granule **g,
					  unsigned long *tracking_size);

/*
 * Lock the longest run of fine granules beginning at @addr that are all in
 * @expected_state. The run is bounded by @end_addr, the current tracking region,
 * a memory-bank boundary, or the first granule in another state.
 * @count receives the number of locked granules. The caller owns the locks for
 * [@addr, @addr + (@count * GRANULE_SIZE)) and must release them in PA order or
 * reverse PA order. Each state is validated before lock acquisition and
 * revalidated after contention. Returns an encoded tracking-aware RMI result.
 */
unsigned long tr_find_lock_fine_granule_run(unsigned long addr,
					     unsigned long end_addr,
					     unsigned char expected_state,
					     unsigned long *count);

/*
 * Lock a granule for a range in either @source_state or @target_state.
 * The states must differ and all output pointers must be non-NULL.
 * The caller must hold no Granule lock. On RMI_SUCCESS, @g is locked,
 * @tracking_size identifies the active representation, and @in_target reports
 * whether the granule is in @target_state. Return the tracking-aware lookup
 * error with no lock held on failure; the outputs are then unspecified.
 */
unsigned long granule_range_lock_conventional(
					unsigned long addr,
					unsigned char source_state,
					unsigned char target_state,
					struct granule **g,
					unsigned long *tracking_size,
					bool *in_target);

/*
 * Publish delegation progress for a locked run of fine granules.
 * The caller owns @locked_count consecutive NS granules starting at aligned
 * @addr, with @delegated_count <= @locked_count. Change the delegated prefix to
 * DELEGATED. Change the remaining granules to PARTIAL if @incomplete, or
 * leave them NS otherwise. Release every granule lock in ascending PA order
 * without acquiring a region reader. The caller must retain ownership of any
 * PARTIAL granules until their PAS transition completes or rolls back.
 */
void granule_range_delegate_fine_unlock(unsigned long addr,
						unsigned long locked_count,
						unsigned long delegated_count,
						bool incomplete);

/*
 * Publish [@addr, @addr + @size) from PARTIAL as DELEGATED or NS.
 * Both arguments must be Granule aligned. @device selects dev_granules when
 * true, or granules otherwise. @delegated selects DELEGATED rather than NS.
 * The caller must own every PARTIAL granule in the range, pinning fine
 * tracking even while a representation transition is pending, and hold no
 * Granule lock. Acquire and release each granule in ascending PA order
 * without entering a region reader gate.
 */
void granule_delegate_fine_transition(unsigned long addr,
				      unsigned long size,
				      bool device, bool delegated);

/*
 * Publish a coarse granule or dev_granule from PARTIAL as DELEGATED or NS.
 * @addr must be aligned to the configured region size, supplied as
 * @tracking_size. @device selects dev_granules when true, or granules
 * otherwise; @delegated selects DELEGATED rather than NS. The caller must own
 * the PARTIAL granule, pinning its coarse representation, and hold no
 * Granule lock. Acquire its lock without entering a region reader gate and
 * release it after publishing the state.
 */
void granule_delegate_coarse_transition(unsigned long addr,
					unsigned long tracking_size,
					bool device, bool delegated);

/*
 * Publish a completed PAS transition by changing an owned granule or
 * dev_granule to NS. @addr must be aligned to @tracking_size, which selects
 * the fine or coarse representation. @device selects dev_granules when true,
 * or granules otherwise. The caller must have completed sanitization where
 * required and returned the entire tracking unit to Non-secure PAS. It must
 * own the PARTIAL granule, pinning its state and representation, and hold
 * no Granule lock. Acquire and release the granule lock without entering a
 * region reader gate.
 */
void granule_range_undelegate_commit(unsigned long addr,
				     unsigned long tracking_size,
				     bool device);

/*
 * Release @count locked fine DELEGATED granules or dev_granules in PA order.
 * The caller owns the run beginning at Granule-aligned @addr. @device selects
 * dev_granules when true, or granules otherwise. If an SRO was @reserved,
 * publish PARTIAL before releasing each lock so the SRO retains the range and
 * its tracking representation across a yield. Otherwise leave the granules
 * DELEGATED. No region reader is acquired.
 */
void granule_range_undelegate_fine_unlock(unsigned long addr, unsigned long count,
					bool device, bool reserved);


/*
 * Return an unlocked fine granule for @addr, or NULL on lookup failure.
 * The caller must protect its representation and metadata from before lookup
 * until granule access ends or its lock is acquired. Retain ownership that
 * pins the representation, or ensure tracking transitions cannot run concurrently.
 * A non-NULL result alone does not protect its lifetime.
 */
struct granule *tr_find_fine_granule(unsigned long addr);

/*
 * Find and lock two independently addressed fine granules in global state
 * order and then PA order. Both addresses must be Granule aligned and the
 * output locations must be non-NULL. Respect the order of any locks already
 * held. RTT, DATA and auxiliary granules require their own hierarchy and
 * ownership rules instead of this independent-address ordering.
 *
 * Return RMI_SUCCESS with both granules locked in their expected states,
 * RMI_BLOCKED for a pending tracking SRO, encoded RMI_ERROR_TRACKING with the
 * failing PA if fine tracking is unavailable, or RMI_ERROR_INPUT for an invalid
 * address, duplicate address or Granule state. On failure, leave both outputs
 * NULL and no additional locks held.
 */
unsigned long tr_find_lock_two_fine_granules(unsigned long addr1,
					     unsigned char expected_state1,
					     struct granule **g1,
					     unsigned long addr2,
					     unsigned char expected_state2,
					     struct granule **g2);

/*
 * Find and lock three independently addressed fine granules in global state
 * and PA order. The address, output and locking contracts, and return values,
 * are the same as tr_find_lock_two_fine_granules(). On failure, leave all three
 * outputs NULL and no additional locks held.
 */
unsigned long tr_find_lock_three_fine_granules(
			unsigned long addr1,
			unsigned char expected_state1,
			struct granule **g1,
			unsigned long addr2,
			unsigned char expected_state2,
			struct granule **g2,
			unsigned long addr3,
			unsigned char expected_state3,
			struct granule **g3);

void granule_memzero_mapped(void *buf);
void granule_dcci_poe(struct granule *g);

/*
 * Perform the PoE cache maintenance required before returning every Granule
 * in [@addr, @addr + @size) to DELEGATED. Both values must be Granule
 * aligned. The operation is a no-op when FEAT_MEC is absent.
 */
void granule_dcci_poe_range(unsigned long addr, unsigned long size);

void granule_sanitize_mapped(void *buf);
void granule_sanitize_1_mapped(void *buf);

/*
 * Helper to transition a granule to DELEGATED state. This function
 * does the necessary Cache maintenance to PoE when FEAT_MEC is present.
 * There should not be any live mapping for this granule on any CPU
 * when this function is called.
 * Note that this API is not to be used for NS -> DELEGATED transition.
 */
static inline void granule_unlock_transition_to_delegated(struct granule *g)
{
	assert((g != NULL) && LOCKED(g));

	unsigned char current_state __unused = granule_get_state(g);

	/* Transition from DELEGATED to DELEGATED is invalid */
	assert(current_state != GRANULE_STATE_DELEGATED);
	/* This function is not to be used for NS -> DELEGATED transition */
	assert(current_state != GRANULE_STATE_NS);
	granule_dcci_poe(g);
	/* Set new state to DELEGATED */
	__granule_set_state(g, GRANULE_STATE_DELEGATED);

	granule_unlock(g);
}

/*
 * Refcount field occupies LSB bits of struct granule,
 * and functions which modify its value can operate directly on
 * the whole 16-bit word without masking, provided that the result
 * doesn't exceed REFCOUNT_MAX or set to negative number.
 */

/*
 * Atomically increments the reference counter of the granule by @val.
 *
 * Must be called with granule lock held.
 */
static inline void granule_refcount_inc(struct granule *g, unsigned short val)
{
	uint16_t old_refcount __unused;

	assert((g != NULL) && LOCKED(g));
	old_refcount = atomic_load_add_16(&g->descriptor, val) & REFCOUNT_MASK;
	assert((old_refcount + val) <= REFCOUNT_MAX);
}

/*
 * Atomically increments the reference counter of the granule.
 *
 * Must be called with granule lock held.
 */
static inline void atomic_granule_get(struct granule *g)
{
	granule_refcount_inc(g, 1U);
}

/*
 * Atomically decrements the reference counter of the granule by @val.
 *
 * Must be called with granule lock held.
 */
static inline void granule_refcount_dec(struct granule *g, unsigned short val)
{
	uint16_t old_refcount __unused;

	assert((g != NULL) && LOCKED(g));

	/* coverity[misra_c_2012_rule_10_1_violation:SUPPRESS] */
	old_refcount = atomic_load_add_16(&g->descriptor, (uint16_t)(-val)) &
							REFCOUNT_MASK;
	assert(old_refcount >= val);
}

/*
 * Atomically decrements the reference counter of the granule.
 *
 * Must be called with granule lock held.
 */
static inline void atomic_granule_put(struct granule *g)
{
	granule_refcount_dec(g, 1U);
}

/*
 * Atomically decrements the reference counter of the granule.
 * Stores to memory with release semantics.
 */
static inline void atomic_granule_put_release(struct granule *g)
{
	uint16_t old_refcount __unused;

	assert(g != NULL);
	old_refcount = atomic_load_add_release_16(&g->descriptor,
						(uint16_t)(-1)) & REFCOUNT_MASK;
	assert(old_refcount != 0U);
}

/*
 * Returns 'true' if granule is locked, 'false' otherwise
 *
 * This function is only meant to be used for verification and testing,
 * and this functionlaity is not required for RMM operations.
 */
static inline bool is_granule_locked(struct granule *g)
{
	assert(g != NULL);
	return LOCKED(g);
}

#endif /* GRANULE_H */
