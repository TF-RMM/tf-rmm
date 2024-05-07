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
#include <stdbool.h>
#include <utils_def.h>

/* Maximum number of entries in an RTT */
#define RTT_REFCOUNT_MAX	(unsigned short)	\
					(GRANULE_SIZE / sizeof(uint64_t))

/* Maximum value defined by the 'refcount' field width in granule descriptor */
#define REFCOUNT_MAX		(unsigned short)	\
					((U(1) << GRN_REFCOUNT_WIDTH) - U(1))

/* RTT_REFCOUNT_MAX can't exceed REFCOUNT_MAX */
COMPILER_ASSERT(RTT_REFCOUNT_MAX <= REFCOUNT_MAX);

/* Granule descriptor fields access macros */
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
	switch (state) {
	case GRANULE_STATE_NS:
		assert(REFCOUNT(g) == 0U);
		break;
	case GRANULE_STATE_DELEGATED:
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
		assert(REFCOUNT(g) == 0U);
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
static inline void granule_set_state(struct granule *g, unsigned char state)
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
 * Acquire the bitlock and then check expected state
 * Fails if unexpected locking sequence detected.
 * Also asserts if invariant conditions are met.
 */
static inline bool granule_lock_on_state_match(struct granule *g,
						unsigned char expected_state)
{
	granule_bitlock_acquire(g);

	if (granule_get_state(g) != expected_state) {
		granule_bitlock_release(g);
		return false;
	}

	__granule_assert_unlocked_invariants(g, expected_state);
	return true;
}

/*
 * Used when we're certain of the type of an object (e.g. because we hold a
 * reference to it). In these cases we should never fail to acquire the lock.
 */
static inline void granule_lock(struct granule *g,
				unsigned char expected_state)
{
	__unused bool locked = granule_lock_on_state_match(g, expected_state);

	assert(locked);
}

static inline void granule_unlock(struct granule *g)
{
	__granule_assert_unlocked_invariants(g, granule_get_state(g));
	granule_bitlock_release(g);
}

/* Transtion state to @new_state and unlock the granule */
static inline void granule_unlock_transition(struct granule *g,
					     unsigned char new_state)
{
	granule_set_state(g, new_state);
	granule_unlock(g);
}

unsigned long granule_addr(const struct granule *g);
struct granule *addr_to_granule(unsigned long addr);
struct granule *find_granule(unsigned long addr);
struct granule *find_lock_granule(unsigned long addr,
				  unsigned char expected_state);

bool find_lock_two_granules(unsigned long addr1,
			    unsigned char expected_state1,
			    struct granule **g1,
			    unsigned long addr2,
			    unsigned char expected_state2,
			    struct granule **g2);

void granule_memzero_mapped(void *buf);

/*
 * Refcount field occupies LSB bits of the granule descriptor,
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
 * Atomically increments the reference counter of the granule by @val.
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
 * Obtain a pointer to a locked unused granule at @addr if @addr is a valid
 * granule physical address, the state of the granule at @addr is
 * @expected_state, and the granule at @addr is unused.
 *
 * Returns:
 * 0, @*g - address of the granule,
 *	if @addr is a valid granule physical address.
 * -EINVAL, @*g = NULL,
 *	if @addr is not aligned to the size of a granule,
 *	@addr is out of range, or if the state of the granule at @addr
 *	is not @expected_state.
 * -EBUSY, @*g = NULL,
 *	if the granule at @addr has a non-zero reference count.
 */
static inline int find_lock_unused_granule(unsigned long addr,
					   unsigned char expected_state,
					   struct granule **g)
{
	*g = find_lock_granule(addr, expected_state);
	if (*g == NULL) {
		return -EINVAL;
	}

	/*
	 * Granules can have lock-free access (e.g. REC), thus using acquire
	 * semantics to avoid race conditions.
	 */
	if (granule_refcount_read_acquire(*g) != 0U) {
		granule_unlock(*g);
		*g = NULL;
		return -EBUSY;
	}

	return 0;
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
