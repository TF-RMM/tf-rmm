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
#include <stdbool.h>
#include <utils_def.h>

/* Maximum value defined by the 'refcount' field width in dev_granule descriptor */
#define DEV_REFCOUNT_MAX	(unsigned char)	\
					((U(1) << DEV_GRN_REFCOUNT_WIDTH) - U(1))

/* Dev Granule descriptor fields access macros */
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
	return DEV_REFCOUNT(g);
}

/*
 * Return refcount value using atomic read with acquire semantics.
 *
 * Must be called with dev_granule lock held.
 */
static inline unsigned char dev_granule_refcount_read_acquire(struct dev_granule *g)
{
	assert((g != NULL) && DEV_LOCKED(g));
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
		assert(DEV_REFCOUNT(g) == 0U);
		break;
	case DEV_GRANULE_STATE_DELEGATED:
		assert(DEV_REFCOUNT(g) == 0U);
		break;
	case DEV_GRANULE_STATE_MAPPED:
		assert(DEV_REFCOUNT(g) == 0U);
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
static inline unsigned char dev_granule_unlocked_state(struct granule *g)
{
	assert(g != NULL);

	/* NOLINTNEXTLINE(clang-analyzer-core.NullDereference) */
	return DEV_STATE(g);
}

/* Must be called with dev_granule lock held */
static inline unsigned char dev_granule_get_state(struct dev_granule *g)
{
	assert((g != NULL) && DEV_LOCKED(g));

	/* NOLINTNEXTLINE(clang-analyzer-core.NullDereference) */
	return DEV_STATE(g);
}

/* Must be called with dev_granule lock held */
static inline void dev_granule_set_state(struct dev_granule *g, unsigned char state)
{
	unsigned char val;

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
 * Acquire the bitlock and then check expected state
 * Fails if unexpected locking sequence detected.
 * Also asserts if invariant conditions are met.
 */
static inline bool dev_granule_lock_on_state_match(struct dev_granule *g,
						   unsigned char expected_state)
{
	dev_granule_bitlock_acquire(g);

	if (dev_granule_get_state(g) != expected_state) {
		dev_granule_bitlock_release(g);
		return false;
	}

	__dev_granule_assert_unlocked_invariants(g, expected_state);
	return true;
}

/*
 * Used when we're certain of the type of an object (e.g. because we hold a
 * reference to it). In these cases we should never fail to acquire the lock.
 */
static inline void dev_granule_lock(struct dev_granule *g,
					unsigned char expected_state)
{
	__unused bool locked = dev_granule_lock_on_state_match(g, expected_state);

	assert(locked);
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
 * Takes a valid pointer to a struct dev_granule, corresponding to dev_type
 * and returns the dev_granule physical address.
 *
 * This is purely a lookup, and provides no guarantees about the attributes of
 * the dev_granule (i.e. whether it is locked, its state or its reference count).
 */
unsigned long dev_granule_addr(const struct dev_granule *g, enum dev_type type);

/*
 * Takes an aligned dev_granule address, returns a pointer to the corresponding
 * struct dev_granule and sets device granule type in address passed in @type.
 *
 * This is purely a lookup, and provides no guarantees about the attributes of
 * the granule (i.e. whether it is locked, its state or its reference count).
 */
struct dev_granule *addr_to_dev_granule(unsigned long addr, enum dev_type *type);

/*
 * Verifies whether @addr is a valid dev_granule physical address, returns
 * a pointer to the corresponding struct dev_granule and sets device granule type.
 *
 * This is purely a lookup, and provides no guarantees w.r.t the state of the
 * granule (e.g. locking).
 *
 * Returns:
 *     Pointer to the struct dev_granule if @addr is a valid dev_granule physical
 *     address and device granule type in address passed in @type.
 *     NULL if any of:
 *     - @addr is not aligned to the size of a granule.
 *     - @addr is out of range.
 */
struct dev_granule *find_dev_granule(unsigned long addr, enum dev_type *type);

/*
 * Obtain a pointer to a locked dev_granule at @addr if @addr is a valid dev_granule
 * physical address and the state of the dev_granule at @addr is @expected_state and
 * set device granule type.
 *
 * Returns:
 *	A valid dev_granule pointer if @addr is a valid dev_granule physical address
 *	and device granule type in address passed in @type.
 *	NULL if any of:
 *	- @addr is not aligned to the size of a granule.
 *	- @addr is out of range.
 *	- if the state of the dev_granule at @addr is not @expected_state.
 */
struct dev_granule *find_lock_dev_granule(unsigned long addr,
					  unsigned char expected_state,
					  enum dev_type *type);
/*
 * Refcount field occupies LSB bits of the dev_granule descriptor,
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
	return DEV_LOCKED(g);
}

#endif /* DEV_GRANULE_H */
