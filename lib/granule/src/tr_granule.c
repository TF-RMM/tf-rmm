/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <assert.h>
#include <dev_granule.h>
#include <granule.h>
#include <memory.h>
#include <status.h>
#include <stddef.h>
#include <stdint.h>
#include <tracking_region_lock.h>
#include <tracking_region_pvt.h>
#include <utils_def.h>

#define TR_GRANULE_SET_MAX	U(3)

/* Return whether @size selects the configured coarse or fine granularity. */
static bool tr_tracking_size_valid(unsigned long size)
{
	return (size == GRANULE_SIZE) ||
	       (size == tracking_region_get_size());
}

/*
 * For RMI_ERROR_TRACKING, encode the failing PA @addr and tracking level 0,
 * since intermediate tracking levels are not yet supported.
 * Return all other statuses unchanged, including RMI_BLOCKED when a
 * pending tracking operation must complete before retrying.
 */
static unsigned long tr_encode_lookup_result(unsigned long ret,
					      unsigned long addr)
{
	if (ret == RMI_ERROR_TRACKING) {
		return pack_return_code_level_addr(RMI_ERROR_TRACKING,
						   (unsigned char)0U, addr);
	}

	return ret;
}

/* Return the active granularity, or RMI_BLOCKED for a pending SRO, with @tr stable. */
static unsigned long tr_active_tracking_size(struct tracking_region *tr,
					     unsigned long *tracking_size)
{
	enum tr_state state;

	assert((tr != NULL) && (tracking_size != NULL));
	if (tracking_region_transition_pending(tr)) {
		return RMI_BLOCKED;
	}

	state = tracking_region_get_state(tr);
	if (state == trs_fine) {
		*tracking_size = GRANULE_SIZE;
		return RMI_SUCCESS;
	}
	if (state == trs_coarse) {
		*tracking_size = tracking_region_get_size();
		return RMI_SUCCESS;
	}

	/* NONE and RESERVED do not provide a usable struct granule or struct dev_granule. */
	return RMI_ERROR_TRACKING;
}

/* Convert an exact RMI device memory category to its coherency type. */
static enum dev_coh_type tr_dev_granule_coh_type(unsigned long category)
{
	assert((category == RMI_MEM_CATEGORY_DEV_COH) ||
	       (category == RMI_MEM_CATEGORY_DEV_NCOH));

	return (category == RMI_MEM_CATEGORY_DEV_COH) ?
		DEV_MEM_COHERENT : DEV_MEM_NON_COHERENT;
}

/*
 * Return the PA represented by fine granule @g. The caller must supply a valid
 * fine granule and keep its representation alive. No locks are acquired; an
 * invalid granule violates this contract and is asserted.
 */
/* cppcheck-suppress misra-c2012-8.7 */
unsigned long tr_granule_addr(const struct granule *g)
{
	unsigned long addr;
	unsigned long idx;

	assert(g != NULL);
	idx = tr_fine_granule_to_idx(g);
	addr = tracking_region_fine_idx_to_addr(idx, TR_MEM_TYPE_CONV,
						  NULL);
	assert(addr != UINT64_MAX);

	return addr;
}

/*
 * Return the PA represented by fine dev_granule @g. The caller must supply a
 * valid fine dev_granule and keep its representation alive. @type must match
 * the device bank's coherency type. No locks are acquired; invalid inputs
 * violate this contract and are asserted.
 */
/* cppcheck-suppress misra-c2012-8.7 */
unsigned long tr_dev_granule_addr(const struct dev_granule *g,
				  enum dev_coh_type type)
{
	unsigned long category;
	unsigned long addr;
	unsigned long idx;

	(void)type;

	assert(g != NULL);
	idx = tr_fine_dev_granule_to_idx(g);
	addr = tracking_region_fine_idx_to_addr(idx, TR_MEM_TYPE_DEV,
						  &category);
	assert(addr != UINT64_MAX);
	assert(type == tr_dev_granule_coh_type(category));

	return addr;
}

/*
 * Return the fine granule for conventional @addr. The caller must supply a
 * Granule-aligned address in a configured conventional bank and keep the fine
 * representation alive. No locks are acquired; an invalid address violates
 * this contract and is asserted.
 */
struct granule *tr_addr_to_granule(unsigned long addr)
{
	unsigned long idx;

	assert(GRANULE_ALIGNED(addr));
	idx = tracking_region_fine_addr_to_idx(addr, TR_MEM_TYPE_CONV,
						  NULL);
	assert(idx != UINT64_MAX);
	return tr_fine_granule_from_idx(idx);
}

/*
 * Return the fine dev_granule for device @addr and its coherency type through
 * non-NULL @type. The caller must supply a Granule-aligned address in a
 * configured device bank and keep the fine representation alive. Lookup
 * failure violates this contract and is asserted.
 */
struct dev_granule *tr_addr_to_dev_granule(unsigned long addr,
					   enum dev_coh_type *type)
{
	unsigned long category;
	unsigned long idx;

	assert(type != NULL);
	assert(GRANULE_ALIGNED(addr));

	idx = tracking_region_fine_addr_to_idx(addr, TR_MEM_TYPE_DEV,
						  &category);
	assert(idx != UINT64_MAX);
	*type = tr_dev_granule_coh_type(category);
	return tr_fine_dev_granule_from_idx(idx);
}

/*
 * Lock an already-owned granule in @expected_state.
 *
 * The caller's ownership must keep the granule and its tracking
 * representation alive through lock acquisition. For example, an SRO owns
 * its PARTIAL granules across continuations, preventing a pending tracking
 * transition from replacing their granules or reclaiming their metadata.
 * Return the locked granule without taking a tracking-region read lock
 * or rejecting a pending transition. See tracking_region_pvt.h for the
 * ownership and locking requirements.
 */
struct granule *tr_lock_owned_granule(unsigned long addr,
		unsigned long tracking_size, unsigned char expected_state)
{
	struct tracking_region *tr = tracking_region_find(addr, TR_MEM_TYPE_CONV);
	struct granule *g;

	assert((tr != NULL) && GRANULE_ALIGNED(addr));
	assert(tr_tracking_size_valid(tracking_size));
	if (tracking_size == GRANULE_SIZE) {
		assert(tracking_region_get_state(tr) == trs_fine);
		g = tr_addr_to_granule(addr);
	} else {
		assert(tracking_region_get_state(tr) == trs_coarse);
		g = &tr->coarse_granule;
	}
	granule_lock(g, expected_state);
	return g;
}

/*
 * Lock an already-owned dev_granule in @expected_state.
 *
 * The caller's ownership must keep the dev_granule and its tracking
 * representation alive through lock acquisition. Return the locked dev_granule
 * without taking a tracking-region read lock or rejecting a pending transition.
 * See tracking_region_pvt.h for the ownership and locking requirements.
 */
struct dev_granule *tr_lock_owned_dev_granule(unsigned long addr,
		unsigned long tracking_size, unsigned char expected_state)
{
	struct tracking_region *tr = tracking_region_find(addr, TR_MEM_TYPE_DEV);
	struct dev_granule *g;
	enum dev_coh_type type;

	assert((tr != NULL) && GRANULE_ALIGNED(addr));
	assert(tr_tracking_size_valid(tracking_size));
	if (tracking_size == GRANULE_SIZE) {
		assert(tracking_region_get_state(tr) == trs_fine);
		g = tr_addr_to_dev_granule(addr, &type);
	} else {
		assert(tracking_region_get_state(tr) == trs_coarse);
		g = &tr->coarse_dev_granule;
	}
	dev_granule_lock(g, expected_state);
	return g;
}

/*
 * Select the granule for @addr at @tracking_size.
 *
 * @tr must cover @addr, which must be Granule aligned. The caller validates
 * that @tracking_size is GRANULE_SIZE (fine) or the configured region size
 * (coarse). Coarse selection returns the region's shared coarse granule.
 *
 * This helper takes no locks and does not check the Granule state. A caller
 * that uses the granule must prevent tracking transitions, for example by
 * retaining @tr's read lock until the granule lock has been acquired.
 * Otherwise, the returned pointer is only a transient selection.
 *
 * Return RMI_SUCCESS with *@g set, RMI_BLOCKED for a pending tracking SRO,
 * RMI_ERROR_TRACKING if the requested representation is inactive, or
 * RMI_ERROR_INPUT if fine address lookup fails. Leave *@g NULL on failure.
 */
static unsigned long tr_select_granule(struct tracking_region *tr,
				       unsigned long addr,
				       unsigned long tracking_size,
				       struct granule **g)
{
	unsigned long idx;

	assert((tr != NULL) && (g != NULL));
	*g = NULL;
	if (tracking_region_transition_pending(tr)) {
		return RMI_BLOCKED;
	}

	if (tracking_size == tracking_region_get_size()) {
		if (tracking_region_get_state(tr) != trs_coarse) {
			return RMI_ERROR_TRACKING;
		}

		*g = &tr->coarse_granule;
		return RMI_SUCCESS;
	}
	if (tracking_region_get_state(tr) != trs_fine) {
		return RMI_ERROR_TRACKING;
	}

	idx = tracking_region_fine_addr_to_idx(addr, TR_MEM_TYPE_CONV,
						  NULL);
	if (idx == UINT64_MAX) {
		return RMI_ERROR_INPUT;
	}

	*g = tr_fine_granule_from_idx(idx);
	return RMI_SUCCESS;
}

/*
 * Select the dev_granule for @addr at @tracking_size.
 *
 * @tr must cover @addr, which must be Granule aligned. The caller validates
 * that @tracking_size is GRANULE_SIZE (fine) or the configured region size
 * (coarse). Coarse selection returns the region's shared coarse dev_granule.
 * The bank lookup supplies the coherency type for either representation.
 *
 * This helper takes no locks and does not check the dev_granule state.
 * A caller that uses the granule must prevent tracking transitions, for
 * example by retaining @tr's read lock until the granule lock has been
 * acquired. Otherwise, the returned pointer is only a transient selection.
 *
 * Return RMI_SUCCESS with *@g set and *@type identifying device coherency.
 * Return RMI_BLOCKED for a pending tracking SRO, RMI_ERROR_TRACKING if the
 * requested representation is inactive, or RMI_ERROR_INPUT if device address
 * lookup fails. Leave *@g NULL on failure; *@type is then unspecified.
 */
static unsigned long tr_select_dev_granule(struct tracking_region *tr,
					   unsigned long addr,
					   unsigned long tracking_size,
					   struct dev_granule **g,
					   enum dev_coh_type *type)
{
	unsigned long category;
	unsigned long idx;

	assert((tr != NULL) && (g != NULL) && (type != NULL));
	*g = NULL;
	if (tracking_region_transition_pending(tr)) {
		return RMI_BLOCKED;
	}

	/*
	 * Both fine and coarse tracking need the bank category to return the
	 * device coherency type. This lookup only reads struct tracking_memory_bank
	 * and calculates an index; it does not access the fine-granule array.
	 */
	idx = tracking_region_fine_addr_to_idx(addr, TR_MEM_TYPE_DEV,
						  &category);
	if (idx == UINT64_MAX) {
		return RMI_ERROR_INPUT;
	}

	*type = tr_dev_granule_coh_type(category);
	if (tracking_size == tracking_region_get_size()) {
		if (tracking_region_get_state(tr) != trs_coarse) {
			return RMI_ERROR_TRACKING;
		}

		*g = &tr->coarse_dev_granule;
		return RMI_SUCCESS;
	}
	if (tracking_region_get_state(tr) != trs_fine) {
		return RMI_ERROR_TRACKING;
	}

	*g = tr_fine_dev_granule_from_idx(idx);
	return RMI_SUCCESS;
}

/*
 * Look up a granule for @addr at @tracking_size.
 *
 * No tracking-region or granule lock is acquired. RMI_SUCCESS only reports
 * a selection; it does not keep the struct granule or its backing alive. A caller
 * that accesses the result must prevent tracking transitions from before this
 * call until it finishes using the granule or acquires its lock. Use a
 * region reader, existing ownership that pins the representation, or an
 * environment where transitions cannot run concurrently. For an unowned input
 * PA, use tr_find_lock_granule() to select and lock the granule together.
 *
 * Return RMI_SUCCESS with *@g set. On failure, leave *@g NULL and return
 * RMI_ERROR_INPUT for an invalid address or tracking size, RMI_BLOCKED for a
 * pending tracking SRO, or encoded RMI_ERROR_TRACKING containing @addr for a
 * representation mismatch. The Granule state is not validated.
 */
unsigned long tr_find_granule(unsigned long addr,
			      unsigned long tracking_size,
			      struct granule **g)
{
	struct tracking_region *tr;

	assert(g != NULL);
	*g = NULL;

	if (!GRANULE_ALIGNED(addr) || !tr_tracking_size_valid(tracking_size)) {
		return RMI_ERROR_INPUT;
	}

	tr = tracking_region_find(addr, TR_MEM_TYPE_CONV);
	if (tr == NULL) {
		return RMI_ERROR_INPUT;
	}

	return tr_encode_lookup_result(
			tr_select_granule(tr, addr, tracking_size, g), addr);
}

/*
 * Look up a dev_granule for @addr at @tracking_size.
 *
 * No tracking-region or dev_granule lock is acquired. RMI_SUCCESS only reports
 * a selection; it does not keep the struct dev_granule or its backing alive. A caller
 * that accesses the result must prevent tracking transitions from before this
 * call until it finishes using the dev_granule or acquires its lock. Use a
 * region reader, existing ownership that pins the representation, or an
 * environment where transitions cannot run concurrently. For an unowned input
 * PA, use tr_find_lock_active_dev_granule() to select and lock the current
 * representation.
 *
 * Return RMI_SUCCESS with *@g set and *@type identifying device coherency.
 * On failure, leave *@g NULL and return RMI_ERROR_INPUT for an invalid address
 * or tracking size, RMI_BLOCKED for a pending tracking SRO, or encoded
 * RMI_ERROR_TRACKING containing @addr for a representation mismatch. *@type is then
 * unspecified. The dev_granule state is not validated.
 */
unsigned long tr_find_dev_granule(unsigned long addr,
				  unsigned long tracking_size,
				  struct dev_granule **g,
				  enum dev_coh_type *type)
{
	struct tracking_region *tr;

	assert((g != NULL) && (type != NULL));
	*g = NULL;

	if (!GRANULE_ALIGNED(addr) || !tr_tracking_size_valid(tracking_size)) {
		return RMI_ERROR_INPUT;
	}

	tr = tracking_region_find(addr, TR_MEM_TYPE_DEV);
	if (tr == NULL) {
		return RMI_ERROR_INPUT;
	}

	return tr_encode_lookup_result(
			tr_select_dev_granule(tr, addr, tracking_size, g, type),
			addr);
}

/*
 * Select and lock a granule under @tr's read lock.
 * Earlier granule locks must precede @expected_state and @addr in the
 * locking order. Return RMI_SUCCESS with *@g locked, a selection error, or
 * RMI_ERROR_INPUT without retaining *@g's lock on a state mismatch.
 */
static unsigned long tr_find_lock_granule_read_locked(
					struct tracking_region *tr,
					unsigned long addr,
					unsigned long tracking_size,
					unsigned char expected_state,
					struct granule **g)
{
	unsigned long ret;

	ret = tr_select_granule(tr, addr, tracking_size, g);
	if (ret != RMI_SUCCESS) {
		return ret;
	}

	if (!granule_lock_on_state_match(*g, expected_state)) {
		*g = NULL;
		return RMI_ERROR_INPUT;
	}

	return RMI_SUCCESS;
}

/*
 * Find and lock a granule for @addr in @expected_state. @tracking_size selects
 * the coarse or fine representation.
 *
 * Keep the region read lock from granule selection through lock acquisition.
 * A tracking transition therefore cannot replace the selected representation
 * before the granule lock makes it stable.
 */
unsigned long tr_find_lock_granule(unsigned long addr,
				   unsigned long tracking_size,
				   unsigned char expected_state,
				   struct granule **g)
{
	struct tracking_region *tr;
	unsigned long ret;

	assert(g != NULL);
	*g = NULL;

	if (!GRANULE_ALIGNED(addr) || !tr_tracking_size_valid(tracking_size)) {
		return RMI_ERROR_INPUT;
	}

	tr = tracking_region_find(addr, TR_MEM_TYPE_CONV);
	if (tr == NULL) {
		return RMI_ERROR_INPUT;
	}

	tracking_region_read_lock(tr);
	ret = tr_find_lock_granule_read_locked(tr, addr, tracking_size,
					      expected_state, g);
	tracking_region_read_unlock(tr);
	return tr_encode_lookup_result(ret, addr);
}

/*
 * Find the granule currently representing @addr, lock it in @expected_state,
 * and report the size of the physical range it represents in *@tracking_size.
 *
 * Hold the region read lock from size discovery through granule locking so
 * the returned granule and size describe the same tracking representation.
 * Release the read lock before returning, including on failure.
 *
 * On RMI_SUCCESS, *@g is locked in @expected_state and *@tracking_size reports
 * GRANULE_SIZE for fine tracking or the configured region size for coarse
 * tracking. On failure, leave *@g NULL and *@tracking_size unspecified. See
 * granule.h for input and range contracts. Errors are unencoded: RMI_BLOCKED for
 * a pending transition, RMI_ERROR_TRACKING for no representation, or
 * RMI_ERROR_INPUT for an invalid address/state.
 */
static unsigned long tr_lock_active_granule(unsigned long addr,
					  unsigned char expected_state,
					  struct granule **g,
					  unsigned long *tracking_size)
{
	struct tracking_region *tr;
	unsigned long ret;

	assert((g != NULL) && (tracking_size != NULL));
	*g = NULL;

	if (!GRANULE_ALIGNED(addr)) {
		return RMI_ERROR_INPUT;
	}

	tr = tracking_region_find(addr, TR_MEM_TYPE_CONV);
	if (tr == NULL) {
		return RMI_ERROR_INPUT;
	}

	tracking_region_read_lock(tr);
	ret = tr_active_tracking_size(tr, tracking_size);
	if (ret == RMI_SUCCESS) {
		ret = tr_find_lock_granule_read_locked(tr, addr,
						      *tracking_size,
						      expected_state, g);
	}
	tracking_region_read_unlock(tr);

	return ret;
}

/*
 * Lock an active granule and encode lookup failures for RMI and SRO callers.
 * On success, return only the granule lock with no region reader held.
 * SRO callers must yield and retry on RMI_BLOCKED. See granule.h for input,
 * output and locking contracts.
 */
unsigned long tr_find_lock_active_granule(unsigned long addr,
					unsigned char expected_state,
					struct granule **g,
					unsigned long *tracking_size)
{
	return tr_encode_lookup_result(
			tr_lock_active_granule(addr, expected_state, g, tracking_size), addr);
}

/*
 * Lock the longest run of fine granules in @expected_state.
 *
 * Retain the tracking-region read lock while collecting the run so a tracking
 * transition cannot replace the fine representation between granule lock
 * acquisitions. Check each granule's state before acquiring it so the run
 * cannot violate the global state lock order when a state boundary is reached.
 * A state, bank, or region boundary terminates a non-empty run successfully;
 * the caller can process that prefix and discover the boundary state in its
 * next range invocation.
 */
/* cppcheck-suppress misra-c2012-8.7 */
unsigned long tr_find_lock_fine_granule_run(unsigned long addr,
					     unsigned long end_addr,
					     unsigned char expected_state,
					     unsigned long *count)
{
	struct tracking_region *tr;
	unsigned long tracking_size;
	unsigned long cursor;
	unsigned long locked = 0UL;
	unsigned long ret;

	assert(count != NULL);
	*count = 0UL;
	if (!GRANULE_ALIGNED(addr) || !GRANULE_ALIGNED(end_addr) ||
	    (end_addr <= addr)) {
		return RMI_ERROR_INPUT;
	}

	tr = tracking_region_find(addr, TR_MEM_TYPE_CONV);
	if (tr == NULL) {
		return RMI_ERROR_INPUT;
	}

	tracking_region_read_lock(tr);
	ret = tr_active_tracking_size(tr, &tracking_size);
	if (ret != RMI_SUCCESS) {
		goto out;
	}
	if (tracking_size != GRANULE_SIZE) {
		ret = RMI_ERROR_TRACKING;
		goto out;
	}

	for (cursor = addr; cursor < end_addr; cursor += GRANULE_SIZE) {
		struct granule *g;

		if (tracking_region_find(cursor, TR_MEM_TYPE_CONV) != tr) {
			assert(ret == RMI_SUCCESS);
			break;
		}

		ret = tr_select_granule(tr, cursor, GRANULE_SIZE, &g);
		if ((ret == RMI_SUCCESS) &&
		    !granule_lock_on_state_match(g, expected_state)) {
			ret = RMI_ERROR_INPUT;
		}
		if (ret != RMI_SUCCESS) {
			/*
			 * Return any locked prefix as a successful run so the caller
			 * can process it before handling the failing address on its
			 * next lookup. If nothing was locked, preserve the error.
			 */
			if (locked != 0UL) {
				ret = RMI_SUCCESS;
			}
			break;
		}
		locked++;
	}

out:
	tracking_region_read_unlock(tr);
	if (ret != RMI_SUCCESS) {
		/* A non-empty locked prefix is always returned as a success. */
		assert(locked == 0UL);
		return tr_encode_lookup_result(ret, addr);
	}

	assert(locked != 0UL);
	*count = locked;
	return RMI_SUCCESS;
}

/*
 * Select and lock a dev_granule under @tr's read lock.
 * Earlier granule locks must precede @expected_state and @addr in the
 * locking order. Return RMI_SUCCESS with *@g locked, a selection error, or
 * RMI_ERROR_INPUT without retaining *@g's lock on a state mismatch.
 */
static unsigned long tr_find_lock_dev_granule_read_locked(
					struct tracking_region *tr,
					unsigned long addr,
					unsigned long tracking_size,
					unsigned char expected_state,
					struct dev_granule **g,
					enum dev_coh_type *type)
{
	unsigned long ret;

	ret = tr_select_dev_granule(tr, addr, tracking_size, g, type);
	if (ret != RMI_SUCCESS) {
		return ret;
	}

	if (!dev_granule_lock_on_state_match(*g, expected_state)) {
		*g = NULL;
		return RMI_ERROR_INPUT;
	}

	return RMI_SUCCESS;
}

/*
 * Find the dev_granule currently representing @addr, lock it in @expected_state,
 * and report the size of the physical range it represents in *@tracking_size.
 *
 * Hold the region read lock from size discovery through dev_granule locking so
 * the returned dev_granule and size describe the same tracking representation.
 * Release the read lock before returning, including on failure.
 *
 * On RMI_SUCCESS, *@g is locked in @expected_state, *@type reports its coherency
 * type and *@tracking_size reports GRANULE_SIZE for fine tracking or the
 * configured region size for coarse tracking. On failure, leave *@g NULL;
 * *@type and *@tracking_size are unspecified. See dev_granule.h for input,
 * range-validation contracts. Errors are unencoded: RMI_BLOCKED for a pending
 * transition, RMI_ERROR_TRACKING for no representation, or RMI_ERROR_INPUT for
 * an invalid address/state.
 */
static unsigned long tr_lock_active_dev_granule(
					unsigned long addr,
					unsigned char expected_state,
					struct dev_granule **g,
					enum dev_coh_type *type,
					unsigned long *tracking_size)
{
	struct tracking_region *tr;
	unsigned long ret;

	assert((g != NULL) && (type != NULL) && (tracking_size != NULL));
	*g = NULL;

	if (!GRANULE_ALIGNED(addr)) {
		return RMI_ERROR_INPUT;
	}

	tr = tracking_region_find(addr, TR_MEM_TYPE_DEV);
	if (tr == NULL) {
		return RMI_ERROR_INPUT;
	}

	tracking_region_read_lock(tr);
	ret = tr_active_tracking_size(tr, tracking_size);
	if (ret == RMI_SUCCESS) {
		ret = tr_find_lock_dev_granule_read_locked(tr, addr,
							  *tracking_size,
							  expected_state,
							  g, type);
	}
	tracking_region_read_unlock(tr);

	return ret;
}

/*
 * Lock an active dev_granule and encode lookup failures for RMI and SRO callers.
 * On success, return only the dev_granule lock with no region reader held.
 * SRO callers must yield and retry on RMI_BLOCKED. See dev_granule.h for input,
 * output and locking contracts.
 */
unsigned long tr_find_lock_active_dev_granule(unsigned long addr,
					unsigned char expected_state,
					struct dev_granule **g,
					enum dev_coh_type *type,
					unsigned long *tracking_size)
{
	return tr_encode_lookup_result(
		tr_lock_active_dev_granule(addr, expected_state, g, type, tracking_size), addr);
}

/*
 * Lock the longest run of fine dev_granules in @expected_state.
 *
 * The tracking-region read lock stabilizes the fine representation while the
 * granules are acquired in ascending PA order. Check each granule's
 * state before acquisition and after contention so a state boundary cannot
 * introduce a lock-order violation. Stop before a different bank, region,
 * coherency type, or Granule state so the caller can pass a homogeneous
 * NS-only range to EL3.
 */
/* cppcheck-suppress misra-c2012-8.7 */
unsigned long tr_find_lock_fine_dev_granule_run(
					unsigned long addr,
					unsigned long end_addr,
					unsigned char expected_state,
					enum dev_coh_type *type,
					unsigned long *count)
{
	struct tracking_region *tr;
	unsigned long tracking_size;
	unsigned long cursor;
	unsigned long locked = 0UL;
	unsigned long ret;

	assert((type != NULL) && (count != NULL));
	*count = 0UL;
	if (!GRANULE_ALIGNED(addr) || !GRANULE_ALIGNED(end_addr) ||
	    (end_addr <= addr)) {
		return RMI_ERROR_INPUT;
	}

	tr = tracking_region_find(addr, TR_MEM_TYPE_DEV);
	if (tr == NULL) {
		return RMI_ERROR_INPUT;
	}

	tracking_region_read_lock(tr);
	ret = tr_active_tracking_size(tr, &tracking_size);
	if (ret != RMI_SUCCESS) {
		goto out;
	}
	if (tracking_size != GRANULE_SIZE) {
		ret = RMI_ERROR_TRACKING;
		goto out;
	}

	for (cursor = addr; cursor < end_addr; cursor += GRANULE_SIZE) {
		enum dev_coh_type current_type;
		struct dev_granule *g;

		if (tracking_region_find(cursor, TR_MEM_TYPE_DEV) != tr) {
			break;
		}

		ret = tr_select_dev_granule(tr, cursor, GRANULE_SIZE, &g,
					    &current_type);
		if ((ret == RMI_SUCCESS) &&
		    !dev_granule_lock_on_state_match(g, expected_state)) {
			ret = RMI_ERROR_INPUT;
		}
		if (ret != RMI_SUCCESS) {
			if (locked != 0UL) {
				ret = RMI_SUCCESS;
			}
			break;
		}
		if ((locked != 0UL) && (current_type != *type)) {
			dev_granule_unlock(g);
			ret = RMI_SUCCESS;
			break;
		}
		if (locked == 0UL) {
			*type = current_type;
		}
		locked++;
	}

out:
	tracking_region_read_unlock(tr);
	if (ret != RMI_SUCCESS) {
		/* A non-empty locked prefix is always returned as a success. */
		assert(locked == 0UL);
		return tr_encode_lookup_result(ret, addr);
	}

	assert(locked != 0UL);
	*count = locked;
	return RMI_SUCCESS;
}

struct tr_granule_set {
	unsigned long addr;
	struct granule *g;
	struct granule **g_ret;
	unsigned char state;
};

/* Return the global lock order for @state. */
static unsigned int tr_granule_lock_order(unsigned char state)
{
	switch (state) {
	case GRANULE_STATE_RD:
		return 0U;
	case GRANULE_STATE_REC:
		return 1U;
	case GRANULE_STATE_PDEV:
		return 2U;
	case GRANULE_STATE_VDEV:
		return 3U;
	case GRANULE_STATE_RTT:
		return 4U;
	case GRANULE_STATE_DELEGATED:
		return 5U;
	case GRANULE_STATE_NS:
		return 6U;
	case GRANULE_STATE_DATA:
		return 7U;
	case GRANULE_STATE_REC_AUX:
		return 8U;
	case GRANULE_STATE_PDEV_AUX:
		return 9U;
	case GRANULE_STATE_VDEV_AUX:
		return 10U;
	case GRANULE_STATE_INTERNAL:
		return 11U;
	case GRANULE_STATE_PSMMU_ST_L2:
		return 12U;
	case GRANULE_STATE_RD_AUX:
		return 13U;
	case GRANULE_STATE_PARTIAL:
		return 14U;
	default:
		assert(false);
		return ~0U;
	}
}

/* Return whether @a must be locked after @b. */
static bool tr_granule_set_after(const struct tr_granule_set *a,
				 const struct tr_granule_set *b)
{
	unsigned int order_a = tr_granule_lock_order(a->state);
	unsigned int order_b = tr_granule_lock_order(b->state);

	if (order_a != order_b) {
		return order_a > order_b;
	}

	return a->addr > b->addr;
}

/* Return whether @gs contains the same address more than once. */
static bool tr_granule_set_has_duplicate_addr(
					const struct tr_granule_set *gs,
					unsigned long n)
{
	for (unsigned long i = 0UL; i < n; i++) {
		for (unsigned long j = i + 1UL; j < n; j++) {
			if (gs[i].addr == gs[j].addr) {
				return true;
			}
		}
	}

	return false;
}

/* Sort granules into global lock order. */
static void tr_sort_granules(struct tr_granule_set *gs, unsigned long n)
{
	for (unsigned long i = 1UL; i < n; i++) {
		struct tr_granule_set temp = gs[i];
		unsigned long j = i;

		while ((j > 0UL) &&
		       tr_granule_set_after(&gs[j - 1UL], &temp)) {
			gs[j] = gs[j - 1UL];
			j--;
		}
		if (i != j) {
			gs[j] = temp;
		}
	}
}

/*
 * Lock @n independently addressed fine granules in state and PA order,
 * rejecting duplicate addresses. Each lookup acquires its own region reader
 * while earlier granule locks pin their representations. Publish output
 * pointers and return RMI_SUCCESS only after all locks succeed; otherwise
 * release the prefix and return the first failing lookup's tracking-aware
 * RMI error. Callers must initialize the output pointers to NULL and obey the
 * locking contract in granule.h.
 */
static unsigned long tr_find_lock_fine_granules(struct tr_granule_set *gs,
					      unsigned long n)
{
	unsigned long ret;
	unsigned long i;

	assert((gs != NULL) && (n > 0UL) && (n <= TR_GRANULE_SET_MAX));

	if (tr_granule_set_has_duplicate_addr(gs, n)) {
		return RMI_ERROR_INPUT;
	}

	/* Keep address validation ahead of granule acquisition. */
	for (i = 0UL; i < n; i++) {
		if (!GRANULE_ALIGNED(gs[i].addr) ||
		    (tracking_region_find(gs[i].addr, TR_MEM_TYPE_CONV) == NULL)) {
			return RMI_ERROR_INPUT;
		}
	}

	tr_sort_granules(gs, n);
	/* Each acquired granule pins its representation during later lookups. */
	for (i = 0UL; i < n; i++) {
		ret = tr_find_lock_granule(gs[i].addr, GRANULE_SIZE,
					    gs[i].state, &gs[i].g);
		if (ret != RMI_SUCCESS) {
			goto out_err;
		}
	}

	for (i = 0UL; i < n; i++) {
		*gs[i].g_ret = gs[i].g;
	}

	return RMI_SUCCESS;

out_err:
	while (i != 0UL) {
		granule_unlock(gs[--i].g);
	}

	return ret;
}

/*
 * Find and lock two fine granules in global state and PA order.
 * See granule.h for the address, state and locking contracts.
 * Return an RMI result, leaving both outputs NULL and no locks held on failure.
 */
/* cppcheck-suppress misra-c2012-8.7 */
unsigned long tr_find_lock_two_fine_granules(
			unsigned long addr1,
			unsigned char expected_state1,
			struct granule **g1,
			unsigned long addr2,
			unsigned char expected_state2,
			struct granule **g2)
{
	struct tr_granule_set gs[] = {
		{
			.addr = addr1,
			.g_ret = g1,
			.state = expected_state1
		},
		{
			.addr = addr2,
			.g_ret = g2,
			.state = expected_state2
		}
	};

	assert((g1 != NULL) && (g2 != NULL));
	*g1 = NULL;
	*g2 = NULL;

	/* All helper accesses are bounded by the exact element count passed here. */
	/* coverity[overrun-buffer-val:SUPPRESS] */
	return tr_find_lock_fine_granules(gs, ARRAY_SIZE(gs));
}

/*
 * Find and lock three fine granules in global state and PA order.
 * See granule.h for the address, state and locking contracts.
 * Return an RMI result, leaving all outputs NULL and no locks held on failure.
 */
/* cppcheck-suppress misra-c2012-8.7 */
unsigned long tr_find_lock_three_fine_granules(
			unsigned long addr1,
			unsigned char expected_state1,
			struct granule **g1,
			unsigned long addr2,
			unsigned char expected_state2,
			struct granule **g2,
			unsigned long addr3,
			unsigned char expected_state3,
			struct granule **g3)
{
	struct tr_granule_set gs[] = {
		{
			.addr = addr1,
			.g_ret = g1,
			.state = expected_state1
		},
		{
			.addr = addr2,
			.g_ret = g2,
			.state = expected_state2
		},
		{
			.addr = addr3,
			.g_ret = g3,
			.state = expected_state3
		}
	};

	assert((g1 != NULL) && (g2 != NULL) && (g3 != NULL));
	*g1 = NULL;
	*g2 = NULL;
	*g3 = NULL;

	return tr_find_lock_fine_granules(gs, ARRAY_SIZE(gs));
}

/*
 * Return the unlocked fine granule for @addr, or NULL on lookup failure. The
 * caller must provide the lifetime protection described by tr_find_granule();
 * a non-NULL result does not make later access safe.
 */
/* cppcheck-suppress misra-c2012-8.7 */
struct granule *tr_find_fine_granule(unsigned long addr)
{
	struct granule *g;

	if (tr_find_granule(addr, GRANULE_SIZE, &g) != RMI_SUCCESS) {
		return NULL;
	}

	return g;
}

/*
 * Return the unlocked fine dev_granule for @addr and its coherency type
 * through @type, or NULL on lookup failure. The caller must provide the lifetime
 * protection described by tr_find_dev_granule(); a non-NULL result does not make
 * later access safe. *@type is unspecified on failure.
 */
/* cppcheck-suppress misra-c2012-8.7 */
struct dev_granule *tr_find_fine_dev_granule(unsigned long addr,
					      enum dev_coh_type *type)
{
	struct dev_granule *g;

	if (tr_find_dev_granule(addr, GRANULE_SIZE, &g, type) != RMI_SUCCESS) {
		return NULL;
	}

	return g;
}

/*
 * Lock a granule for a range in either @source_state or @target_state.
 * The states must differ and all output pointers must be non-NULL.
 * The caller must hold no Granule lock. On RMI_SUCCESS, @g is locked,
 * @tracking_size identifies the active representation, and @in_target reports
 * whether the granule is in @target_state. Return the tracking-aware lookup
 * error with no lock held on failure; the outputs are then unspecified.
 */
/* cppcheck-suppress misra-c2012-8.7 */
unsigned long granule_range_lock_conventional(
					unsigned long addr,
					unsigned char source_state,
					unsigned char target_state,
					struct granule **g,
					unsigned long *tracking_size,
					bool *in_target)
{
	unsigned long ret;

	ret = tr_find_lock_active_granule(addr, source_state, g,
					  tracking_size);
	if (ret == RMI_SUCCESS) {
		*in_target = false;
		return ret;
	}
	if (ret != RMI_ERROR_INPUT) {
		return ret;
	}

	ret = tr_find_lock_active_granule(addr, target_state, g,
					  tracking_size);
	if (ret == RMI_SUCCESS) {
		*in_target = true;
	}
	return ret;
}

/*
 * Lock a dev_granule for a range in either @source_state or @target_state.
 * The states must differ and all output pointers must be non-NULL.
 * On RMI_SUCCESS, @g is locked, @tracking_size identifies the active
 * representation, and @in_target reports whether it is in @target_state. The
 * caller must hold no Granule lock. Return the tracking-aware lookup error with
 * no lock held on failure; the outputs are then unspecified. Lookup validates
 * the device coherency type, which is not otherwise needed by this operation.
 */
/* cppcheck-suppress misra-c2012-8.7 */
unsigned long granule_range_lock_device(unsigned long addr,
					unsigned char source_state,
					unsigned char target_state,
					struct dev_granule **g,
					unsigned long *tracking_size,
					bool *in_target)
{
	enum dev_coh_type type __unused;
	unsigned long ret;

	ret = tr_find_lock_active_dev_granule(addr, source_state, g, &type,
					      tracking_size);
	if (ret == RMI_SUCCESS) {
		*in_target = false;
		return ret;
	}
	if (ret != RMI_ERROR_INPUT) {
		return ret;
	}

	ret = tr_find_lock_active_dev_granule(addr, target_state, g, &type,
					      tracking_size);
	if (ret == RMI_SUCCESS) {
		*in_target = true;
	}
	return ret;
}

/*
 * Publish delegation progress for a locked run of fine granules.
 * The caller owns @locked_count consecutive NS granules starting at aligned
 * @addr, with @delegated_count <= @locked_count. Change the delegated prefix to
 * DELEGATED. Change the remaining granules to PARTIAL if @incomplete, or
 * leave them NS otherwise. Release every granule lock in ascending PA order
 * without acquiring a region reader. The caller must retain ownership of any
 * PARTIAL granules until their PAS transition completes or rolls back.
 */
/* cppcheck-suppress misra-c2012-8.7 */
void granule_range_delegate_fine_unlock(unsigned long addr,
						unsigned long locked_count,
						unsigned long delegated_count,
						bool incomplete)
{
	assert(delegated_count <= locked_count);

	for (unsigned long i = 0UL; i < locked_count; i++) {
		struct granule *g =
			tr_addr_to_granule(addr + (i * GRANULE_SIZE));

		if (i < delegated_count) {
			granule_unlock_transition(g, GRANULE_STATE_DELEGATED);
		} else if (incomplete) {
			granule_unlock_transition(g, GRANULE_STATE_PARTIAL);
		} else {
			granule_unlock(g);
		}
	}
}

/*
 * Publish delegation progress for a locked run of fine dev_granules.
 * The caller owns @locked_count consecutive NS dev_granules starting at aligned
 * @addr, with @delegated_count <= @locked_count. Change the delegated prefix to
 * DELEGATED. Change the remaining dev_granules to PARTIAL if @incomplete, or
 * leave them NS otherwise. Release every dev_granule lock in ascending PA order
 * without acquiring a region reader. The caller must retain ownership of any
 * PARTIAL dev_granules until their PAS transition completes or rolls back.
 */
/* cppcheck-suppress misra-c2012-8.7 */
void granule_range_delegate_fine_dev_unlock(unsigned long addr,
					    unsigned long locked_count,
					    unsigned long delegated_count,
					    bool incomplete)
{
	assert(delegated_count <= locked_count);

	for (unsigned long i = 0UL; i < locked_count; i++) {
		enum dev_coh_type type;
		struct dev_granule *g = tr_addr_to_dev_granule(
					addr + (i * GRANULE_SIZE), &type);

		(void)type;
		if (i < delegated_count) {
			dev_granule_unlock_transition(
					g, DEV_GRANULE_STATE_DELEGATED);
		} else if (incomplete) {
			dev_granule_unlock_transition(
					g, DEV_GRANULE_STATE_PARTIAL);
		} else {
			dev_granule_unlock(g);
		}
	}
}

/*
 * Publish [@addr, @addr + @size) from PARTIAL as DELEGATED or NS.
 * Both arguments must be Granule aligned. @device selects dev_granules when
 * true, or granules otherwise. @delegated selects DELEGATED rather than NS.
 * The caller must own every PARTIAL granule in the range, pinning fine
 * tracking even while a representation transition is pending, and hold no
 * Granule lock. Acquire and release each granule in ascending PA order
 * without entering a region reader gate.
 */
/* cppcheck-suppress misra-c2012-8.7 */
void granule_delegate_fine_transition(unsigned long addr,
				      unsigned long size,
				      bool device, bool delegated)
{
	assert(GRANULE_ALIGNED(addr) && GRANULE_ALIGNED(size));
	for (unsigned long offset = 0UL; offset < size;
	     offset += GRANULE_SIZE) {
		if (device) {
			struct dev_granule *g;

			g = tr_lock_owned_dev_granule(addr + offset, GRANULE_SIZE,
						      DEV_GRANULE_STATE_PARTIAL);
			dev_granule_unlock_transition(g, delegated ?
				DEV_GRANULE_STATE_DELEGATED : DEV_GRANULE_STATE_NS);
		} else {
			struct granule *g;

			g = tr_lock_owned_granule(addr + offset, GRANULE_SIZE,
						  GRANULE_STATE_PARTIAL);
			granule_unlock_transition(g, delegated ?
				GRANULE_STATE_DELEGATED : GRANULE_STATE_NS);
		}
	}
}

/*
 * Publish a coarse granule or dev_granule from PARTIAL as DELEGATED or NS.
 * @addr must be aligned to the configured region size, supplied as
 * @tracking_size. @device selects dev_granules when true, or granules
 * otherwise; @delegated selects DELEGATED rather than NS. The caller must own
 * the PARTIAL granule, pinning its coarse representation, and hold no
 * Granule lock. Acquire its lock without entering a region reader gate and
 * release it after publishing the state.
 */
/* cppcheck-suppress misra-c2012-8.7 */
void granule_delegate_coarse_transition(unsigned long addr,
					unsigned long tracking_size,
					bool device, bool delegated)
{
	assert(tracking_size == tracking_region_get_size());
	if (device) {
		struct dev_granule *g;

		g = tr_lock_owned_dev_granule(addr, tracking_size,
					      DEV_GRANULE_STATE_PARTIAL);
		dev_granule_unlock_transition(g, delegated ?
				DEV_GRANULE_STATE_DELEGATED : DEV_GRANULE_STATE_NS);
	} else {
		struct granule *g;

		g = tr_lock_owned_granule(addr, tracking_size,
					  GRANULE_STATE_PARTIAL);
		granule_unlock_transition(g, delegated ?
				GRANULE_STATE_DELEGATED : GRANULE_STATE_NS);
	}
}
