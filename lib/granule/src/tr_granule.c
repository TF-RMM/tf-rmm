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
 * environment where transitions cannot run concurrently.
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
