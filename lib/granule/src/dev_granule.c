/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <assert.h>
#include <debug.h>
#include <dev_granule.h>
#include <platform_api.h>
#include <stddef.h>
#include <utils_def.h>

/* Non-coherent device granules */
IF_NCBMC(static) struct dev_granule dev_ncoh_granules[RMM_MAX_NCOH_GRANULES]
			IF_NCBMC(__section("granules_memory"));

/*
 * Takes a valid pointer to a struct dev_granule, corresponding to dev_type
 * and returns the dev_granule physical address.
 *
 * This is purely a lookup, and provides no guarantees about the attributes of
 * the dev_granule (i.e. whether it is locked, its state or its reference count).
 */
unsigned long dev_granule_addr(const struct dev_granule *g, enum dev_type type)
{
	(void)type;
	unsigned long idx;

	assert(g != NULL);

	/* No coherent device granules */
	assert(type == DEV_RANGE_NON_COHERENT);

	idx = ((unsigned long)g - (unsigned long)dev_ncoh_granules) /
						sizeof(struct dev_granule);
	return plat_dev_granule_idx_to_addr(idx, type);
}

/*
 * Takes a dev_granule index, corresponding to dev_type
 * and returns a pointer to the struct dev_granule.
 *
 * This is purely a lookup, and provides no guarantees about the attributes of
 * the granule (i.e. whether it is locked, its state or its reference count).
 */
static struct dev_granule *dev_granule_from_idx(unsigned long idx, enum dev_type type)
{
	(void)type;

	/* No coherent device granules */
	assert((type == DEV_RANGE_NON_COHERENT) && (idx < RMM_MAX_NCOH_GRANULES));

	return &dev_ncoh_granules[idx];
}

/*
 * Takes an aligned dev_granule address, returns a pointer to the corresponding
 * struct dev_granule and sets device granule type in address passed in @type.
 *
 * This is purely a lookup, and provides no guarantees about the attributes of
 * the granule (i.e. whether it is locked, its state or its reference count).
 */
struct dev_granule *addr_to_dev_granule(unsigned long addr, enum dev_type *type)
{
	unsigned long idx;

	assert(GRANULE_ALIGNED(addr));

	idx = plat_dev_granule_addr_to_idx(addr, type);
	return dev_granule_from_idx(idx, *type);
}

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
struct dev_granule *find_dev_granule(unsigned long addr, enum dev_type *type)
{
	unsigned long idx;

	if (!GRANULE_ALIGNED(addr)) {
		return NULL;
	}

	idx = plat_dev_granule_addr_to_idx(addr, type);

	if (idx == UINT64_MAX) {
		return NULL;
	}

	return dev_granule_from_idx(idx, *type);
}

/*
 * Obtain a pointer to a locked dev_granule at @addr if @addr is a valid dev_granule
 * physical address and the state of the dev_granule at @addr is @expected_state and
 * set device granule type.
 *
 * Returns:
 *	A valid dev-granule pointer if @addr is a valid dev_granule physical address
 *	and device granule type in address passed in @type.
 *	NULL if any of:
 *	- @addr is not aligned to the size of a granule.
 *	- @addr is out of range.
 *	- if the state of the dev_granule at @addr is not @expected_state.
 */
struct dev_granule *find_lock_dev_granule(unsigned long addr,
					  unsigned char expected_state,
					  enum dev_type *type)
{
	struct dev_granule *g = find_dev_granule(addr, type);

	if (g == NULL) {
		return NULL;
	}

	if (!dev_granule_lock_on_state_match(g, expected_state)) {
		return NULL;
	}

	return g;
}
