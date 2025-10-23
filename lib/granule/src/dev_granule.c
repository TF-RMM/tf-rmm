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
static struct dev_granule *dev_ncoh_granules;
static unsigned long max_dev_ncoh_granules;

/* cppcheck-suppress misra-c2012-8.7 */
int dev_granule_init(uintptr_t alloc, size_t alloc_size,
	unsigned long max_ncoh_granules)
{
	assert(alloc != 0ULL);
	/* cppcheck-suppress moduloofone */
	assert(ALIGNED(alloc, sizeof(struct dev_granule)));

	dev_ncoh_granules = (struct dev_granule *)alloc;

	assert(alloc_size != 0U);

	if (max_ncoh_granules > (alloc_size / sizeof(struct dev_granule))) {
		ERROR("Max dev granules mismatch\n");
		return -1;
	}

	max_dev_ncoh_granules = max_ncoh_granules;
	return 0;
}

/*
 * Takes a valid pointer to a struct dev_granule, corresponding to device memory
 * coherency type and returns the dev_granule physical address.
 *
 * This is purely a lookup, and provides no guarantees about the attributes of
 * the dev_granule (i.e. whether it is locked, its state or its reference count).
 */
/* cppcheck-suppress misra-c2012-8.7 */
unsigned long dev_granule_addr(const struct dev_granule *g, enum dev_coh_type type)
{
	unsigned long idx;

	assert(g != NULL);
	assert(dev_ncoh_granules != NULL);

	/* No coherent device granules */
	assert(type == DEV_MEM_NON_COHERENT);

	idx = ((unsigned long)g - (unsigned long)dev_ncoh_granules) /
						sizeof(struct dev_granule);
	assert(idx < max_dev_ncoh_granules);
	return plat_dev_granule_idx_to_addr(idx, type);
}

/*
 * Takes a dev_granule index, corresponding to dev_type
 * and returns a pointer to the struct dev_granule.
 *
 * This is purely a lookup, and provides no guarantees about the attributes of
 * the granule (i.e. whether it is locked, its state or its reference count).
 */
static struct dev_granule *dev_granule_from_idx(unsigned long idx, enum dev_coh_type type)
{
	(void)type;
	assert(dev_ncoh_granules != NULL);

	/* No coherent device granules */
	assert((type == DEV_MEM_NON_COHERENT) && (idx < max_dev_ncoh_granules));

	return &dev_ncoh_granules[idx];
}

/*
 * Takes an aligned dev_granule address, returns a pointer to the corresponding
 * struct dev_granule and sets device granule coherency type in address passed
 * in @type.
 *
 * This is purely a lookup, and provides no guarantees about the attributes of
 * the granule (i.e. whether it is locked, its state or its reference count).
 */
/* cppcheck-suppress misra-c2012-8.7 */
struct dev_granule *addr_to_dev_granule(unsigned long addr, enum dev_coh_type *type)
{
	unsigned long idx;

	assert(GRANULE_ALIGNED(addr));

	idx = plat_dev_granule_addr_to_idx(addr, type);
	return dev_granule_from_idx(idx, *type);
}

/*
 * Verifies whether @addr is a valid dev_granule physical address, returns
 * a pointer to the corresponding struct dev_granule and sets device granule
 * coherency type.
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
struct dev_granule *find_dev_granule(unsigned long addr, enum dev_coh_type *type)
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
 * set device granule coherency type.
 *
 * Returns:
 *	A valid dev_granule pointer if @addr is a valid dev_granule physical address
 *	and device granule type in address passed in @type.
 *	NULL if any of:
 *	- @addr is not aligned to the size of a granule.
 *	- @addr is out of range.
 *	- if the state of the dev_granule at @addr is not @expected_state.
 *	The system coherent memory space associated with dev_granule is returned in
 *	@type output parameter.
 */
struct dev_granule *find_lock_dev_granule(unsigned long addr,
					  unsigned char expected_state,
					  enum dev_coh_type *type)
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

/*
 * Obtain a pointer to an array of @n locked dev_granules at @addr if @addr is a
 * valid dev_granule physical address and the states of all @n dev_granules in
 * array at @addr are @expected_state.
 *
 * Returns:
 *	A valid pointer to the 1st dev_granule in array if @addr is a valid
 *	dev_granule physical address.
 *	NULL if any of:
 *	- @addr is not aligned to the size of a granule.
 *	- @addr is out of range.
 *	- if the states of all dev_granules in array at @addr are not @expected_state.
 *	- if not all @n dev_granules in array have the same coherency type.
 *	The coherency type associated with dev_granules is returned in
 *	@type output parameter.
 *
 * Locking only succeeds if all @n the dev_granules are in their expected states and
 * have the same coherency memory type.
 * If the function fails, no lock is held.
 */
/* cppcheck-suppress misra-c2012-8.7 */
struct dev_granule *find_lock_dev_granules(unsigned long addr,
					   unsigned char expected_state,
					   unsigned long n,
					   enum dev_coh_type *type)
{
	struct dev_granule *g;

	/*
	 * Find and lock the 1st dev_granule in array.
	 * Get its coherency type.
	 */
	g = find_lock_dev_granule(addr, expected_state, type);
	if (g == NULL) {
		return NULL;
	}

	for (unsigned long i = 1UL; i < n; i++) {
		enum dev_coh_type g_type;
		struct dev_granule *g_dev;

		addr += GRANULE_SIZE;

		g_dev = find_lock_dev_granule(addr, expected_state, &g_type);
		if ((g_dev == NULL) || (g_type != *type)) {
			while (i != 0UL) {
				dev_granule_unlock(&g[--i]);
			}
			return NULL;
		}
	}

	return g;
}
