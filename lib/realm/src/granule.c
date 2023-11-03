/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <assert.h>
#include <buffer.h>
#include <debug.h>
#include <granule.h>
#include <mmio.h>
#include <platform_api.h>
#include <smc.h>
#include <status.h>
#include <stddef.h>
/* According to the C standard, the memset function used in this file is declared in string.h */
/* coverity[unnecessary_header: SUPPRESS] */
#include <string.h>
#include <utils_def.h>

IF_NCBMC(static) struct granule granules[RMM_MAX_GRANULES];

/*
 * Takes a valid pointer to a struct granule, and returns the granule physical
 * address.
 *
 * This is purely a lookup, and provides no guarantees about the attributes of
 * the granule (i.e. whether it is locked, its state or its reference count).
 */
unsigned long granule_addr(const struct granule *g)
{
	unsigned long idx;

	assert(g != NULL);
	assert(ALIGNED_TO_ARRAY(g, granules));

	idx = ((unsigned long)g - (unsigned long)granules) /
						sizeof(struct granule);

	return plat_granule_idx_to_addr(idx);
}

/*
 * Takes a granule index, and returns a pointer to the struct granule.
 *
 * This is purely a lookup, and provides no guarantees about the attributes of
 * the granule (i.e. whether it is locked, its state or its reference count).
 */
static struct granule *granule_from_idx(unsigned long idx)
{
	assert(idx < RMM_MAX_GRANULES);
	return &granules[idx];
}

/*
 * Takes an aligned granule address, and returns a pointer to the corresponding
 * struct granule.
 *
 * This is purely a lookup, and provides no guarantees about the attributes of
 * the granule (i.e. whether it is locked, its state or its reference count).
 */
struct granule *addr_to_granule(unsigned long addr)
{
	unsigned long idx;

	assert(GRANULE_ALIGNED(addr));

	idx = plat_granule_addr_to_idx(addr);
	return granule_from_idx(idx);
}

/*
 * Verifies whether @addr is a valid granule physical address, and returns a
 * pointer to the corresponding struct granule.
 *
 * This is purely a lookup, and provides no guarantees w.r.t the state of the
 * granule (e.g. locking).
 *
 * Returns:
 *     Pointer to the struct granule if @addr is a valid granule physical
 *     address.
 *     NULL if any of:
 *     - @addr is not aligned to the size of a granule.
 *     - @addr is out of range.
 */
struct granule *find_granule(unsigned long addr)
{
	unsigned long idx;

	if (!GRANULE_ALIGNED(addr)) {
		return NULL;
	}

	idx = plat_granule_addr_to_idx(addr);

	if (idx >= RMM_MAX_GRANULES) {
		return NULL;
	}

	return granule_from_idx(idx);
}

/*
 * Obtain a pointer to a locked granule at @addr if @addr is a valid granule
 * physical address and the state of the granule at @addr is @expected_state.
 *
 * Returns:
 *	A valid granule pointer if @addr is a valid granule physical address.
 *	NULL if any of:
 *	- @addr is not aligned to the size of a granule.
 *	- @addr is out of range.
 *	- if the state of the granule at @addr is not
 *	@expected_state.
 */
struct granule *find_lock_granule(unsigned long addr,
				  enum granule_state expected_state)
{
	struct granule *g;

	g = find_granule(addr);
	if (g == NULL) {
		return NULL;
	}

	if (!granule_lock_on_state_match(g, expected_state)) {
		return NULL;
	}

	return g;
}

struct granule_set {
	unsigned long addr;
	enum granule_state state;
	struct granule *g;
	struct granule **g_ret;
};

/*
 * Sort a set of granules by their address.
 */
static void sort_granules(struct granule_set *gs, unsigned long n)
{
	for (unsigned long i = 1UL; i < n; i++) {
		struct granule_set temp = gs[i];
		unsigned long j = i;

		while ((j > 0UL) && (gs[j - 1UL].addr > temp.addr)) {
			gs[j] = gs[j - 1UL];
			j--;
		}
		if (i != j) {
			gs[j] = temp;
		}
	}
}

/*
 * Find a set of granules and lock them in order of their address.
 *
 * @granules: Pointer to array of @n items.  Each item must be pre-populated
 *		with ->addr set to the granule's address, and ->state set to
 *		the expected state of the granule, and ->g_ret pointing to
 *		a valid 'struct granule *'.
 *		This function sorts the supplied array in place.
 * @n: Number of struct granule_set in array pointed to by @granules
 *
 * Returns:
 *     True if all granules in @granules were successfully locked.
 *
 *     False if any two entries in @granules have the same ->addr, or
 *     if, for any entry in @granules, any of the following is true:
 *       - entry->addr is not aligned to the size of a granule
 *       - entry->addr is out of range
 *       - the state of the granule at entry->addr is not entry->state
 *
 * Locking only succeeds if the granules are in their expected states as per the
 * locking rules in granule_types.h.
 *
 * If the function succeeds, for all items in @granules, ->g points to a locked
 * granule in ->state and *->g_ret is set to the pointer value.
 *
 * If the function fails, no lock is held and no *->g_ret pointers are
 * modified.
 */
static bool find_lock_granules(struct granule_set *gs, unsigned long n)
{
	unsigned long i;

	sort_granules(gs, n);

	for (i = 0UL; i < n; i++) {
		/* Check for duplicates */
		if ((i != 0UL) &&
		    (gs[i].addr == gs[i - 1UL].addr)) {
			goto out_err;
		}

		gs[i].g = find_lock_granule(gs[i].addr, gs[i].state);
		if (gs[i].g == NULL) {
			goto out_err;
		}
	}

	for (i = 0UL; i < n; i++) {
		*gs[i].g_ret = gs[i].g;
	}

	return true;

out_err:
	while (i-- != 0UL) {
		granule_unlock(gs[i].g);
	}

	return false;
}

/*
 * Find two granules and lock them in order of their address.
 *
 * See find_lock_granules().
 */
bool find_lock_two_granules(
			unsigned long addr1,
			enum granule_state expected_state1,
			struct granule **g1,
			unsigned long addr2,
			enum granule_state expected_state2,
			struct granule **g2)
{
	struct granule_set gs[] = {
		{addr1, expected_state1, NULL, g1},
		{addr2, expected_state2, NULL, g2}
	};

	assert((g1 != NULL) && (g2 != NULL));

	return find_lock_granules(gs, ARRAY_SIZE(gs));
}

void granule_memzero(struct granule *g, enum buffer_slot slot)
{
	unsigned long *buf;

	assert(g != NULL);

	buf = granule_map(g, slot);
	assert(buf != NULL);

	(void)memset(buf, 0, GRANULE_SIZE);
	buffer_unmap(buf);
}

void granule_memzero_mapped(void *buf)
{
	(void)memset(buf, 0, GRANULE_SIZE);
}

/*
 * The parent REC granules lock is expected to be acquired before functions
 * aux_granules_map() and aux_granules_unmap() are called.
 */
void *aux_granules_map(struct granule *rec_aux_pages[], unsigned int num_aux)
{
	void *rec_aux = NULL;

	assert(rec_aux_pages != NULL);
	assert(num_aux <= MAX_REC_AUX_GRANULES);

	for (unsigned int i = 0U; i < num_aux; i++) {
		void *aux = granule_map(rec_aux_pages[i],
					(enum buffer_slot)((unsigned int)
							   SLOT_REC_AUX0 + i));

		assert(aux != NULL);

		if (i == 0UL) {
			rec_aux = aux;
		}
	}
	return rec_aux;
}

void aux_granules_unmap(void *rec_aux, unsigned int num_aux)
{
	unsigned char *rec_aux_vaddr = (unsigned char *)rec_aux;

	assert(rec_aux != NULL);
	assert(num_aux <= MAX_REC_AUX_GRANULES);

	for (unsigned int i = 0U; i < num_aux; i++) {
		buffer_unmap((void *)((uintptr_t)rec_aux_vaddr + (i * GRANULE_SIZE)));
	}
}
