/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef TRACKING_REGION_PVT_H
#define TRACKING_REGION_PVT_H

#include <rwlock.h>
#include <tracking_region.h>

#define TR_STATE_WIDTH		U(2)
#define TR_STATE_SHIFT		U(0)

#define TR_MEM_CAT_WIDTH	U(2)
#define TR_MEM_CAT_SHIFT	(TR_STATE_SHIFT + TR_STATE_WIDTH)

/*
 * struct tracking_region stores the tracking state, memory category,
 * transition marker, reader-writer lock and coarse granule for one region.
 *
 * An instance exists for every represented region, irrespective of its current
 * tracking state. In COARSE state, the memory category selects the active
 * member of the union. In FINE state, granules and dev_granules are held in
 * separate arrays.
 */
struct tracking_region {
	/* Place the 8-byte-aligned lock first to avoid padding around the union. */
	rwlock_t lock;

	/* For coarse tracking, the memory category selects the active member. */
	union {
		struct granule coarse_granule;
		struct dev_granule coarse_dev_granule;
	};
	/*
	 * Bit fields in struct tracking_region:
	 * [4]:		SRO representation transition in progress
	 * [3:2]:	memory category
	 * [1:0]:	tracking state
	 */
	uint8_t descriptor;
};

/*
 * Validate @addr against the selected memory banks and return its
 * struct tracking_region, or NULL if the address is invalid or the array has not
 * been populated.
 */
struct tracking_region *tracking_region_find(unsigned long addr,
					     enum tr_mem_type type);

/* Return the tracking state recorded in @tr. */
enum tr_state tracking_region_get_state(const struct tracking_region *tr);

/* Return whether an SRO is changing @tr's active tracking representation. */
bool tracking_region_transition_pending(const struct tracking_region *tr);

/*
 * Return the reserved VA base and active page count for the array of
 * struct tracking_region. The active span can be smaller than the worst-case VA
 * reservation and need not have backing memory when this function is called.
 */
void tracking_region_array_active_range(uintptr_t *base,
					unsigned long *pages);

/*
 * Return the reserved, page-aligned fine-granule range for memory @type in
 * tracking region @tr_idx. Return false without updating the outputs when the
 * region contains no memory of that type. The range need not have backing.
 */
bool tracking_region_fine_page_range(unsigned long tr_idx,
				     enum tr_mem_type type,
				     uintptr_t *base,
				     unsigned long *pages);

/* Return whether reserved tracking-metadata @va currently has backing. */
bool tracking_region_page_is_mapped(uintptr_t va);

/* Return the PA backing a mapped tracking-metadata @va. */
uintptr_t tracking_region_page_to_pa(uintptr_t va);

/* Map page-aligned tracking-metadata VA @va to backing PA @pa. */
int tracking_region_page_populate(uintptr_t va, uintptr_t pa);

/* Remove the backing mapping from page-aligned tracking-metadata @va. */
int tracking_region_page_depopulate(uintptr_t va);

/*
 * Validate the SET_TRACKING inputs and return the selected struct tracking_region
 * and its array index. A region-aligned hole is accepted only when a
 * bank occurs later in the same region. tracking_region_set_tracking_owned()
 * performs the composition-specific target-state validation.
 */
bool tracking_region_set_tracking_find(unsigned long addr,
				       unsigned long category,
				       unsigned long *tr_idx,
				       struct tracking_region **tr);

/*
 * Return the next populated range of @type within the tracking region at
 * @base. The caller initializes @cursor to zero and preserves it between
 * calls. On success, @start and @end describe a non-empty, half-open range and
 * @fine_idx receives the type-local fine-granule index corresponding to
 * @start, and @cursor is advanced. Return false after the final intersecting
 * bank.
 */
bool tracking_region_next_bank_range(unsigned long base,
				     enum tr_mem_type type,
				     unsigned int *cursor,
				     unsigned long *start,
				     unsigned long *end,
				     unsigned long *fine_idx);

/* Return whether Granule @addr backs a fine-metadata page belonging to @tr. */
bool tracking_region_is_self_describing_fine_page(
					const struct tracking_region *tr,
					unsigned long addr);

/*
 * Set or clear the in-progress representation-transition marker. The caller
 * must hold @tr's write lock.
 */
void tracking_region_transition_set_locked(struct tracking_region *tr,
					   bool pending);

/*
 * Change a tracking representation on behalf of the SRO which owns @tr's
 * transition marker. Return an RMI status code with the same semantics as
 * tracking_region_set_tracking().
 */
unsigned long tracking_region_set_tracking_owned(unsigned long addr,
						 unsigned long category,
						 unsigned long state);

/*
 * Initialize the fine granule for self-describing metadata page @addr as
 * INTERNAL. The caller must hold @tr's write lock while its transition marker
 * is set. @addr must be a Host-donated conventional page within @tr.
 */
void tracking_region_fine_descriptor_init_internal_locked(
					struct tracking_region *tr,
					unsigned long addr);

/* Return the fine granule at @idx. */
struct granule *tr_fine_granule_from_idx(unsigned long idx);

/* Return the index of fine granule @g. */
unsigned long tr_fine_granule_to_idx(const struct granule *g);

/* Return the fine dev_granule at @idx. */
struct dev_granule *tr_fine_dev_granule_from_idx(unsigned long idx);

/* Return the index of fine dev_granule @g. */
unsigned long tr_fine_dev_granule_to_idx(const struct dev_granule *g);

/*
 * Convert a valid granule-aligned address using its bank-local base and full
 * tracking-region offset. @type selects the fine granule or dev_granule
 * array. If non-NULL, @category receives the exact RMI memory category.
 * UINT64_MAX is returned for an invalid address.
 */
unsigned long tracking_region_fine_addr_to_idx(
						unsigned long addr,
						enum tr_mem_type type,
						unsigned long *category);

/*
 * Convert an index in the fine granule or dev_granule array
 * to its valid PA. Indices reserved for holes are rejected. If non-NULL,
 * @category receives the exact RMI memory category. UINT64_MAX is returned
 * for an invalid index.
 */
unsigned long tracking_region_fine_idx_to_addr(
						unsigned long idx,
						enum tr_mem_type type,
						unsigned long *category);

/*
 * Convert an address to its compressed struct tracking_region array index. The
 * address must be granule aligned but need not be tracking-region aligned.
 * @type selects the conventional or device struct tracking_memory_bank array.
 * Both refer to the same struct tracking_region array. If non-NULL, @category
 * receives the exact memory category. UINT64_MAX is returned when the address
 * is invalid for the selected memory type.
 */
unsigned long tracking_region_addr_to_idx(unsigned long addr,
					  enum tr_mem_type type,
					  unsigned long *category);

#endif /* TRACKING_REGION_PVT_H */
