/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef XLAT_LOW_VA_H
#define XLAT_LOW_VA_H

#include <stdint.h>
#include <xlat_tables.h>

enum map_regions {
	MAP_REGION_APP,
	MAP_REGION_CODE,
	MAP_REGION_RO,
	MAP_REGION_RW,
	MAP_REGION_SHARED,
	MAP_REGION_VA_POOL,
	NR_MAP_REGIONS
};

/* Extra regions for platform-specific mappings */
#define XLAT_EXTRA_MMAP_REGIONS		5U

/* MISRA insists on an unsigned type for the number of regions. */
#define COMMON_REGIONS	((unsigned int)NR_MAP_REGIONS)

/* Total number of memory map regions */
#define TOTAL_MMAP_REGIONS	(COMMON_REGIONS + XLAT_EXTRA_MMAP_REGIONS)

/*
 * Structure to hold the Low VA translation information.
 * Align to cache line size as this structure will be accessed prior
 * to MMU enable.
 */
/* NOLINTNEXTLINE(clang-analyzer-optin.performance.Padding) as fields are in logical order*/
struct xlat_low_va_info {
	/* Structures to hold the Static Low VA translation context information */
	struct xlat_ctx low_va_ctx;
	struct xlat_mmap_region low_va_regions[TOTAL_MMAP_REGIONS];

	/* Static Low VA regions for RMM */
	unsigned int low_va_regions_num;
	unsigned int low_va_regions_capacity;

	/* The below fields are copied over from previous RMM in case of LFA */
	/* Structures to hold the dynamic Low VA translation context info */
	struct xlat_ctx dyn_va_ctx;

	/* Size of the dynamic VA pool */
	size_t dyn_va_pool_size;

	/* Base address of the dynamic VA pool */
	uintptr_t dyn_va_pool_base;

} __aligned(CACHE_WRITEBACK_GRANULE);

/* Setup low VA translation tables */
int xlat_low_va_setup(struct xlat_mmap_region *plat_regions,
			unsigned int nregions, uintptr_t rmm_img_start,
			struct xlat_low_va_info *va_info);

/* Configure MMU for low VA space */
int xlat_low_va_mmu_cfg(void);

/* Get the VA of the shared buffer */
uintptr_t xlat_low_va_shared_buf_va(void);

/* Get the Low VA information */
struct xlat_low_va_info *xlat_get_low_va_info(void);

/* Allocate VA and map memory */
uintptr_t xlat_low_va_map(size_t size, uint64_t attr, uintptr_t in_pa, bool clear_memory);

/*
 * Unmap VA and free the allocated VA space. The caller should ensure that the VA has been mapped
 * with xlat_low_va_map() before calling this function. This function does not check if the VA is
 * currently mapped or not. There is an assertion in the implementation that will fail if the VA
 * is not currently mapped.
 */
int xlat_low_va_unmap(uintptr_t va, size_t size);

/* Get dynamic VA base */
uintptr_t xlat_low_va_get_dyn_va_base(void);

/*
 * Walk the low VA translation tables starting at 'va' and return the
 * corresponding PA via 'pa_out'. The function then checks subsequent L3
 * descriptors for physically contiguous mappings, accumulating their size.
 *
 * The walk terminates when:
 *   - The VA reaches 'top_va' (exclusive upper bound), or
 *   - A descriptor is invalid/empty, or
 *   - The next PA is not contiguous with the previous one.
 *
 * This function assumes that tables are created down to L3.
 *
 * Arguments:
 *   - va: Starting virtual address (must be page-aligned).
 *   - top_va: Upper VA limit (exclusive, must be page-aligned, > va).
 *   - pa_out: Output pointer for the PA corresponding to 'va'.
 *
 * Returns:
 *   - The accumulated contiguous size (in bytes) starting from 'va'.
 *   - 0 if the starting VA is not validly mapped or inputs are invalid.
 *   - On success, *pa_out contains the PA of 'va'.
 */
size_t xlat_low_va_get_contig_pa(uintptr_t va, uintptr_t top_va,
				     uintptr_t *pa_out);

/*
 * Reserve a contiguous VA region in the dynamic VA pool without mapping
 * any PA. The reserved region is invisible to hardware and cannot be used
 * for translation until populated and committed.
 *
 * Arguments:
 *   - size: Size to reserve (must be granule-aligned, > 0).
 *   - reserved_va: Output pointer for the reserved VA base.
 *
 * Returns:
 *   - 0 on success with *reserved_va set.
 *   - Negative error code on failure.
 */
int xlat_low_va_reserve(size_t size, uintptr_t *reserved_va);

/*
 * Populate a sub-range of a previously reserved VA region with a PA mapping.
 * The entries are written with full attributes but remain invalid to hardware.
 * Multiple calls can populate different (non-overlapping) sub-ranges of the
 * same reservation with different PAs.
 *
 * Arguments:
 *   - va: Starting VA to populate (must be within a reserved region).
 *   - pa: Physical address to map (must be granule-aligned).
 *   - size: Size to populate (must be granule-aligned, > 0).
 *   - attr: Memory attributes for the mapping.
 *
 * Returns:
 *   - 0 on success.
 *   - Negative error code on failure.
 */
int xlat_low_va_populate(uintptr_t va, uintptr_t pa, size_t size, uint64_t attr);

/*
 * Commit a previously populated VA region, making all entries valid to
 * hardware. After this call the CPU can translate through the region.
 * The entire range must have been populated before committing.
 *
 * Arguments:
 *   - va: Starting VA to commit (must be granule-aligned).
 *   - size: Size to commit (must be granule-aligned, > 0).
 *
 * Returns:
 *   - 0 on success.
 *   - Negative error code on failure.
 */
int xlat_low_va_commit(uintptr_t va, size_t size);

/*
 * Decommit a previously committed VA region, making entries invalid to
 * hardware while retaining the VA reservation and PA/attribute data.
 * The region can be re-committed later with xlat_low_va_commit.
 * TLB is invalidated for the affected range.
 *
 * Arguments:
 *   - va: Starting VA to decommit (must be granule-aligned).
 *   - size: Size to decommit (must be granule-aligned, > 0).
 *
 * Returns:
 *   - 0 on success.
 *   - Negative error code on failure.
 */
int xlat_low_va_decommit(uintptr_t va, size_t size);

/*
 * Release a VA reservation, returning the VA space to the free pool.
 * The region must not be valid (must be reserved, populated-but-uncommitted,
 * or decommitted). Use xlat_low_va_decommit first if the region is live.
 *
 * Arguments:
 *   - va: Starting VA to unreserve (must be granule-aligned).
 *   - size: Size to unreserve (must be granule-aligned, > 0).
 *
 * Returns:
 *   - 0 on success.
 *   - Negative error code on failure.
 */
int xlat_low_va_unreserve(uintptr_t va, size_t size);

#endif /* XLAT_LOW_VA_H */
