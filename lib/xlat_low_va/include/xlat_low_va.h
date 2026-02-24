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

#endif /* XLAT_LOW_VA_H */
