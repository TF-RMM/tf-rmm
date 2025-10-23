/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <assert.h>
#include <cpuid.h>
#include <debug.h>
#include <errno.h>
#include <rmm_el3_ifc.h>
#include <sizes.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>
#include <utils_def.h>
#include <xlat_low_va.h>
#include <xlat_low_va_arch.h>
#include <xlat_tables.h>


#define XLAT_LOW_VIRT_ADDR_SPACE_SIZE	(1UL << 41U)	/* 64TB */

IMPORT_SYM(uintptr_t, rmm_text_start, RMM_CODE_START);
IMPORT_SYM(uintptr_t, rmm_text_end, RMM_CODE_END);
IMPORT_SYM(uintptr_t, rmm_ro_start, RMM_RO_START);
IMPORT_SYM(uintptr_t, rmm_ro_end, RMM_RO_END);
IMPORT_SYM(uintptr_t, rmm_rw_start, RMM_RW_START);
IMPORT_SYM(uintptr_t, rmm_rw_end, RMM_RW_END);

/*
 * Memory map REGIONS used for the RMM runtime (static mappings)
 */
#define RMM_CODE_SIZE		(RMM_CODE_END - RMM_CODE_START)
#define RMM_RO_SIZE		(RMM_RO_END - RMM_RO_START)
#define RMM_RW_SIZE		(RMM_RW_END - RMM_RW_START)

/*
 * Define additional tables to cover the case where RMM may be located at a
 * different PA during LFA
 */
#define EXTRA_LFA_TABLES	5U

/*
 * Map the application binary data as RO. This is necessary so that the RMM can
 * simply access the app header structures. Execution is not enabled as RMM is
 * never intended to run app code in EL2. Write is not enabled as data pages
 * might only be written from EL0, and for that purpose a separate mapping is
 * created.
 */
#define RMM_APP			MAP_REGION_FLAT(			\
					0,				\
					0,				\
					(MT_RO_DATA | MT_REALM))

#define RMM_CODE		MAP_REGION_FLAT(			\
					RMM_CODE_START,			\
					RMM_CODE_SIZE,			\
					(MT_CODE | MT_REALM))

#define RMM_RO			MAP_REGION_FLAT(			\
					RMM_RO_START,			\
					RMM_RO_SIZE,			\
					(MT_RO_DATA | MT_REALM))

#define RMM_RW			MAP_REGION_FLAT(			\
					RMM_RW_START,			\
					RMM_RW_SIZE,			\
					(MT_RW_DATA | MT_REALM))

/*
 * Leave an invalid page between the end of RMM memory and the beginning
 * of the shared buffer VA. This will help to detect any memory access
 * underflow by RMM.
 */
#define RMM_SHARED_BUFFER_START	(RMM_RW_END + SZ_4K)

/*
 * Some of the fields for the RMM_SHARED and RMM_VA_POOL regions will be populated
 * at runtime.
 */
#define RMM_SHARED		MAP_REGION(				\
					0U,				\
					RMM_SHARED_BUFFER_START,	\
					0U,				\
					(MT_RW_DATA | MT_REALM))

/*
 * The VA pool region must be on discrete L2 and L3 tables so that this be created
 * separately. The base address will be determined at runtime.
 */
#define RMM_VA_POOL		MAP_REGION_TRANSIENT(			\
					0UL,				\
					RMM_VA_POOL_SIZE,		\
					XLAT_BLOCK_SIZE(1))

static struct xlat_low_va_info g_va_info;


struct xlat_low_va_info *xlat_get_low_va_info(void)
{
	return &g_va_info;
}

uintptr_t xlat_low_va_shared_buf_va(void)
{
	return RMM_SHARED_BUFFER_START;
}

static void sort_mmap_region_array(struct xlat_mmap_region *regions,
			unsigned int region_count)
{
	for (unsigned int i = 1; i < region_count; ++i) {
		struct xlat_mmap_region key = regions[i];
		int j = (int)i - 1;

		while ((j >= 0) && (regions[j].base_va > key.base_va)) {
			regions[j + 1] = regions[j];
			--j;
		}
		regions[j + 1] = key;
	}
}

/*
 * Find a suitable base address for the VA pool region.
 * The pool is placed after all existing regions with:
 * - A gap of 1 L1 block entry between the pool and other regions
 * - Alignment to L1 block size boundary
 * - Pool occupies separate L1 block entries (not shared with other regions)
 * - Pool fits within a single L1 table
 * - Minimum address of 1GB (SZ_1G)
 */
static uintptr_t find_va_pool_base(struct xlat_mmap_region *regions,
				   unsigned int region_count)
{
	uintptr_t l1_block_size = XLAT_BLOCK_SIZE(1);
	uintptr_t l1_table_size = l1_block_size * XLAT_TABLE_ENTRIES;
	uintptr_t min_address = SZ_1G;
	uintptr_t highest_end = min_address;

	/* Find the highest region end address */
	for (unsigned int i = 0; i < region_count; i++) {
		uintptr_t region_end = regions[i].base_va + regions[i].size;

		if (region_end > highest_end) {
			highest_end = region_end;
		}
	}

	/*
	 * Round up to next L1 block boundary to ensure the pool doesn't
	 * share L2/L3 tables with other regions
	 */
	uintptr_t candidate_base = round_up(highest_end, l1_block_size);

	/* Add 1 L1 block as a gap */
	candidate_base += l1_block_size;

	/*
	 * Ensure the pool fits within a single L1 table.
	 * If it doesn't fit, move to the next L1 table boundary.
	 */
	uintptr_t l1_table_start = round_down(candidate_base, l1_table_size);
	uintptr_t l1_table_end = l1_table_start + l1_table_size;

	if ((candidate_base + RMM_VA_POOL_SIZE) > l1_table_end) {
		/* Pool doesn't fit in current L1 table, move to next one */
		candidate_base = l1_table_end;
	}

	return candidate_base;
}

static int xlat_low_va_static_setup(struct xlat_mmap_region *plat_regions,
	unsigned int nregions, uintptr_t rmm_img_start,
	struct xlat_low_va_info *va_info)
{
	int ret;
	uintptr_t tbl_pa;
	unsigned int num_tbls;

	struct xlat_mmap_region regions[COMMON_REGIONS] = {
		[MAP_REGION_APP] = RMM_APP,
		[MAP_REGION_CODE] = RMM_CODE,
		[MAP_REGION_RO] = RMM_RO,
		[MAP_REGION_RW] = RMM_RW,
		[MAP_REGION_SHARED] = RMM_SHARED,
		[MAP_REGION_VA_POOL] = RMM_VA_POOL,
	};

	if (nregions > XLAT_EXTRA_MMAP_REGIONS) {
		ERROR("%s: Number of platform regions exceeds maximum (%u)\n",
			__func__, XLAT_EXTRA_MMAP_REGIONS);
		return -ERANGE;
	}

	if (va_info != NULL) {
		/* Flush previous low VA info before any use */
		flush_dcache_range((uintptr_t)va_info, sizeof(struct xlat_low_va_info));

		/* Validate the low VA info received from previous RMM */
		if (va_info->low_va_regions_capacity != TOTAL_MMAP_REGIONS) {
			ERROR("%s: Insufficient regions in previous low va info\n",
				__func__);
			ERROR("Expected: %u, Found: %u\n",
				TOTAL_MMAP_REGIONS,
				va_info->low_va_regions_capacity);
			return -ERANGE;
		}
	}

	g_va_info.low_va_regions_capacity = TOTAL_MMAP_REGIONS;

	/* Setup the parameters for the application binary data */
	regions[MAP_REGION_APP].base_pa = rmm_img_start;
	regions[MAP_REGION_APP].base_va = rmm_img_start;
	regions[MAP_REGION_APP].size = RMM_CODE_START - rmm_img_start;

	/* Setup the parameters of the shared area */
	regions[MAP_REGION_SHARED].base_pa = get_shared_buf_pa();
	regions[MAP_REGION_SHARED].size = rmm_el3_ifc_get_shared_buf_size();

	(void)memcpy((void *)&g_va_info.low_va_regions[0], (void *)&regions[0U],
			 sizeof(struct xlat_mmap_region) * COMMON_REGIONS);
	if (nregions > 0U) {
		assert(plat_regions != NULL);
		(void)memcpy((void *)&g_va_info.low_va_regions[COMMON_REGIONS],
				 (void *)&plat_regions[0U],
				 sizeof(struct xlat_mmap_region) * nregions);
	}

	g_va_info.low_va_regions_num = nregions + COMMON_REGIONS;

	/* Find suitable VA pool base address */
	uintptr_t va_pool_base = find_va_pool_base(&g_va_info.low_va_regions[0],
						   g_va_info.low_va_regions_num);
	g_va_info.dyn_va_pool_base = va_pool_base;
	g_va_info.low_va_regions[MAP_REGION_VA_POOL].base_va = va_pool_base;

	INFO("Dynamic VA pool base address: 0x%lx\n", va_pool_base);

	assert((va_pool_base + RMM_VA_POOL_SIZE) <= XLAT_LOW_VIRT_ADDR_SPACE_SIZE);

	/* Sort the regions based on base_va */
	sort_mmap_region_array(&g_va_info.low_va_regions[0], nregions + COMMON_REGIONS);

	/* Estimate the number of tables needed for the regions */
	num_tbls = (unsigned int)xlat_estimate_num_l3_l2_tables(&g_va_info.low_va_regions[0],
					nregions + COMMON_REGIONS);

	/* Add 2 additional tables for L0 and L1. */
	num_tbls += 2U;

	/*
	 * If previous low va info is available from previous RMM, we can reuse the memory
	 * allocated for the translation tables. Validate that there are enough tables
	 * allocated.
	 */
	if ((va_info != NULL)) {
		if (va_info->low_va_tbls.tables_num < num_tbls) {
			ERROR("Insufficient static tables in previous low va info\n");
			ERROR("Expected: %u, Found: %u\n",
				num_tbls,
				va_info->low_va_tbls.tables_num);
			return -ENOMEM;
		}
		num_tbls = va_info->low_va_tbls.tables_num;
		tbl_pa = va_info->low_va_tbls.base_table_pa;
	} else {
		/*
		 * Add a margin such that the same static table pool will be
		 * sufficient when RMM is Live firmware Activated.
		 */
		num_tbls += EXTRA_LFA_TABLES;

		/* Reserve memory for the translation tables */
		ret = rmm_el3_ifc_reserve_memory(num_tbls * GRANULE_SIZE, 0,
				GRANULE_SIZE, &tbl_pa);
		if (ret != 0) {
			ERROR("%s: Reserving memory for xlat low VA failed\n",
							__func__);
			return -ENOMEM;
		}
	}

	/* Invalidate the tables memory */
	inv_dcache_range(tbl_pa, num_tbls * sizeof(uint64_t) * XLAT_TABLE_ENTRIES);

	/* Initialize the translation context */
	ret = xlat_ctx_cfg_init(&g_va_info.low_va_ctx_cfg, VA_LOW_REGION,
				&g_va_info.low_va_regions[0], nregions + COMMON_REGIONS,
				0UL,
				XLAT_LOW_VIRT_ADDR_SPACE_SIZE,
				RMM_ASID);
	if (ret != 0) {
		ERROR("%s: xlat_ctx_cfg_init() failed (%i)\n", __func__, ret);
		return ret;
	}

	ret = xlat_ctx_init(&g_va_info.low_va_ctx, &g_va_info.low_va_ctx_cfg,
			&g_va_info.low_va_tbls,
			(uint64_t *)tbl_pa,
			num_tbls,
			(uint64_t)tbl_pa);
	if (ret != 0) {
		ERROR("%s: xlat_ctx_init() failed (%i)\n", __func__, ret);
		return ret;
	}

	INFO("Static Low VA initialized. xlat tables allocated: %u used: %u\n",
				num_tbls, g_va_info.low_va_ctx.tbls->next_table);

	return 0;
}

/*
 * Setup the Low VA translation tables and context. This includes both static
 * and dynamic tables. If previous low va info is provided, it reuses the
 * static tables from previous RMM instance.
 */
int xlat_low_va_setup(struct xlat_mmap_region *plat_regions,
	unsigned int nregions, uintptr_t rmm_img_start,
	struct xlat_low_va_info *va_info)
{
	int ret;

	assert(!is_mmu_enabled());

	ret = xlat_low_va_static_setup(plat_regions, nregions, rmm_img_start, va_info);
	if (ret != 0) {
		ERROR("%s: xlat_low_va_static_setup() failed (%i)\n", __func__, ret);
		return ret;
	}

	/* Invalidate the low va info structure as we have modified it with MMU off. */
	inv_dcache_range((uintptr_t)&g_va_info, sizeof(g_va_info));
	return 0;
}

/*
 * Configure MMU for low VA space
 */
int xlat_low_va_mmu_cfg(void)
{
	struct xlat_mmu_cfg mmu_config;
	int ret;

	/* Setup the MMU cfg for the low region (runtime context) */
	ret = xlat_arch_setup_mmu_cfg(&g_va_info.low_va_ctx, &mmu_config);
	if (ret != 0) {
		ERROR("%s (%u): Failed to setup xlat tables for CPU[%u]\n",
			__func__, __LINE__, my_cpuid());
		return ret;
	}

	xlat_arch_write_mmu_cfg(&mmu_config);
	return 0;
}
