/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch_features.h>
#include <arch_helpers.h>
#include <assert.h>
#include <debug.h>
#include <errno.h>
#include <limits.h>
#include <stdbool.h>
#include <stdint.h>
#include <utils_def.h>
#include <xlat_contexts.h>
#include <xlat_defs.h>
#include <xlat_defs_private.h>
#include <xlat_tables.h>
#include <xlat_tables_private.h>

/*
 * Function that verifies that a memory map array is valid.
 * Returns:
 *        0: Success, the memory map array is valid.
 *   EINVAL: Invalid values were used as arguments.
 *   ERANGE: The memory limits were surpassed.
 *    EPERM: Region overlaps another one in an invalid way or is in an
 *	     incorrect order.
 */
static int validate_mmap_regions(struct xlat_mmap_region *mm,
				 unsigned int mm_regions,
				 uintptr_t ctx_base_va, size_t va_size,
				 xlat_addr_region_id_t region)
{
	uintptr_t mm_end_pa;
	uintptr_t previous_end_va;

	if (mm == NULL) {
		return -EINVAL;
	}

	if (mm_regions == 0U) {
		return -EINVAL;
	}

	for (unsigned int i = 0U; i < mm_regions; i++) {
		uintptr_t base_va;
		uintptr_t base_pa;
		uintptr_t end_pa;
		uintptr_t end_va;
		size_t size;
		size_t granularity;

		size = mm[i].size;
		granularity = mm[i].granularity;
		base_pa = mm[i].base_pa;
		base_va = mm[i].base_va;
		end_pa = base_pa + size - 1UL;

		VERBOSE("mm_region : pa 0x%lx, va 0x%lx, size 0x%lx\n",
			mm[i].base_pa, mm[i].base_va, mm[i].size);
		if (size == 0UL) {
			ERROR("mm_region %u size is zero\n", i);
			return -EINVAL;
		}

		if (region == VA_LOW_REGION) {
			if (((base_va & HIGH_REGION_MASK) != 0ULL) ||
			     (((base_va + size) & HIGH_REGION_MASK) != 0ULL)) {
				ERROR("%s (%u): Base VA and address space do not match: ",
							__func__, __LINE__);
				ERROR("Base va = 0x%lx, Address space = Low region\n",
					base_va);
				return -EINVAL;
			}
		}

		if (base_va < ctx_base_va) {
			ERROR("%s (%u): Base VA is not aligned with region start: ",
						__func__, __LINE__);
			ERROR("Base VA = 0x%lx, region start VA = 0x%lx\n",
				base_va, ctx_base_va);
			return -EINVAL;
		}

		/*
		 * If this context is handling the high half region of the VA,
		 * adjust the start address of this area by substracting the
		 * start address of the region as the table entries are
		 * relative to the latter. Once ttbr1_el2 is configured, the
		 * MMU will translate the addresses properly. Note that this is
		 * not needed for low_region in the default case, but do this anyway
		 * as it is needed in case a partial table is setup for low region.
		 */
		mm[i].base_va -= ctx_base_va;
		base_va = mm[i].base_va;
		end_va = base_va + mm[i].size;

		if (!IS_PAGE_ALIGNED(base_pa) || !IS_PAGE_ALIGNED(base_va) ||
				!IS_PAGE_ALIGNED(size)) {
			ERROR("%s (%u): Base PA, Base VA and size must be page aligned: ",
						__func__, __LINE__);
			return -EFAULT;
		}

		if ((granularity != XLAT_BLOCK_SIZE(0)) &&
		    (granularity != XLAT_BLOCK_SIZE(1)) &&
		    (granularity != XLAT_BLOCK_SIZE(2)) &&
		    (granularity != XLAT_BLOCK_SIZE(3))) {
			ERROR("%s (%u): Invalid granularity: ",
						__func__, __LINE__);
			return -EINVAL;
		}

		/* Check for overflows */
		if ((base_pa > end_pa) || (base_va > end_va)) {
			ERROR("%s (%u): Memory region overflow detected: ",
						__func__, __LINE__);
			return -ERANGE;
		}

		/*
		 * end_va is calculated as an offset with regards to the base
		 * address for the current context, so compare it against
		 * max_va_size to ensure we are within the allowed range.
		 */
		if (end_va > va_size) {
			ERROR("%s (%u): End VA exceeds the maximum VA size: ",
						__func__, __LINE__);
			return -ERANGE;
		}

		if (end_pa > xlat_arch_get_max_supported_pa()) {
			ERROR("%s (%u): End PA exceeds the maximum supported PA: ",
						__func__, __LINE__);
			return -ERANGE;
		}

		if (i > 0U) {
			if (base_va < mm[i - 1U].base_va) {
				/* Incorrect order */
				ERROR("%s (%u): Base VAs are not in ascending order: ",
							__func__, __LINE__);
				return -EPERM;
			}

			/*
			 * Check that the PA and the VA do not
			 * overlap with the ones on the previous region.
			 */
			previous_end_va = mm[i - 1U].base_va +
							mm[i - 1U].size - 1UL;

			/* No overlaps with VAs of previous regions */
			if (base_va <= previous_end_va) {
				ERROR("%s (%u): Base VA overlaps with a previous region: ",
							__func__, __LINE__);
				return -EPERM;
			}

			/*
			 * PA shouldn't be sanity checked in case of Transient
			 * regions as their PA is invalid at the time of
			 * creation.
			 */
			if (MT_TYPE(mm[i].attr) == MT_TRANSIENT) {
				continue;
			}
			/* No overlaps with PAs of previous regions */
			for (unsigned int j = 0; j < i; j++) {
				if (MT_TYPE(mm[j].attr) == MT_TRANSIENT) {
					continue;
				}
				mm_end_pa = mm[j].base_pa + mm[j].size - 1UL;

				if ((end_pa >= mm[j].base_pa) &&
				    (end_pa <= mm_end_pa)) {
					ERROR("%s (%u): End PA overlaps with a previous region: ",
								__func__, __LINE__);
					return -EPERM;
				}

				if ((base_pa >= mm[j].base_pa) &&
				    (base_pa <= mm_end_pa)) {
					ERROR("%s (%u): Base PA overlaps with a previous region: ",
								__func__, __LINE__);
					return -EPERM;
				}
			}
		}
	}

	return 0;
}

static int add_mmap_to_ctx_cfg(struct xlat_ctx_cfg *cfg,
				xlat_addr_region_id_t region,
				struct xlat_mmap_region *mm,
				unsigned int mm_regions,
				uint64_t partial_va_base,
				size_t va_size)
{
	int ret;

	if (region == VA_LOW_REGION) {
		if (partial_va_base == 0UL) {
			/*
			 * Initialize the base_va for the current context if not
			 * initialized yet.
			 *
			 * For the low region, the architecture mandates that
			 * base_va has to be 0.
			 */
			cfg->base_va = 0ULL;
		} else {
			/*
			 * If partial table base va is provided, use it as
			 * base_va.
			 */
			cfg->base_va = partial_va_base;
		}
	} else {
		/*
		 * Initialize the base_va for the current context if not
		 * initialized yet.
		 *
		 * For the high region, the architecture mandates that
		 * base_va has to be 0xFFFF-FFFF-FFFF-FFFF minus the VA space
		 * size plus one.
		 *
		 * Overwriting this field should not be a problem as its value
		 * is expected to be always the same.
		 */
		cfg->base_va = (~(0UL) - va_size + 1ULL);

		/* TODO partial_va_base is not supported for HIGH region. */
		assert(partial_va_base == 0UL);
	}


	ret = validate_mmap_regions(mm, mm_regions, cfg->base_va,
				    va_size, region);

	if (ret != 0) {
		return ret;
	}

	/* Adjust the cfg parameters which depend from the mmap regions */
	cfg->max_mapped_pa = 0ULL;
	for (unsigned int i = 0U; i < mm_regions; i++) {
		uintptr_t end_pa;

		assert(mm[i].size != 0UL);
		if (MT_TYPE(mm[i].attr) == MT_TRANSIENT) {
			continue;
		}

		end_pa = mm[i].base_pa + mm[i].size - 1ULL;
		if (end_pa > cfg->max_mapped_pa) {
			cfg->max_mapped_pa = end_pa;
		}
	}
	cfg->max_mapped_va_offset = mm[mm_regions - 1U].base_va +
				       mm[mm_regions - 1U].size - 1ULL;
	cfg->mmap = mm;
	cfg->mmap_regions = mm_regions;

	return 0;
}

int xlat_ctx_cfg_init(struct xlat_ctx_cfg *cfg,
		      xlat_addr_region_id_t region,
		      struct xlat_mmap_region *mm,
		      unsigned int mm_regions,
		      uint64_t partial_va_base,
		      size_t va_size,
		      uint32_t asid)
{
	int retval;
	size_t max_va_size = (is_feat_lpa2_4k_present() == true) ?
		MAX_VIRT_ADDR_SPACE_SIZE_LPA2 : MAX_VIRT_ADDR_SPACE_SIZE;

	if (cfg == NULL) {
		return -EINVAL;
	}

	if (mm == NULL) {
		return -EINVAL;
	}

	if (region >= VA_REGIONS) {
		return -EINVAL;
	}

	if (!GRANULE_ALIGNED(va_size) || !IS_POWER_OF_TWO(va_size)) {
		return -EINVAL;
	}

	if ((va_size > max_va_size) ||
	    (va_size < MIN_VIRT_ADDR_SPACE_SIZE)) {
		return -EINVAL;
	}

	if (cfg->init) {
		return -EALREADY;
	}

	if ((asid & ((1UL << TTBRx_EL2_ASID_WIDTH) - 1U)) != asid) {
		return -EINVAL;
	}

	/* cppcheck-suppress misra-c2012-10.6 */
	cfg->base_level = (GET_XLAT_TABLE_LEVEL_BASE(va_size));
	if ((partial_va_base != 0UL) &&
		(ALIGNED(partial_va_base, XLAT_BLOCK_SIZE(cfg->base_level)) == false)) {
		ERROR("%s: Partial base VA is not aligned with base level block size.",
							__func__);
		return -EINVAL;
	}

	retval = add_mmap_to_ctx_cfg(cfg, region, mm, mm_regions, partial_va_base, va_size);

	if (retval < 0) {
		return retval;
	}

	cfg->max_va_size = va_size;
	cfg->region = region;
	cfg->init = true;
	cfg->asid = asid;

	if (!is_mmu_enabled()) {
		inv_dcache_range((uintptr_t)cfg, sizeof(struct xlat_ctx_cfg));
		inv_dcache_range((uintptr_t)mm, sizeof(struct xlat_mmap_region)
					* mm_regions);
	}

	return 0;
}

static int xlat_ctx_init_cmn(struct xlat_ctx *ctx,
		  struct xlat_ctx_cfg *cfg,
		  struct xlat_ctx_tbls *tbls_ctx,
		  uint64_t *tables_ptr,
		  unsigned int ntables,
		  uint64_t base_table_pa,
		  long tbls_va_pa_diff)
{
	if ((ctx == NULL) || (tbls_ctx == NULL) || (cfg == NULL)) {
		return -EINVAL;
	}

	if ((tables_ptr == NULL) || (ntables == 0U)) {
		return -EINVAL;
	}

	if (ALIGNED(tables_ptr, XLAT_TABLES_ALIGNMENT) == false) {
		return -EINVAL;
	}

	if (tbls_ctx->init) {
		return -EALREADY;
	}

	if (!cfg->init) {
		return -EINVAL;
	}

	/* Add the configuration to the context */
	ctx->cfg = cfg;

	/* Initialize the tables structure */
	XLAT_INIT_CTX_TBLS(tbls_ctx, tables_ptr, ntables, base_table_pa, tbls_va_pa_diff);

	/* Add the tables to the context */
	ctx->tbls = tbls_ctx;

	if (!is_mmu_enabled()) {
		inv_dcache_range((uintptr_t)ctx, sizeof(struct xlat_ctx));
		inv_dcache_range((uintptr_t)tbls_ctx, sizeof(struct xlat_ctx_tbls));
		inv_dcache_range((uintptr_t)cfg, sizeof(struct xlat_ctx_cfg));
	}
	return xlat_init_tables_ctx(ctx);
}


int xlat_ctx_init(struct xlat_ctx *ctx,
		  struct xlat_ctx_cfg *cfg,
		  struct xlat_ctx_tbls *tbls_ctx,
		  uint64_t *tables_ptr,
		  unsigned int ntables,
		  uint64_t base_table_pa)
{
	return xlat_ctx_init_cmn(ctx, cfg, tbls_ctx, tables_ptr, ntables,
				base_table_pa, 0L);
}


int xlat_ctx_init_remapped_tbls(struct xlat_ctx *ctx,
		  struct xlat_ctx_cfg *cfg,
		  struct xlat_ctx_tbls *tbls_ctx,
		  uint64_t *tables_ptr,
		  unsigned int ntables,
		  uint64_t base_table_pa,
		  uint64_t tbls_array_va)
{
	long tbls_va_to_pa_diff = (long)tbls_array_va - (long)base_table_pa;

	return xlat_ctx_init_cmn(ctx, cfg, tbls_ctx, tables_ptr, ntables,
				base_table_pa, tbls_va_to_pa_diff);
}
