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
		end_va = base_va + size - 1UL;

		if (region == VA_LOW_REGION) {
			if (((base_va & HIGH_REGION_MASK) != 0ULL) ||
			     (((base_va + size) & HIGH_REGION_MASK) != 0ULL)) {
				ERROR("%s (%u): Base VA and address space do not match: ",
							__func__, __LINE__);
				ERROR("Base va = 0x%lx, Address space = Low region\n",
					base_va);
				return -EINVAL;
			}
		} else {
			if (base_va < ctx_base_va) {
				ERROR("%s (%u): Base VA is not aligned with high region start: ",
							__func__, __LINE__);
				ERROR("Base VA = 0x%lx, high region start VA = 0x%lx\n",
				base_va, ctx_base_va);
				return -EINVAL;
			}
			/*
			 * If this context is handling the high half region of the VA,
			 * adjust the start address of this area by substracting the
			 * start address of the region as the table entries are
			 * relative to the latter. Once ttbr1_el2 is configured, the
			 * MMU will translate the addresses properly.
			 */
			mm[i].base_va -= ctx_base_va;
			base_va = mm[i].base_va;
			end_va = base_va + mm[i].size;
		}

		if (!IS_PAGE_ALIGNED(base_pa) || !IS_PAGE_ALIGNED(base_va) ||
				!IS_PAGE_ALIGNED(size)) {
			return -EFAULT;
		}

		if ((granularity != XLAT_BLOCK_SIZE(0)) &&
		    (granularity != XLAT_BLOCK_SIZE(1)) &&
		    (granularity != XLAT_BLOCK_SIZE(2)) &&
		    (granularity != XLAT_BLOCK_SIZE(3))) {
			return -EINVAL;
		}

		/* Check for overflows */
		if ((base_pa > end_pa) || (base_va > end_va)) {
			return -ERANGE;
		}

		/*
		 * end_va is calculated as an offset with regards to the base
		 * address for the current context, so compare it against
		 * max_va_size to ensure we are within the allowed range.
		 */
		if (end_va > va_size) {
			return -ERANGE;
		}

		if (end_pa > xlat_arch_get_max_supported_pa()) {
			return -ERANGE;
		}

		if (i > 0U) {
			if (base_va < mm[i - 1U].base_va) {
				/* Incorrect order */
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
					return -EPERM;
				}

				if ((base_pa >= mm[j].base_pa) &&
				    (base_pa <= mm_end_pa)) {
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
				size_t va_size)
{
	int ret;

	if (region == VA_LOW_REGION) {
		/*
		 * Initialize the base_va for the current context if not
		 * initialized yet.
		 *
		 * For the low region, the architecture mandates that
		 * base_va has to be 0.
		 *
		 * Overwriting this field should not be a problem as its value
		 * is expected to be always the same.
		 */
		cfg->base_va = 0ULL;
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
		      size_t va_size)
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

	if ((va_size & (GRANULE_SIZE - 1ULL)) != 0ULL) {
		return -EINVAL;
	}

	if ((va_size > max_va_size) ||
	    (va_size < MIN_VIRT_ADDR_SPACE_SIZE)) {
		return -EINVAL;
	}

	if (cfg->initialized == true) {
		return -EALREADY;
	}

	retval = add_mmap_to_ctx_cfg(cfg, region, mm, mm_regions, va_size);

	if (retval < 0) {
		return retval;
	}

	cfg->max_va_size = va_size;

	/* cppcheck-suppress misra-c2012-10.6 */
	cfg->base_level = (GET_XLAT_TABLE_LEVEL_BASE(va_size));
	cfg->region = region;
	cfg->initialized = true;

	if (!is_mmu_enabled()) {
		inv_dcache_range((uintptr_t)cfg, sizeof(struct xlat_ctx_cfg));
		inv_dcache_range((uintptr_t)mm, sizeof(struct xlat_mmap_region));
	}

	return 0;
}

int xlat_ctx_init(struct xlat_ctx *ctx,
		  struct xlat_ctx_cfg *cfg,
		  struct xlat_ctx_tbls *tbls_ctx,
		  uint64_t *tables_ptr,
		  unsigned int ntables)
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

	if (tbls_ctx->initialized == true) {
		return -EALREADY;
	}

	if (cfg->initialized == false) {
		return -EINVAL;
	}

	/* Add the configuration to the context */
	ctx->cfg = cfg;

	/* Initialize the tables structure */
	XLAT_INIT_CTX_TBLS(tbls_ctx, tables_ptr, ntables);

	/* Add the tables to the context */
	ctx->tbls = tbls_ctx;

	if (!is_mmu_enabled()) {
		inv_dcache_range((uintptr_t)ctx, sizeof(struct xlat_ctx));
		inv_dcache_range((uintptr_t)tbls_ctx, sizeof(struct xlat_ctx_tbls));
		inv_dcache_range((uintptr_t)cfg, sizeof(struct xlat_ctx_cfg));
	}
	return xlat_init_tables_ctx(ctx);
}
