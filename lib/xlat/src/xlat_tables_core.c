/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 * SPDX-FileCopyrightText: Copyright Arm Limited and Contributors.
 */

/* This file is derived from xlat_table_v2 library in TF-A project */

#include <arch_features.h>
#include <arch_helpers.h>
#include <assert.h>
#include <debug.h>
#include <errno.h>
#include <stdbool.h>
#include <stdint.h>
#include <utils_def.h>
#include <xlat_contexts.h>
#include "xlat_defs_private.h"
#include <xlat_tables.h>
#include "xlat_tables_private.h"

/*
 * Enumeration of actions that can be made when mapping table entries depending
 * on the previous value in that entry and information about the region being
 * mapped.
 */
typedef enum {

	/* Do nothing */
	ACTION_NONE,

	/* Write a block (or page, if in level 3) entry. */
	ACTION_WRITE_BLOCK_ENTRY,

	/*
	 * Create a new table and write a table entry pointing to it. Recurse
	 * into it for further processing.
	 */
	ACTION_CREATE_NEW_TABLE,

	/*
	 * There is a table descriptor in this entry, read it and recurse into
	 * that table for further processing.
	 */
	ACTION_RECURSE_INTO_TABLE,

} action_t;

/* Returns a pointer to the first empty translation table. */
static inline uint64_t *xlat_table_get_empty(struct xlat_ctx *ctx)
{
	assert(ctx->tbls->next_table < ctx->tbls->tables_num);

	return &ctx->tbls->tables[(size_t)XLAT_TABLE_ENTRIES *
					ctx->tbls->next_table++];
}

/*
 * Function that returns the index of the first table affected by the VA on
 * the specified mmap region.
 */
static uintptr_t xlat_tables_find_start_va(struct xlat_mmap_region *mm,
					   const uintptr_t table_base_va,
					   const int level)
{
	uintptr_t table_idx_va;

	if (mm->base_va > table_base_va) {
		/* Find the first index of the table affected by the region. */
		table_idx_va = mm->base_va & ~XLAT_BLOCK_MASK(level);
	} else {
		/* Start from the beginning of the table. */
		table_idx_va = table_base_va;
	}

	return table_idx_va;
}

/*
 * Function that returns table index for the given VA and level arguments.
 */
static inline unsigned int  xlat_tables_va_to_index(const uintptr_t table_base_va,
						    const uintptr_t va,
						    const int level)
{
	return (unsigned int)((va - table_base_va) >> XLAT_ADDR_SHIFT(level));
}

/*
 * From the given arguments, it decides which action to take when mapping the
 * specified region.
 */
static action_t xlat_tables_map_region_action(const struct xlat_mmap_region *mm,
					      unsigned int desc_type,
					      uintptr_t dest_pa,
					      uintptr_t table_entry_base_va,
					      int level)
{
	uintptr_t mm_end_va = mm->base_va + mm->size - 1UL;
	uintptr_t table_entry_end_va = table_entry_base_va +
					XLAT_BLOCK_SIZE(level) - 1UL;

	/*
	 * The descriptor types allowed depend on the current table level.
	 */

	if ((mm->base_va <= table_entry_base_va) &&
	    (mm_end_va >= table_entry_end_va)) {

		/*
		 * Table entry is covered by region
		 * --------------------------------
		 *
		 * This means that this table entry can describe the whole
		 * translation with this granularity in principle.
		 */

		if (level == 3) {
			/*
			 * Last level, only page descriptors are allowed.
			 */
			if (desc_type == PAGE_DESC) {
				/*
				 * There's another region mapped here, don't
				 * overwrite.
				 */
				return ACTION_NONE;
			}
			if (desc_type != INVALID_DESC) {
				ERROR("%s (%u): Expected invalid descriptor\n",
					__func__, __LINE__);
				panic();
			}
			return ACTION_WRITE_BLOCK_ENTRY;
		} else {

			/*
			 * Other levels. Table descriptors are allowed. Block
			 * descriptors too, but they have some limitations.
			 */

			if (desc_type == TABLE_DESC) {
				/* There's already a table, recurse into it. */
				return ACTION_RECURSE_INTO_TABLE;

			} else if (desc_type == INVALID_DESC) {
				/*
				 * There's nothing mapped here, create a new
				 * entry.
				 *
				 * Check if the destination granularity allows
				 * us to use a block descriptor or we need a
				 * finer table for it.
				 *
				 * Also, check if the current level allows block
				 * descriptors. If not, create a table instead.
				 */
				if (((dest_pa & XLAT_BLOCK_MASK(level)) != 0U)
				    || (level < XLAT_MIN_BLOCK_LVL()) ||
				    (mm->granularity < XLAT_BLOCK_SIZE(level))) {
					return ACTION_CREATE_NEW_TABLE;
				} else {
					return ACTION_WRITE_BLOCK_ENTRY;
				}

			} else {
				/*
				 * There's another region mapped here, don't
				 * overwrite.
				 */
				if (desc_type != BLOCK_DESC) {
					ERROR("%s (%u): Excpected block descriptor\n",
						__func__, __LINE__);
					panic();
				}

				return ACTION_NONE;
			}
		}

	} else if ((mm->base_va <= table_entry_end_va) ||
		   (mm_end_va >= table_entry_base_va)) {

		/*
		 * Region partially covers table entry
		 * -----------------------------------
		 *
		 * This means that this table entry can't describe the whole
		 * translation, a finer table is needed.

		 * There cannot be partial block overlaps in level 3. If that
		 * happens, some of the preliminary checks when adding the
		 * mmap region failed to detect that PA and VA must at least be
		 * aligned to PAGE_SIZE.
		 */
		if (level >= 3) {
			ERROR("%s (%u): Expected table level below 3\n",
				__func__, __LINE__);
			panic();
		}

		if (desc_type == INVALID_DESC) {
			/*
			 * The block is not fully covered by the region. Create
			 * a new table, recurse into it and try to map the
			 * region with finer granularity.
			 */
			return ACTION_CREATE_NEW_TABLE;

		} else {
			if (desc_type != TABLE_DESC) {
				ERROR("%s (%u): Expected table descriptor\n",
					__func__, __LINE__);
				panic();
			}
			/*
			 * The block is not fully covered by the region, but
			 * there is already a table here. Recurse into it and
			 * try to map with finer granularity.
			 *
			 * PAGE_DESC for level 3 has the same value as
			 * TABLE_DESC, but this code can't run on a level 3
			 * table because there can't be overlaps in level 3.
			 */
			return ACTION_RECURSE_INTO_TABLE;
		}
	} else {

		/*
		 * This table entry is outside of the region specified in the
		 * arguments, don't write anything to it.
		 */
		return ACTION_NONE;
	}
}

/*
 * Recursive function that writes to the translation tables and maps the
 * specified region. On success, it returns the VA of the last byte that was
 * successfully mapped. On error, it returns the VA of the next entry that
 * should have been mapped.
 *
 * NOTE: This function violates misra-c2012-17.2 due to recursivity.
 */
/* coverity[misra_c_2012_rule_17_2_violation:SUPPRESS] */
static uintptr_t xlat_tables_map_region(struct xlat_ctx *ctx,
					struct xlat_mmap_region *mm,
					uintptr_t table_base_va,
					uintptr_t *const table_base,
					unsigned int table_entries,
					int level)
{
	uintptr_t table_idx_va;
	unsigned int table_idx;
	uintptr_t mm_end_va;
	struct xlat_ctx_cfg *ctx_cfg;

	assert(mm != NULL);
	assert(ctx != NULL);
	ctx_cfg = ctx->cfg;

	assert(ctx_cfg != NULL);
	assert((level >= ctx_cfg->base_level) &&
	       (level <= XLAT_TABLE_LEVEL_MAX));
	assert(table_entries <= XLAT_GET_TABLE_ENTRIES(level));

	mm_end_va = mm->base_va + mm->size - 1U;

	if ((level < ctx_cfg->base_level) ||
	    (level > XLAT_TABLE_LEVEL_MAX)) {
		ERROR("%s (%u): Level out of boundaries (%i)\n",
			__func__, __LINE__, level);
		panic();
	}

	table_idx_va = xlat_tables_find_start_va(mm, table_base_va, level);
	table_idx = xlat_tables_va_to_index(table_base_va, table_idx_va, level);

	while (table_idx < table_entries) {
		uintptr_t table_idx_pa;
		uint64_t *subtable;
		uint64_t desc;

		desc = table_base[table_idx];

		table_idx_pa = mm->base_pa + table_idx_va - mm->base_va;

		action_t action = xlat_tables_map_region_action(mm,
			(uint32_t)(desc & DESC_MASK), table_idx_pa,
			table_idx_va, level);

		if (action == ACTION_WRITE_BLOCK_ENTRY) {
			table_base[table_idx] =
				xlat_desc(mm->attr, table_idx_pa, level);

		} else if (action == ACTION_CREATE_NEW_TABLE) {
			uintptr_t end_va;

			subtable = xlat_table_get_empty(ctx);
			if (subtable == NULL) {
				/* Not enough free tables to map this region */
				ERROR("%s (%u): Not enough free tables to map region\n",
					__func__, __LINE__);
				panic();
			}

			/* Point to new subtable from this one. */
			table_base[table_idx] =
				TABLE_DESC | (uintptr_t)(void *)subtable;

			/* Recurse to write into subtable */
			/* cppcheck-suppress misra-c2012-17.2 */
			end_va = xlat_tables_map_region(ctx, mm, table_idx_va,
					       subtable, XLAT_TABLE_ENTRIES,
					       level + 1);
			if (end_va != (table_idx_va + XLAT_BLOCK_SIZE(level) - 1UL)) {
				return end_va;
			}

		} else if (action == ACTION_RECURSE_INTO_TABLE) {
			uintptr_t end_va;

			subtable = (uint64_t *)(void *)xlat_get_oa_from_tte(desc);
			/* Recurse to write into subtable */
			/* cppcheck-suppress misra-c2012-17.2 */
			end_va = xlat_tables_map_region(ctx, mm, table_idx_va,
					       subtable, XLAT_TABLE_ENTRIES,
					       level + 1);
			if (end_va != (table_idx_va + XLAT_BLOCK_SIZE(level) - 1UL)) {
				return end_va;
			}

		} else {
			if (action != ACTION_NONE) {
				ERROR("%s (%u): Unexpected action: %u\n",
					__func__, __LINE__, action);
				panic();
			}
		}

		table_idx++;
		table_idx_va += XLAT_BLOCK_SIZE(level);

		/* If reached the end of the region, exit */
		if (mm_end_va <= table_idx_va) {
			break;
		}
	}

	return table_idx_va - 1U;
}

/*
 * Returns a block/page table descriptor for the given level and attributes.
 */
uint64_t xlat_desc(uint64_t attr, uintptr_t addr_pa, int level)
{
	uint64_t desc;
	uint64_t mem_type;
	bool lpa2_enabled = is_feat_lpa2_4k_present();

	if ((MT_TYPE(attr) == MT_TRANSIENT)) {
		/* Transient entry requested. */
		desc = TRANSIENT_DESC;
		return desc;
	}

	/* Make sure that the granularity is fine enough to map this address. */
	assert((addr_pa & XLAT_BLOCK_MASK(level)) == 0U);

	desc = set_oa_to_tte(addr_pa);

	/*
	 * There are different translation table descriptors for level 3 and the
	 * rest.
	 */
	desc |= (level == XLAT_TABLE_LEVEL_MAX) ? PAGE_DESC : BLOCK_DESC;
	/*
	 * Always set the access flag, as this library assumes access flag
	 * faults aren't managed.
	 */
	desc |= LOWER_ATTRS(ACCESS_FLAG);

	/* Determine the physical address space this region belongs to. */
	desc |= xlat_arch_get_pas(attr);

	/*
	 * Deduce other fields of the descriptor based on the MT_RW memory
	 * region attributes.
	 */
	desc |= ((attr & MT_RW) != 0UL) ? LOWER_ATTRS(AP_RW) : LOWER_ATTRS(AP_RO);

	if ((attr & MT_NG) != 0UL) {
		desc |= XLAT_GET_NG_HINT();
	}

	/*
	 * Mark this area as non-executable for unprivileged exception levels,
	 * if not marked otherwise.
	 */
	if ((attr & MT_EXEC_UNPRIV) == 0UL) {
		desc |= XLAT_GET_UXN_DESC();
	}

	if ((attr & MT_AP_UNPRIV) != 0UL) {
		desc |= XLAT_GET_AP_ACCESS_UNPRIV_DESC();
	}

	/*
	 * Deduce shareability domain and executability of the memory region
	 * from the memory type of the attributes (MT_TYPE).
	 *
	 * Data accesses to device memory and non-cacheable normal memory are
	 * coherent for all observers in the system, and correspondingly are
	 * always treated as being Outer Shareable. Therefore, for these 2 types
	 * of memory, it is not strictly needed to set the shareability field
	 * in the translation tables.
	 */
	mem_type = MT_TYPE(attr);
	if (mem_type == MT_DEVICE) {
		desc |= LOWER_ATTRS(ATTR_DEVICE_INDEX);

		/*
		 * Always map device memory as execute-never.
		 * This is to avoid the possibility of a speculative instruction
		 * fetch, which could be an issue if this memory region
		 * corresponds to a read-sensitive peripheral.
		 */
		desc |= XLAT_GET_PXN_DESC();

	} else { /* Normal memory */
		/*
		 * Always map read-write normal memory as execute-never.
		 * This library assumes that it is used by software that does
		 * not self-modify its code, therefore R/W memory is reserved
		 * for data storage, which must not be executable.
		 *
		 * Note that setting the XN bit here is for consistency only.
		 * The function that enables the MMU sets the SCTLR_ELx.WXN bit,
		 * which makes any writable memory region to be treated as
		 * execute-never, regardless of the value of the XN bit in the
		 * translation table.
		 *
		 * For read-only memory, rely on the MT_EXECUTE/MT_EXECUTE_NEVER
		 * attribute to figure out the value of the PXN bit.  The actual
		 * XN bit(s) to set in the descriptor depends on the context's
		 * translation regime and the policy applied in
		 * XLAT_GET_PXN_DESC().
		 */

		/* Only MT_MEMORY allowed from here on */
		assert(mem_type == MT_MEMORY);

		if (((attr & MT_RW) != 0UL) || ((attr & MT_EXECUTE_NEVER) != 0UL)) {
			desc |= XLAT_GET_PXN_DESC();
		} else {
			/* Set GP bit for block and page code entries for BTI */
			desc |= XLAT_GET_GP_DESC();
		}

		desc |= LOWER_ATTRS(ATTR_IWBWA_OWBWA_NTR_INDEX);

		if (lpa2_enabled == false) {
			/* Configure Inner Shareability */
			desc |= INPLACE(LOWER_ATTR_SH, ISH);
		}
	}

	return desc;
}

int xlat_init_tables_ctx(struct xlat_ctx *ctx)
{
	struct xlat_ctx_cfg *ctx_cfg;
	struct xlat_ctx_tbls *ctx_tbls;

	ctx_cfg = ctx->cfg;
	ctx_tbls = ctx->tbls;

	xlat_mmap_print(ctx);

	/*
	 * All tables must be zeroed/initialized before mapping any region
	 * as they are allocated outside the .bss area.
	 * For this initialization, ignore the level and assume that all
	 * tables are of the same size.
	 */
	for (unsigned int j = 0; j < ctx_tbls->tables_num; j++) {
		for (unsigned int i = 0U; i < XLAT_TABLE_ENTRIES; i++) {
			ctx_tbls->tables[(j * XLAT_TABLE_ENTRIES) + i] =
								INVALID_DESC;
		}
	}

	/*
	 * Use the first table as table base and setup the
	 * next available table.
	 */
	ctx_tbls->next_table++;
	for (unsigned int i = 0U; i < ctx->cfg->mmap_regions; i++) {
		uintptr_t end_va = xlat_tables_map_region(ctx,
						&ctx_cfg->mmap[i], 0U,
						ctx_tbls->tables,
						XLAT_GET_TABLE_ENTRIES(ctx_cfg->base_level),
						ctx_cfg->base_level);
		if (end_va != (ctx_cfg->mmap[i].base_va +
					ctx_cfg->mmap[i].size - 1UL)) {
			ERROR("%s (%u): Not enough memory to map region: "
			      " VA:0x%lx  PA:0x%lx  size:0x%zx  attr:0x%lx\n",
			      __func__, __LINE__, ctx_cfg->mmap[i].base_va,
						  ctx_cfg->mmap[i].base_pa,
						  ctx_cfg->mmap[i].size,
						  ctx_cfg->mmap[i].attr);
			return -ENOMEM;
		}
	}

	/* Inv the cache as a good measure */
	if (!is_mmu_enabled()) {
		inv_dcache_range((uintptr_t)(void *)ctx_tbls->tables,
				 sizeof(uint64_t) * (unsigned long)ctx_tbls->tables_num
							* XLAT_TABLE_ENTRIES);
	}
	ctx_tbls->initialized = true;

	if (!is_mmu_enabled()) {
		inv_dcache_range((uintptr_t)(void *)ctx_tbls,
				   sizeof(struct xlat_ctx_tbls));
	}
	xlat_tables_print(ctx);

	return 0;
}
