/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 * SPDX-FileCopyrightText: Copyright Arm Limited and Contributors.
 */

/* This file is derived from xlat_table_v2 library in TF-A project */

#include <arch_features.h>
#include <arch_helpers.h>
#include <debug.h>
#include <errno.h>
#include <limits.h>
#include <stdbool.h>
#include <stdint.h>
#include <string.h>
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
	return ctx->tbls->tables[ctx->tbls->next_table++];
}

/*
 * Function that returns the index of the first table affected by the VA on
 * the specified mmap region.
 */
static uintptr_t xlat_tables_find_start_va(struct xlat_mmap_region *mm,
					   const uintptr_t table_base_va,
					   const unsigned int level)
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
						    const unsigned int level)
{
	return (unsigned int)((va - table_base_va) >> XLAT_ADDR_SHIFT(level));
}

/*
 * From the given arguments, it decides which action to take when mapping the
 * specified region.
 */
static action_t xlat_tables_map_region_action(const struct xlat_mmap_region *mm,
			unsigned int desc_type, uintptr_t dest_pa,
			uintptr_t table_entry_base_va, unsigned int level)
{
	uintptr_t mm_end_va = mm->base_va + mm->size - 1UL;
	uintptr_t table_entry_end_va =
			table_entry_base_va + XLAT_BLOCK_SIZE(level) - 1UL;

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

		if (level == 3U) {
			/*
			 * Last level, only page descriptors are allowed.
			 */
			if (desc_type == PAGE_DESC) {
				/*
				 * There's another region mapped here, don't
				 * overwrite.
				 */
				return ACTION_NONE;
			} else {
				if (desc_type != INVALID_DESC) {
					ERROR("%s (%u): Expected invalid descriptor\n",
						__func__, __LINE__);
					panic();
				}
				return ACTION_WRITE_BLOCK_ENTRY;
			}

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
				    || (level < MIN_LVL_BLOCK_DESC) ||
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
		if (level >= 3U) {
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
static uintptr_t xlat_tables_map_region(struct xlat_ctx *ctx,
					struct xlat_mmap_region *mm,
					uintptr_t table_base_va,
					uintptr_t *const table_base,
					unsigned int table_entries,
					unsigned int level)
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

	mm_end_va = mm->base_va + mm->size - 1U;

	if ((level < ctx_cfg->base_level) || (level > XLAT_TABLE_LEVEL_MAX)) {
		ERROR("%s (%u): Level out of boundaries (%u)\n",
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
			/* FIXME: This violates misra-c2012-17.2 */
			end_va = xlat_tables_map_region(ctx, mm, table_idx_va,
					       subtable, XLAT_TABLE_ENTRIES,
					       level + 1U);
			if (end_va !=
				(table_idx_va + XLAT_BLOCK_SIZE(level) - 1UL)) {
				return end_va;
			}

		} else if (action == ACTION_RECURSE_INTO_TABLE) {
			uintptr_t end_va;

			subtable = (uint64_t *)(void *)(desc & TABLE_ADDR_MASK);
			/* Recurse to write into subtable */
			/* FIXME: This violates misra-c2012-17.2 */
			end_va = xlat_tables_map_region(ctx, mm, table_idx_va,
					       subtable, XLAT_TABLE_ENTRIES,
					       level + 1U);
			if (end_va !=
				(table_idx_va + XLAT_BLOCK_SIZE(level) - 1UL)) {
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
 * Function that verifies that a region can be mapped.
 * Returns:
 *        0: Success, the mapping is allowed.
 *   EINVAL: Invalid values were used as arguments.
 *   ERANGE: The memory limits were surpassed.
 *   ENOMEM: There is not enough memory in the mmap array.
 *    EPERM: Region overlaps another one in an invalid way.
 * EALREADY: The context configuration is already marked as initialized.
 */
static int mmap_add_region_check(const struct xlat_ctx *ctx,
				 const struct xlat_mmap_region *mm)
{
	uintptr_t base_pa = mm->base_pa;
	uintptr_t base_va = mm->base_va;
	size_t size = mm->size;
	size_t granularity = mm->granularity;
	uintptr_t end_pa = base_pa + size - 1UL;
	uintptr_t end_va = base_va + size - 1UL;
	unsigned int index;
	struct xlat_ctx_cfg *ctx_cfg = ctx->cfg;

	if (!IS_PAGE_ALIGNED(base_pa) || !IS_PAGE_ALIGNED(base_va) ||
			!IS_PAGE_ALIGNED(size)) {
		return -EFAULT;
	}

	if ((granularity != XLAT_BLOCK_SIZE(1U)) &&
	    (granularity != XLAT_BLOCK_SIZE(2U)) &&
	    (granularity != XLAT_BLOCK_SIZE(3U))) {
		return -EINVAL;
	}

	/* Check for overflows */
	if ((base_pa > end_pa) || (base_va > end_va)) {
		return -ERANGE;
	}

	/*
	 * end_va is calculated as an offset with regards to the base address
	 * for the current context, so compare it against max_va_size to ensure
	 * we are within the allowed range.
	 */
	if (end_va > ctx_cfg->max_va_size) {
		return -ERANGE;
	}

	if (end_pa > xlat_arch_get_max_supported_pa()) {
		return -ERANGE;
	}

	/* Check that there is space in the ctx->mmap array */
	if (ctx_cfg->mmap[ctx_cfg->mmap_num - 1U].size != 0UL) {
		return -ENOMEM;
	}

	/* Check for PAs and VAs overlaps with all other regions in this context */
	index = 0U;
	while ((index < ctx_cfg->mmap_num) &&
	       (ctx_cfg->mmap[index].size != 0UL)) {
		uintptr_t mm_cursor_end_va = ctx_cfg->mmap[index].base_va +
					     ctx_cfg->mmap[index].size - 1UL;

		unsigned long long mm_cursor_end_pa =
				ctx_cfg->mmap[index].base_pa
				+ ctx_cfg->mmap[index].size - 1UL;

		bool separated_pa = (end_pa < ctx_cfg->mmap[index].base_pa) ||
						(base_pa > mm_cursor_end_pa);
		bool separated_va = (end_va < ctx_cfg->mmap[index].base_va) ||
						(base_va > mm_cursor_end_va);

		if (!separated_va || !separated_pa) {
			return -EPERM;
		}
		++index;
	}

	return 0;
}

/*
 * Returns a block/page table descriptor for the given level and attributes.
 */
uint64_t xlat_desc(uint64_t attr, uintptr_t addr_pa, unsigned int level)
{
	uint64_t desc;
	uint32_t mem_type;

	if ((MT_TYPE(attr) == MT_TRANSIENT)) {
		/* Transient entry requested. */
		desc = 0ULL;
		return desc;
	}

	/* Make sure that the granularity is fine enough to map this address. */
	if ((addr_pa & XLAT_BLOCK_MASK(level)) != 0U) {
		ERROR("%s (%u): 0x%lx has incorrect granularity\n",
			__func__, __LINE__, addr_pa);
	}

	desc = addr_pa;
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

	if ((attr & MT_CONT) != 0UL) {
		desc |= XLAT_GET_CONT_HINT();
	}

	if ((attr & MT_NG) != 0UL) {
		desc |= XLAT_GET_NG_HINT();
	}

	/*
	 * Mark this area as non-executable for unpriviledged exception levels.
	 */
	desc |= XLAT_GET_UXN_DESC();

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
		desc |= LOWER_ATTRS(ATTR_DEVICE_INDEX | OSH);
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
		uint32_t shareability_type;

		if (((attr & MT_RW) != 0UL) || ((attr & MT_EXECUTE_NEVER) != 0UL)) {
			desc |= XLAT_GET_PXN_DESC();
		}

		shareability_type = MT_SHAREABILITY(attr);
		if (mem_type == MT_MEMORY) {
			desc |= LOWER_ATTRS(ATTR_IWBWA_OWBWA_NTR_INDEX);
			if (shareability_type == MT_SHAREABILITY_NSH) {
				desc |= LOWER_ATTRS(NSH);
			} else if (shareability_type == MT_SHAREABILITY_OSH) {
				desc |= LOWER_ATTRS(OSH);
			} else {
				desc |= LOWER_ATTRS(ISH);
			}

			/* Check if Branch Target Identification is enabled */
			/* TODO: This is needed if BTI is enabled. Double check this code. */
			/* Set GP bit for block and page code entries
			 * if BTI mechanism is implemented.
			 */
		} else {
			if (mem_type != MT_NON_CACHEABLE) {
				/* Only non cacheable memory at this point */
				panic();
			}
			desc |= LOWER_ATTRS(ATTR_NON_CACHEABLE_INDEX | OSH);
		}
	}

	return desc;
}

/*****************************************************************************
 * Public part of the core translation library.
 ****************************************************************************/

/*
 * Add a memory region with defined base PA and base VA. This function can only
 * be used before marking the xlat_ctx_cfg for the current xlat_ctx as
 * initialized.
 *
 * The region cannot be removed once added.
 *
 * This function returns 0 on success or an error code otherwise.
 */
int xlat_mmap_add_region_ctx(struct xlat_ctx *ctx,
			     struct xlat_mmap_region *mm)
{
	unsigned int mm_last_idx = 0U;
	unsigned int mm_cursor_idx = 0U;
	uintptr_t end_pa;
	uintptr_t end_va;
	struct xlat_ctx_cfg *ctx_cfg;
	struct xlat_ctx_tbls *ctx_tbls;
	int ret;

	if (ctx == NULL) {
		return -EINVAL;
	}

	ctx_cfg = ctx->cfg;
	ctx_tbls = ctx->tbls;

	if (ctx_cfg == NULL || ctx_tbls == NULL) {
		return -EINVAL;
	}

	if (mm == NULL) {
		return -EINVAL;
	}

	/* The context data cannot be initialized */
	if (xlat_ctx_cfg_initialized(ctx) == true) {
		return -EINVAL;
	}

	/* Memory regions must be added before initializing the xlat tables. */
	assert(ctx_tbls->initialized == false);

	/* Ignore empty regions */
	if (mm->size == 0UL) {
		return 0;
	}

	if (ctx_cfg->region == VA_LOW_REGION) {
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
		ctx_cfg->base_va = 0ULL;

		if ((mm->base_va & HIGH_REGION_MASK) ||
		     ((mm->base_va + mm->size) & HIGH_REGION_MASK)) {
			ERROR("%s (%u): Base VA and address space do not match: ",
							__func__, __LINE__);
			ERROR("Base va = 0x%lx, Address space = Low region\n",
				mm->base_va);
			return -EINVAL;
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
		ctx_cfg->base_va = (ULONG_MAX - ctx_cfg->max_va_size + 1ULL);

		if (mm->base_va < ctx_cfg->base_va) {
			ERROR("%s (%u): Base VA is not aligned with the high region start: ",
							__func__, __LINE__);
			ERROR("Base VA = 0x%lx, high region start VA = 0x%lx\n",
				mm->base_va, ctx_cfg->base_va);
			return -EINVAL;
		}

		/*
		 * If this context is handling the high half region of the VA,
		 * adjust the start address of this area by substracting the
		 * start address of the region as the table entries are
		 * relative to the latter. Once ttbr1_el2 is configured, the
		 * MMU will translate the addresses properly.
		 */
		mm->base_va -= ctx_cfg->base_va;
	}

	end_pa = mm->base_pa + mm->size - 1UL;
	end_va = mm->base_va + mm->size - 1UL;

	ret = mmap_add_region_check(ctx, mm);
	if (ret != 0) {
		ERROR("%s (%u): mmap_add_region_check() failed. error %d\n",
					__func__, __LINE__, ret);
		return ret;
	}

	/*
	 * Find correct place in mmap to insert new region.
	 * Overlapping is not allowed.
	 */
	while (((ctx_cfg->mmap[mm_cursor_idx].base_va) < mm->base_va)
	       && (ctx_cfg->mmap[mm_cursor_idx].size != 0UL)
	       && (mm_cursor_idx < ctx_cfg->mmap_num)) {
		++mm_cursor_idx;
	}

	/*
	 * Find the last entry marker in the mmap
	 */
	while ((mm_last_idx < ctx_cfg->mmap_num) &&
	       (ctx_cfg->mmap[mm_last_idx].size != 0UL)) {
		++mm_last_idx;
	}

	/*
	 * Check if we have enough space in the memory mapping table.
	 * This shouldn't happen as we have checked in mmap_add_region_check
	 * that there is free space.
	 */
	assert(ctx_cfg->mmap[mm_last_idx].size == 0UL);

	/*
	 * Make room for new region by moving other regions up by one place.
	 */
	(void)memmove((void *)(&ctx_cfg->mmap[mm_cursor_idx + 1U]),
		      (void *)(&ctx_cfg->mmap[mm_cursor_idx]),
		      sizeof(struct xlat_mmap_region) *
						(mm_last_idx - mm_cursor_idx));

	/* Store the memory mapping information into the context. */
	(void)memcpy((void *)(&ctx_cfg->mmap[mm_cursor_idx]), (void *)mm,
						sizeof(struct xlat_mmap_region));

	if (end_pa > ctx_cfg->max_mapped_pa) {
		ctx_cfg->max_mapped_pa = end_pa;
	}

	if (end_va > ctx_cfg->max_mapped_va_offset) {
		ctx_cfg->max_mapped_va_offset = end_va;
	}

	return 0;
}

/*
 * Add an array of memory regions with defined base PA and base VA.
 * This function needs to be called before initialiting the xlat_ctx_cfg.
 * Setting the `last` argument to true will initialise the xlat_ctx_cfg.
 *
 * The regions cannot be removed once added.
 *
 * Return 0 on success or a negative error code otherwise.
 */
int xlat_mmap_add_ctx(struct xlat_ctx *ctx,
		      struct xlat_mmap_region *mm,
		      bool last)
{
	if ((ctx == NULL) || (mm == NULL)) {
		return -EINVAL;
	}

	struct xlat_mmap_region *mm_cursor = mm;

	while (mm_cursor->size != 0UL) {
		int retval;

		retval = xlat_mmap_add_region_ctx(ctx, mm_cursor);
		if (retval != 0) {
			/*
			 * In case of error, stop an return.
			 * Note, the context might be in an invalid
			 * state and it will need to be restarted.
			 */
			return retval;
		}
		mm_cursor++;
	}

	if (last) {
		/*
		 * Mark the configuration part of the context as initialized.
		 * From this point on, no more memory mapping areas can be
		 * added to this context (or any other sharing the same
		 * configuration).
		 */
		ctx->cfg->initialized = true;
		flush_dcache_range((uintptr_t)(void *)ctx->cfg,
				   sizeof(struct xlat_ctx_cfg));

	}

#if LOG_LEVEL >= LOG_LEVEL_VERBOSE
	VERBOSE("Runtime mapings");
	if (ctx->cfg->region == VA_LOW_REGION) {
		VERBOSE("(Low Region):\n");
	} else {
		VERBOSE("(High Region):\n");
	}

	for (unsigned int i = 0U; i < ctx->cfg->mmap_num; i++) {
		VERBOSE("\tRegion: 0x%lx - 0x%lx has attributes 0x%lx\n",
			ctx->cfg->mmap[i].base_va,
			ctx->cfg->mmap[i].base_va + ctx->cfg->mmap[i].size - 1U,
			ctx->cfg->mmap[i].attr);
	}
#endif /* LOG_LEVEL_VERBOSE */

	return 0;
}

/*
 * Initialize translation tables (and mark xlat_ctx_cfg as initialized if
 * not already initialized) associated to the current context.
 *
 * The struct xlat_ctx_cfg of the context might be shared with other
 * contexts that might have already initialized it. This is expected and
 * should not cause any problem.
 *
 * This function assumes that the xlat_ctx_cfg field of the context has been
 * properly configured by previous calls to xlat_mmap_add_region_ctx().
 *
 * This function returns 0 on success or an error code otherwise.
 */
int xlat_init_tables_ctx(struct xlat_ctx *ctx)
{
	struct xlat_ctx_cfg *ctx_cfg;
	struct xlat_ctx_tbls *ctx_tbls;
	unsigned int index;

	if (ctx == NULL) {
		return -EINVAL;
	}

	ctx_cfg = ctx->cfg;
	ctx_tbls = ctx->tbls;

	if (ctx_cfg == NULL || ctx_tbls == NULL) {
		return -EINVAL;
	}

	if (xlat_ctx_tbls_initialized(ctx)) {
		VERBOSE("%s (%u): Translation tables already initialized\n",
					__func__, __LINE__);
		return -EALREADY;
	}

	if (!xlat_ctx_cfg_initialized(ctx)) {
		VERBOSE("%s (%u): Translation context configuration not initialized\n",
					__func__, __LINE__);
		return -EINVAL;
	}

	if (is_mmu_enabled() == true) {
		ERROR("%s (%u): MMU is already enabled\n", __func__, __LINE__);
		return -EINVAL;
	}

	xlat_mmap_print(ctx);

	/*
	 * All tables must be zeroed/initialized before mapping any region
	 * as they are allocated outside the .bss area.
	 */
	for (unsigned int i = 0U; i < XLAT_TABLE_ENTRIES; i++) {
		ctx_tbls->base_table[i] = INVALID_DESC;
	}

	for (unsigned int j = 0; j < ctx_tbls->tables_num; j++) {
		for (unsigned int i = 0U; i < XLAT_TABLE_ENTRIES; i++) {
			ctx_tbls->tables[j][i] = INVALID_DESC;
		}
	}

	index = 0U;
	while ((index < ctx_cfg->mmap_num) &&
	       (ctx_cfg->mmap[index].size != 0UL)) {
		uintptr_t end_va = xlat_tables_map_region(ctx,
						&ctx_cfg->mmap[index],
						0U,
						ctx_tbls->base_table,
						ctx_tbls->max_base_table_entries,
						ctx_cfg->base_level);
		if (end_va != (ctx_cfg->mmap[index].base_va +
					ctx_cfg->mmap[index].size - 1UL)) {
			ERROR("%s (%u): Not enough memory to map region: "
			      " VA:0x%lx  PA:0x%lx  size:0x%zx  attr:0x%lx\n",
			      __func__, __LINE__, ctx_cfg->mmap[index].base_va,
						  ctx_cfg->mmap[index].base_pa,
						  ctx_cfg->mmap[index].size,
						  ctx_cfg->mmap[index].attr);
			return -ENOMEM;
		}

		++index;
	}

	/* Flush the cache as a good measure */
	flush_dcache_range((uintptr_t)(void *)ctx_tbls->base_table,
			 sizeof(uint64_t) * XLAT_TABLE_ENTRIES);
	flush_dcache_range((uintptr_t)(void *)ctx_tbls->tables,
			 sizeof(uint64_t) * (unsigned long)ctx_tbls->tables_num
						* XLAT_TABLE_ENTRIES);

	ctx_tbls->initialized = true;

	flush_dcache_range((uintptr_t)(void *)ctx_tbls,
			   sizeof(struct xlat_ctx_tbls));
	flush_dcache_range((uintptr_t)(void *)ctx, sizeof(struct xlat_ctx));

	xlat_tables_print(ctx);

	return 0;
}

/*
 * Initialize a context dynamically at runtime using the given xlat_ctx_cfg
 * and xlat_ctx_tbls structures.
 *
 * Return 0 if success or a Posix erro code otherwise.
 */
int xlat_ctx_create_dynamic(struct xlat_ctx *ctx,
			    struct xlat_ctx_cfg *cfg,
			    struct xlat_ctx_tbls *tbls,
			    void *base_tables,
			    unsigned int base_level_entries,
			    void *tables_ptr,
			    unsigned int ntables)
{
	if (ctx == NULL) {
		return -EINVAL;
	}

	if (XLAT_TABLES_CTX_CFG_VALID(ctx) &&
	    XLAT_TABLES_CTX_TBL_VALID(ctx)) {
		return -EALREADY;
	}

	/* Add the configuration to the context */
	XLAT_SETUP_CTX_CFG(ctx, cfg);

	/* Initialize the tables structure */
	XLAT_INIT_CTX_TBLS(tbls, tables_ptr, ntables,
			   base_tables, base_level_entries);

	/* Add the tables to the context */
	XLAT_SETUP_CTX_TBLS(ctx, tbls);

	return 0;
}

/*
 * Returns true if the context is already initialized and false otherwise.
 * This function only takes into account whether xlat_ctx_cfg is initialized.
 */
bool xlat_ctx_cfg_initialized(const struct xlat_ctx * const ctx)
{
	assert(ctx != NULL);
	assert(ctx->cfg != NULL);
	return ctx->cfg->initialized;
}

/*
 * Returns true if the translation tables on the current context are already
 * initialized or false otherwise.
 */
bool xlat_ctx_tbls_initialized(const struct xlat_ctx * const ctx)
{
	assert(ctx != NULL);
	assert(ctx->tbls != NULL);
	return ctx->tbls->initialized;
}
