/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 * SPDX-FileCopyrightText: Copyright Arm Limited and Contributors.
 */

/* This file is derived from xlat_table_v2 library in TF-A project */

#include <arch_helpers.h>
#include <assert.h>
#include <debug.h>
#include <errno.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <utils_def.h>
#include <xlat_cmn_arch.h>
#include <xlat_contexts.h>
#include "xlat_defs_private.h"
#include <xlat_tables.h>
#include "xlat_tables_private.h"

#if LOG_LEVEL < LOG_LEVEL_VERBOSE

void xlat_mmap_print(const struct xlat_ctx *ctx)
{
	(void)ctx;

	/* Empty */
}

void xlat_tables_print(struct xlat_ctx *ctx)
{
	(void)ctx;

	/* Empty */
}

#else /* if LOG_LEVEL >= LOG_LEVEL_VERBOSE */

void xlat_mmap_print(const struct xlat_ctx *ctx)
{
	VERBOSE("mmap:\n");

	for (unsigned int i = 0U; i < ctx->cfg.mmap_regions; i++) {
		uintptr_t base_va;

		base_va = ((ctx->cfg.region == VA_LOW_REGION) ?
				ctx->cfg.mmap[i].base_va :
				(ctx->cfg.mmap[i].base_va
					+ ctx->cfg.base_va));
		if (MT_TYPE(ctx->cfg.mmap[i].attr) != MT_TRANSIENT) {
			VERBOSE(" VA:0x%lx  PA:0x%lx  size:0x%zx  attr:0x%lx  granularity:0x%zx\n",
			       base_va, ctx->cfg.mmap[i].base_pa,
			       ctx->cfg.mmap[i].size, ctx->cfg.mmap[i].attr,
			       ctx->cfg.mmap[i].granularity);
		} else {
			VERBOSE(" VA:0x%lx  PA: TRANSIENT  size:0x%zx  granularity:0x%zx\n",
			       base_va, ctx->cfg.mmap[i].size,
			       ctx->cfg.mmap[i].granularity);
		}
	};
	VERBOSE("\n");
}

/* Print the attributes of the specified block descriptor. */
static void xlat_desc_print(uint64_t desc)
{
	uint64_t mem_type_index = ATTR_INDEX_GET(desc);

	if (mem_type_index == ATTR_IWBWA_OWBWA_NTR_INDEX) {
		VERBOSE("MEM");
	} else {
		if (mem_type_index != ATTR_DEVICE_INDEX) {
			/* Unsupported memory type */
			panic();
		}
		VERBOSE("DEV");
	}

	VERBOSE(((desc & LOWER_ATTRS(AP_RO)) != 0ULL) ? "-RO" : "-RW");
	VERBOSE(((desc & UPPER_ATTRS(PXN)) != 0ULL) ? "-PXN" : "-PEXEC");
	VERBOSE(((desc & UPPER_ATTRS(XN)) != 0ULL) ? "-XN" : "-EXEC");

	if ((desc & LOWER_ATTRS(NS)) == 0ULL) {
		VERBOSE("-RL");
	} else {
		VERBOSE("-N");
	}

	/* Check Guarded Page bit */
	if ((desc & UPPER_ATTRS(GP)) != 0ULL) {
		VERBOSE("-GP");
	}
}

static const char * const level_spacers[] = {
	"[LV-1] ",
	"  [LV0] ",
	"    [LV1] ",
	"      [LV2] ",
	"        [LV3] "
};

static char *invalid_descriptors_ommited =
		"%s(%d invalid descriptors omitted)\n";

static char *tr_invalid_descriptors_ommited =
		"%s(%d transient invalid descriptors omitted)\n";

/*
 * Recursive function that reads the translation tables passed as an argument
 * and prints their status.
 */
static void xlat_tables_print_internal(struct xlat_ctx *ctx,
				       uintptr_t table_base_va,
				       const uint64_t *table_base,
				       int level)
{
	uint64_t *addr_inner;
	unsigned int multiple_row_count;
	unsigned int table_idx = 0U;
	bool is_invalid, is_transient_inv;
	uint64_t prev_desc;
	size_t level_size;
	uintptr_t table_idx_va;
	char *str = NULL;

	if (level > XLAT_TABLE_LEVEL_MAX) {
		/* Level out of bounds */
		panic();
	}

	assert(ctx != NULL);

	level_size = XLAT_BLOCK_SIZE(level);
	table_idx_va = table_base_va + ctx->cfg.base_va;

	/*
	 * Keep track of how many invalid or transient descriptors are counted
	 * in a row. Whenever multiple invalid descriptors are found, only the
	 * first one is printed, and a line is added to inform about how many
	 * descriptors have been omitted.
	 */
	multiple_row_count = 0U;
	prev_desc = 0ULL;

	while (table_idx < XLAT_GET_TABLE_ENTRIES(level)) {
		uint64_t desc;

		desc = table_base[table_idx];

		is_transient_inv = (desc == TRANSIENT_DESC);
		is_invalid = (desc == INVALID_DESC);

		if ((is_invalid == true) || (is_transient_inv == true)) {
			if (multiple_row_count == 0U) {
				prev_desc = desc;
				VERBOSE("%sVA:0x%lx size:0x%zx\n",
					level_spacers[level + 1],
					table_idx_va, level_size);


				if (is_invalid == true) {
					str = invalid_descriptors_ommited;
				} else {
					str = tr_invalid_descriptors_ommited;
				}
			}
			multiple_row_count++;

		} else {
			if ((multiple_row_count > 0U) && (prev_desc != desc)) {
				VERBOSE(str, level_spacers[level + 1],
					multiple_row_count - 1U);
				multiple_row_count = 0U;
			}

			/*
			 * Check if this is a table or a block. Tables are only
			 * allowed in levels other than 3, but DESC_PAGE has the
			 * same value as DESC_TABLE, so we need to check.
			 */
			if (((desc & DESC_MASK) == TABLE_DESC) &&
					(level < XLAT_TABLE_LEVEL_MAX)) {
				/*
				 * Do not print any PA for a table descriptor,
				 * as it doesn't directly map physical memory
				 * but instead points to the next translation
				 * table in the translation table walk.
				 */
				VERBOSE("%sVA:0x%lx size:0x%zx\n",
				       level_spacers[level + 1],
				       table_idx_va, level_size);

				addr_inner =
					(uint64_t *)(void *)xlat_get_oa_from_tte(desc);

				/* FIXME: Recursion. */
				xlat_tables_print_internal(ctx, table_idx_va,
					addr_inner, level + 1U);
			} else {
				VERBOSE("%sVA:0x%lx PA:0x%lx size:0x%zx ",
				       level_spacers[level + 1], table_idx_va,
				       (uint64_t)xlat_get_oa_from_tte(desc),
				       level_size);
				xlat_desc_print(desc);
				if (desc & TRANSIENT_DESC) {
					VERBOSE("[TRANSIENT]");
				}
				VERBOSE("\n");
			}
		}

		table_idx++;
		table_idx_va += level_size;
	}

	if (multiple_row_count > 1U) {
		VERBOSE(str, level_spacers[level + 1],
						multiple_row_count - 1U);
	}
}

void xlat_tables_print(struct xlat_ctx *ctx)
{
	unsigned int used_page_tables;
	struct xlat_ctx_cfg *ctx_cfg = &ctx->cfg;

	assert(ctx_cfg != NULL);

	uintptr_t max_mapped_va_offset =
			(ctx_cfg->max_mapped_va_offset + ctx_cfg->base_va);
	uintptr_t max_allowed_va =
			(ctx_cfg->max_va_size + ctx_cfg->base_va - 1ULL);


	VERBOSE("Translation tables state for %s VA region:\n",
		(ctx_cfg->region == VA_LOW_REGION) ? "Low" : "High");
	VERBOSE("  Max allowed PA:  0x%lx\n", xlat_arch_get_max_supported_pa());
	VERBOSE("  Max allowed VA:  0x%lx\n", max_allowed_va);
	VERBOSE("  Max mapped PA:   0x%lx", ctx_cfg->max_mapped_pa);
	for (unsigned int i = 0U; i < ctx->cfg.mmap_regions; i++) {
		if (ctx_cfg->mmap[i].attr == MT_TRANSIENT) {
			/*
			 * If there is a transient region on this context, we
			 * do not know what will be the highest PA, so print a
			 * note on the log.
			 */
			VERBOSE(" - Estimated (transient region)");
			break;
		}
	}
	VERBOSE("\n");
	VERBOSE("  Max mapped VA:   0x%lx\n", max_mapped_va_offset);

	VERBOSE("  Initial lookup level: %i\n", ctx_cfg->base_level);

	used_page_tables = ctx->tbls.next_table;
	VERBOSE("  Used %d tables out of %d (spare: %d)\n",
				used_page_tables, ctx->tbls.tables_num,
				ctx->tbls.tables_num - used_page_tables);

	xlat_tables_print_internal(ctx, 0U, ctx->tbls.tables,
				   ctx_cfg->base_level);
}

#endif /* LOG_LEVEL >= LOG_LEVEL_VERBOSE */

/*
 * Do a translation table walk to find the last level table that maps
 * va with regards to the context va_base.
 *
 * On success, return the address of the last level table within the
 * translation table. Its lookup level is stored in '*out_level' and
 * the base VA applicable to the table is returned through '*tt_base_va'.
 *
 * On error, or if the VA is outside the VA space for the context,
 * return NULL.
 */
static uint64_t *find_xlat_last_table(uintptr_t va,
				      const struct xlat_ctx * const ctx,
				      int * const out_level,
				      uintptr_t * const tt_base_va)
{
	uintptr_t va_offset;
	int start_level;
	uint64_t *ret_table;
	const struct xlat_ctx_tbls *ctx_tbls __unused;
	const struct xlat_ctx_cfg *ctx_cfg;
	uintptr_t table_base_va;

	assert(ctx != NULL);
	assert(out_level != NULL);
	assert(tt_base_va != NULL);
	bool mmu_en __unused = is_mmu_enabled();

	if (va < ctx->cfg.base_va) {
		return NULL;
	}

	/* Extract the base_va from the given VA */
	va_offset = va - ctx->cfg.base_va;
	va_offset &= ~PAGE_SIZE_MASK; /* Page address of the VA address passed. */

	if (va_offset >= ctx->cfg.max_va_size) {
		return NULL;
	}

	ctx_tbls = &ctx->tbls;
	ctx_cfg = &ctx->cfg;
	start_level = ctx_cfg->base_level;
	ret_table = remap_table_address(ctx->tbls.tables, ctx_tbls->tbls_va_to_pa_diff, mmu_en);
	table_base_va = ctx_cfg->base_va;

	for (int level = start_level;
	     level <= XLAT_TABLE_LEVEL_MAX; level++) {
		unsigned int idx = XLAT_TABLE_IDX(va_offset, level);
		uint64_t desc = ret_table[idx];
		uint64_t desc_type = desc & DESC_MASK;

		if ((desc_type != TABLE_DESC) ||
		    (level == XLAT_TABLE_LEVEL_MAX)) {
			*out_level = level;
			*tt_base_va = table_base_va;
			return ret_table;
		}

		/* Get the base address mapped by the next table */
		table_base_va += (XLAT_BLOCK_SIZE(level) * idx);

		/* Get the next table */
		ret_table = remap_table_address(xlat_get_oa_from_tte(desc),
					ctx_tbls->tbls_va_to_pa_diff, mmu_en);
	}

	/*
	 * This shouldn't be reached, the translation table walk should end at
	 * most at level XLAT_TABLE_LEVEL_MAX and return from inside the loop
	 * but we need this to avoid MISRA problems.
	 */
	return NULL;
}

/* Check if we need to create tables at the given level */
static bool need_tables_at_lvl(const struct xlat_mmap_region *region,
		uint64_t parent_lvl_blk_sz)
{
	return ((region->granularity < parent_lvl_blk_sz) ||
		!ALIGNED(region->base_va, parent_lvl_blk_sz) ||
		!ALIGNED(region->base_va + region->size, parent_lvl_blk_sz) ||
		((MT_TYPE(region->attr) != MT_TRANSIENT) &&
			!ALIGNED(region->base_pa, parent_lvl_blk_sz)));
}

/*
 * Estimate the number of L3 and L2 tables needed for the given memory regions.
 * This function assumes that the regions are sorted by ascending base_va.
 * It also assumes that the regions are at least aligned to PAGE_SIZE
 * and do not overlap.
 */
unsigned long xlat_estimate_num_l3_l2_tables(
	const struct xlat_mmap_region *regions,
	unsigned int region_count)
{
	unsigned long total_l3_tables = 0UL;
	unsigned long total_l2_tables = 0UL;
	uint64_t l3_tbl_sz = XLAT_BLOCK_SIZE(2);
	uint64_t l2_tbl_sz = XLAT_BLOCK_SIZE(1);

	uint64_t last_l3_va_end = 0UL;
	uint64_t last_l2_va_end = 0UL;
	unsigned int i;
	uint64_t region_va, region_size;
	uint64_t l3_start, l3_end;
	unsigned long l3_tables = 0UL;
	uint64_t l2_start, l2_end;
	unsigned long l2_tables = 0UL;

	for (i = 0U; i < region_count; ++i) {
		region_va = regions[i].base_va;
		region_size = regions[i].size;
		VERBOSE("Region %u: VA=0x%lx, size=0x%lx, granularity=0x%lx\n",
			i, region_va, region_size, regions[i].granularity);

		/* L3 tables */
		l3_start = region_va;
		l3_end = region_va + region_size;
		/* If region starts inside last L3 block, skip to next block */
		if (l3_start < last_l3_va_end) {
			l3_start = last_l3_va_end;
		}

		/* Only count L3 tables if needed */
		if ((need_tables_at_lvl(&regions[i], l3_tbl_sz) != false) &&
						(l3_start < l3_end)) {
			l3_tables = (round_up(l3_end, l3_tbl_sz) -
				round_down(l3_start, l3_tbl_sz)) / l3_tbl_sz;

			total_l3_tables += l3_tables;
			last_l3_va_end = round_up(l3_end, l3_tbl_sz);

			VERBOSE(" l3_start 0x%lx l3_end 0x%lx last_l3_va_end 0x%lx"
				" l3_tables %lu total_l3_tables %lu\n",
				l3_start, l3_end, last_l3_va_end, l3_tables,
				total_l3_tables);
		}

		/* L2 tables */
		l2_start = region_va;
		l2_end = region_va + region_size;
		/* If region starts inside last L2 block, skip to next block */
		if (l2_start < last_l2_va_end) {
			l2_start = last_l2_va_end;
		}

		/* Only count L2 tables if needed */
		if ((need_tables_at_lvl(&regions[i], l2_tbl_sz) != false) &&
							 (l2_start < l2_end)) {
			l2_tables = (round_up(l2_end, l2_tbl_sz) -
				round_down(l2_start, l2_tbl_sz)) / l2_tbl_sz;

			total_l2_tables += l2_tables;
			last_l2_va_end = round_up(l2_end, l2_tbl_sz);

			VERBOSE(" l2_start 0x%lx l2_end 0x%lx last_l2_va_end 0x%lx"
				" l2_tables %lu total_l2_tables %lu\n",
				l2_start, l2_end, last_l2_va_end,
				l2_tables, total_l2_tables);
		}
	}

	VERBOSE("Estimated L3 and L2 tables: %lu\n", total_l3_tables +
					 total_l2_tables);
	return total_l3_tables + total_l2_tables;
}

/*
 * Function to stitch L1 table from a child context into an existing L1 table
 * in the parent context.
 * The block entries in the child L1 table are copied to the corresponding
 * entries in the parent L1 table.
 * The child context tables must have been created with xlat_ctx_init() and
 * must be fully populated with the mappings for the VA range specified.
 * The VA range must be aligned to L1 block size and contained within a single
 * L1 table of the parent context.
 * This function returns 0 on success or an error code otherwise.
 */
int xlat_stitch_tables_l1(struct xlat_ctx *parent_ctx, uint64_t *child_l1,
			uintptr_t va_start, size_t va_size)
{
	int ret;
	struct xlat_llt_info parent_llt;
	unsigned int l1_idx_start, l1_idx_end;

	assert(!is_mmu_enabled());
	assert(parent_ctx != NULL);
	assert(child_l1 != NULL);

	/*
	 * Check that va_start is aligned to L1 block size and va_size is
	 * contained in the L1 table.
	 */
	assert(ALIGNED(va_start, XLAT_BLOCK_SIZE(1)));
	assert(ALIGNED(va_size, XLAT_BLOCK_SIZE(1)));
	assert((round_down(va_start, XLAT_BLOCK_SIZE(0)) + XLAT_BLOCK_SIZE(0))
						>= (va_start + va_size));

	/* Get the L1 table pointer in the parent context for va_start */
	ret = xlat_get_llt_from_va(&parent_llt, parent_ctx, va_start);
	if ((ret != 0) || (parent_llt.level != 1)) {
		ERROR("%s: xlat_get_llt_from_va() failed (%i)\n", __func__, ret);
		return ret;
	}

	assert((parent_llt.table != NULL) && (parent_llt.llt_base_va ==
				round_down(va_start, XLAT_BLOCK_SIZE(0))));

	/* Calculate the index in the L1 table for va_start */
	l1_idx_start = XLAT_TABLE_IDX(va_start, 1);
	l1_idx_end = XLAT_TABLE_IDX(va_start + va_size - 1U, 1);

	/* Copy entries from child to parent for the range */
	for (unsigned int idx = l1_idx_start; idx <= l1_idx_end; ++idx) {
		/* Assert that parent desc is a TRANSIENT desc */
		assert(parent_llt.table[idx] == TRANSIENT_DESC);
		parent_llt.table[idx] = child_l1[idx];
	}

	inv_dcache_range((uintptr_t)&parent_llt.table[l1_idx_start],
		(sizeof(uint64_t) * ((uint64_t)((l1_idx_end - l1_idx_start) + 1U))));
	return 0;
}

/*****************************************************************************
 * Public part of the utility library for translation tables.
 ****************************************************************************/

/*
 * Function to unmap a memory page for a given VA. The region to which the VA
 * belongs should have been configured as TRANSIENT during the xlat library
 * configuration.
 *
 * This function implements the "Break" part of the Break-Before-Make
 * semantics needed by the Armv8.x architecture in order to update the page
 * descriptors.
 *
 * This function returns 0 on success or an error code otherwise.
 */
int xlat_unmap_memory_page(struct xlat_llt_info * const table,
			   const uintptr_t va)
{
	uint64_t *tte;
	uint64_t desc;

	assert(table != NULL);

	tte = xlat_get_tte_ptr(table, va);

	if (tte == NULL) {
		return -EFAULT;
	}

	/* This function must only be called on valid transient descriptors */
	desc = xlat_read_tte(tte);
	if ((desc & (TRANSIENT_DESC | VALID_DESC))
					!= (TRANSIENT_DESC | VALID_DESC)) {
		return -EFAULT;
	}

	xlat_write_tte_release(tte, TRANSIENT_DESC);

	/* Invalidate any cached copy of this mapping in the TLBs. */
	XLAT_ARCH_TLBI_VA(va, nsh);

	/* Ensure completion of the invalidation. */
	XLAT_ARCH_TLBI_SYNC(nsh);

	return 0;
}

/*
 * Function to map a physical memory page from the descriptor table entry
 * and VA given. The region to which the VA belongs should have been configured
 * as TRANSIENT during the xlat library configuration.
 * This function implements the "Make" part of the
 * Break-Before-Make semantics mandated by the Armv8.x architecture in order
 * to update the page descriptors.
 *
 * This function returns 0 on success or a negative error code otherwise.
 *
 * For simplicity, this function
 *	- will not check for overlaps of the PA with other mmap regions.
 *	- will mask out the LSBs of the PA so the page/block corresponding to
 *	  the PA will actually be mapped.
 */
int xlat_map_memory_page_with_attrs(const struct xlat_llt_info * const table,
				    const uintptr_t va,
				    const uintptr_t pa,
				    const uint64_t attrs)
{
	uint64_t tte;
	uint64_t *tte_ptr;

	assert(table != NULL);

	tte_ptr = xlat_get_tte_ptr(table, va);

	if (tte_ptr == NULL) {
		return -EFAULT;
	}

	if (xlat_read_tte(tte_ptr) != TRANSIENT_DESC) {
		return -EFAULT;
	}

	/* Check that pa is within boundaries */
	if (pa > xlat_arch_get_max_supported_pa()) {
		return -EFAULT;
	}

	/* Generate the new descriptor */
	tte = xlat_desc(attrs, pa & XLAT_ADDR_MASK(table->level),
			table->level) | TRANSIENT_DESC;

	xlat_write_tte(tte_ptr, tte);

	/* Ensure the translation table write has drained into memory */
	dsb(nshst);
	isb();

	return 0;
}

/*
 * Return a xlat_llt_info structure given a context and a VA.
 * The return structure is populated on the retval field.
 *
 * If 'va' is within the boundaries of the context's VA space, this function
 * will return the last level table information, regardless of whether 'va'
 * is mapped or not.
 *
 * This function returns 0 on success or a POSIX error code otherwise.
 */
int xlat_get_llt_from_va(struct xlat_llt_info * const llt,
			 const struct xlat_ctx * const ctx,
			 const uintptr_t va)
{
	uintptr_t tt_base_va;
	uint64_t *table;
	int level;

	assert(ctx != NULL);
	assert(llt != NULL);
	assert(ctx->tbls.init);
	assert(ctx->cfg.init);

	table = find_xlat_last_table(va, ctx, &level, &tt_base_va);

	if (table == NULL) {
		WARN("Address 0x%lx outside the VA space.\n", va);
		return -EFAULT;
	}

	llt->table = table;
	llt->level = level;
	llt->llt_base_va = tt_base_va;

	return 0;
}

/*
 * This function finds the TTE on a table given the corresponding
 * xlat_llt_info structure and the VA corresponding to the entry.
 *
 * If va is outside the range for the table, it returns NULL.
 *
 * For simplicity and as long as va is applicable to the table, this function
 * will return a pointer to a tte on the table without making any asumption
 * about its type or validity. It is the caller responsibility to do any
 * necessary checks on the returned tte before using it.
 */
uint64_t *xlat_get_tte_ptr(const struct xlat_llt_info * const llt,
			   const uintptr_t va)
{
	uintptr_t offset;
	unsigned int index;

	assert(llt != NULL);

	assert(llt->level <= XLAT_TABLE_LEVEL_MAX);
	assert(llt->level >= XLAT_TABLE_LEVEL_MIN);

	if (va < llt->llt_base_va) {
		return NULL;
	}

	offset = va - llt->llt_base_va;
	index = (unsigned int)(offset >> XLAT_ADDR_SHIFT(llt->level));

	assert(llt->table != NULL);
	return (index < XLAT_GET_TABLE_ENTRIES(llt->level)) ?
			&llt->table[index] : NULL;
}

/*
 * Helper to update the descriptor on a level 3 table entry for a given
 * VA offset.
 */
static void xlat_update_level3_descriptor(uintptr_t va_offset,
					uintptr_t pa,
					uint64_t *l3_table,
					uint64_t attr)

{
	uint64_t desc;

	unsigned int l3_idx = (unsigned int)(va_offset >>
			XLAT_ADDR_SHIFT(XLAT_TABLE_LEVEL_MAX));
	assert(l3_idx < XLAT_TABLE_ENTRIES);

	/* Ensure correct mapping and unmapping sequences are followed */
	assert(/* Unmapping: */
		((MT_TYPE(attr) == MT_TRANSIENT) &&
		((l3_table[l3_idx] & (TRANSIENT_DESC | VALID_DESC)) ==
					(TRANSIENT_DESC | VALID_DESC))) ||
		/* Mapping: */
		((MT_TYPE(attr) != MT_TRANSIENT) &&
		((l3_table[l3_idx] & (TRANSIENT_DESC | VALID_DESC)) ==
					TRANSIENT_DESC)));

	/* Set VA_ALLOCATED_FLAG when mapping, clear it when unmapping */
	if (MT_TYPE(attr) == MT_TRANSIENT) {
		/* Assert that the tte is allocated */
		assert((l3_table[l3_idx] & VA_ALLOCATED_FLAG) != 0ULL);

		/* Unmapping: clear the allocated flag */
		desc = TRANSIENT_DESC;
	} else {
		/* Mapping: set the allocated flag */
		desc = xlat_desc(attr, pa, XLAT_TABLE_LEVEL_MAX)
				| TRANSIENT_DESC | VA_ALLOCATED_FLAG;
	}

	xlat_write_tte_release(&l3_table[l3_idx], desc);
}

/*
 * Helper to check if all entries in a table have VA_ALLOCATED_FLAG set.
 * Returns true if all entries are fully allocated, false otherwise.
 */
static bool is_table_fully_allocated(uint64_t *table, int level)
{
	unsigned int num_entries = XLAT_GET_TABLE_ENTRIES(level);

	for (unsigned int i = 0; i < num_entries; i++) {
		uint64_t desc = xlat_read_tte(&table[i]);

		if ((desc & TRANSIENT_DESC) == 0ULL) {
			/*
			 * Not a dynamic region. For the purpose of checking
			 * fully allocated tables, skip this entry.
			 */
			continue;
		}

		/* Check if this entry has VA_ALLOCATED_FLAG set */
		if ((desc & VA_ALLOCATED_FLAG) == 0ULL) {
			return false;
		}
		/*
		 * If we reach here, then it is TRANSIENT and Allocated.
		 * So it must be a Valid page or table descriptor.
		 */
		assert((desc & VALID_DESC) != 0UL);
	}

	return true;
}

/*
 * Helper to update parent table flags after allocation/deallocation.
 * Walks up the table hierarchy and sets/clears VA_ALLOCATED_FLAG based on
 * whether all child entries are allocated.
 */
static void update_parent_flags(struct xlat_ctx *ctx, uintptr_t va, bool allocating)
{
	assert(ctx != NULL);

	struct xlat_ctx_tbls *ctx_tbls __unused = &ctx->tbls;
	struct xlat_ctx_cfg *ctx_cfg = &ctx->cfg;
	uintptr_t va_offset = va - ctx_cfg->base_va;
	int start_level = ctx_cfg->base_level;
	bool mmu_en __unused = is_mmu_enabled();

	/* Walk from L2 up to base level to update parent flags */
	for (int level = 2; level >= start_level; level--) {
		uint64_t *table = remap_table_address(ctx->tbls.tables,
						      ctx_tbls->tbls_va_to_pa_diff, mmu_en);

		/* Walk to the table at this level */
		for (int l = start_level; l < level; l++) {
			unsigned int idx = XLAT_TABLE_IDX(va_offset, l);

			assert(idx < XLAT_GET_TABLE_ENTRIES(l));

			uint64_t desc = table[idx];

			/* Must be a valid table descriptor */
			assert((desc & DESC_MASK) == TABLE_DESC);

			table = remap_table_address(xlat_get_oa_from_tte(desc),
						   ctx_tbls->tbls_va_to_pa_diff, mmu_en);
		}

		/* Get child table to check */
		unsigned int child_idx = XLAT_TABLE_IDX(va_offset, level);
		uint64_t parent_desc = table[child_idx];

		/* Must be a valid table descriptor */
		assert((parent_desc & DESC_MASK) == TABLE_DESC);

		/* Get the child table */
		uint64_t *child_table = remap_table_address(xlat_get_oa_from_tte(parent_desc),
							   ctx_tbls->tbls_va_to_pa_diff, mmu_en);

		/* Check if all child entries are allocated */
		bool fully_allocated = is_table_fully_allocated(child_table, level + 1);

		/* Update the parent table descriptor flag */
		uint64_t new_desc = parent_desc;

		if (fully_allocated && allocating) {
			new_desc |= VA_ALLOCATED_FLAG;
		} else {
			new_desc &= ~VA_ALLOCATED_FLAG;
		}

		if (new_desc != parent_desc) {
			xlat_write_tte(&table[child_idx], new_desc);
		}
	}
}

/*
 * Function to update level 3 table entries for a VA range.
 * Continues modifying the same L3 table as long as VA is within its range.
 * Only walks from base table when a new L3 table is needed.
 * `next_va` is updated to the next VA after the end of the mapped region.
 * This function returns 0 on success or a POSIX error code otherwise.
 */
static int xlat_tables_update_level3(struct xlat_ctx *ctx,
				struct xlat_mmap_region *mm, uintptr_t *next_va)
{
	assert(ctx != NULL);
	assert(mm != NULL);

	*next_va = mm->base_va;
	uintptr_t pa = mm->base_pa;
	uintptr_t end_va = mm->base_va + mm->size;

	struct xlat_llt_info llt;
	uintptr_t l3_base_va = 0;
	uint64_t *l3_table = NULL;
	uintptr_t prev_l3_base_va = 0;
	bool allocating = (MT_TYPE(mm->attr) != MT_TRANSIENT);

	while (*next_va < end_va) {
		/*
		 * If l3_table is not set or VA is outside current L3 table,
		 * get new L3 table.
		 */
		if ((l3_table == NULL) || (*next_va >= (l3_base_va +
				XLAT_BLOCK_SIZE(XLAT_TABLE_LEVEL_MAX)))) {
			/* Update parent flags for the previous L3 table before moving to next */
			if (l3_table != NULL) {
				update_parent_flags(ctx, prev_l3_base_va, allocating);
			}

			int ret = xlat_get_llt_from_va(&llt, ctx, *next_va);

			if ((ret != 0) || (llt.level != XLAT_TABLE_LEVEL_MAX)) {
				ERROR("%s: Failed to get L3 table for VA 0x%lx\n",
				      __func__, *next_va);
				return -EFAULT;
			}
			l3_table = llt.table;
			l3_base_va = llt.llt_base_va;
			prev_l3_base_va = l3_base_va;
		}

		/* Now at level 3 table */
		assert(l3_table != NULL);

		xlat_update_level3_descriptor(*next_va - l3_base_va,
						pa, l3_table, mm->attr);
		*next_va += XLAT_BLOCK_SIZE(XLAT_TABLE_LEVEL_MAX);

		/* Only increment PA if not unmapping */
		if (MT_TYPE(mm->attr) != MT_TRANSIENT) {
			pa += XLAT_BLOCK_SIZE(XLAT_TABLE_LEVEL_MAX);
		}
	}

	/* Update parent table flags for the last L3 table processed */
	if (l3_table != NULL) {
		update_parent_flags(ctx, prev_l3_base_va, allocating);
	}

	return 0;
}

/*
 * Optimized hierarchical VA search using VA_ALLOCATED_FLAG at all levels.
 * Searches L1 → L2 → L3, skipping fully allocated subtrees.
 * Processes entire L3 tables at once to avoid redundant table walks.
 * Handles consecutive free pages across L3 table boundaries.
 * Returns 0 on success with *out_mapped_va set, or -ENOMEM if no space found.
 */
static int find_available_va(struct xlat_ctx *ctx, size_t size,
			     uintptr_t *out_mapped_va)
{
	assert(ctx != NULL);

	struct xlat_ctx_tbls *ctx_tbls __unused = &ctx->tbls;
	struct xlat_ctx_cfg *ctx_cfg = &ctx->cfg;
	uintptr_t va_base = ctx_cfg->base_va;
	uintptr_t va_end __unused = va_base + ctx_cfg->max_va_size;

	size_t num_pages = size / GRANULE_SIZE;
	int start_level = ctx_cfg->base_level;
	bool mmu_en __unused = is_mmu_enabled();
	size_t l3_table_size = XLAT_BLOCK_SIZE(2); /* 2MB - size covered by one L3 table */
	/* Track consecutive free pages across L3 boundaries */
	size_t consecutive_free = 0;
	uintptr_t candidate_va = va_base;

	assert((start_level >= XLAT_TABLE_LEVEL_MIN) &&
	       (start_level <= XLAT_TABLE_LEVEL_MAX));


	/* Iterate through VA space L3 table by L3 table */
	uintptr_t va_offset = 0;
	while (va_offset < ctx_cfg->max_va_size) {

		/* Walk through levels to get the L3 table for this VA range */
		uint64_t *table = remap_table_address(ctx->tbls.tables,
						     ctx_tbls->tbls_va_to_pa_diff, mmu_en);
		uintptr_t table_base_va_offset = 0;
		bool skip_subtree = false;
		size_t skip_size = 0;

		for (int level = start_level; level <= XLAT_TABLE_LEVEL_MAX; level++) {
			unsigned int idx = XLAT_TABLE_IDX(va_offset - table_base_va_offset, level);

			assert(idx < XLAT_GET_TABLE_ENTRIES(level));

			uint64_t desc = xlat_read_tte(&table[idx]);

			/* Check if this subtree is fully allocated or if it is not TRANSIENT */
			if (((desc & VA_ALLOCATED_FLAG) != 0ULL) ||
			    ((desc & TRANSIENT_DESC) == 0ULL)) {
				/* Skip this entire subtree */
				skip_subtree = true;
				skip_size = XLAT_BLOCK_SIZE(level);
				break;
			}

			/* If we're at L3, scan all entries in this table */
			if (level == XLAT_TABLE_LEVEL_MAX) {
				unsigned int num_entries = XLAT_GET_TABLE_ENTRIES(level);
				uintptr_t l3_base_va = va_base + (va_offset & ~(l3_table_size - 1U));

				/* Scan through all entries in this L3 table */
				for (unsigned int i = idx; i < num_entries; i++) {
					uint64_t page_desc = xlat_read_tte(&table[i]);
					uintptr_t page_va = l3_base_va + (i * GRANULE_SIZE);

					/* Check if we've exceeded the VA space */
					assert(page_va < va_end);

					if ((page_desc & VA_ALLOCATED_FLAG) == 0ULL) {
						/* This page is free */
						consecutive_free++;
						if (consecutive_free >= num_pages) {
							*out_mapped_va = candidate_va;
							return 0;
						}
					} else {
						/* Page is allocated, reset search */
						consecutive_free = 0;
						candidate_va = page_va + GRANULE_SIZE;
					}
				}

				/* Move to next L3 table - will walk from base again */
				va_offset = round_up(va_offset + 1U, l3_table_size);
				break;
			}

			/* Not at L3 yet, assert that it's a table descriptor at lower level. */
			assert((desc & DESC_MASK) == TABLE_DESC);

			/* Descend to next level */
			table_base_va_offset += (XLAT_BLOCK_SIZE(level) * idx);
			table = remap_table_address(xlat_get_oa_from_tte(desc),
						   ctx_tbls->tbls_va_to_pa_diff, mmu_en);

		}

		/* If we need to skip a subtree, reset consecutive count and jump */
		if (skip_subtree) {
			consecutive_free = 0;
			va_offset = round_up(va_offset + 1U, skip_size);
			candidate_va = va_base + va_offset;
		}
	}

	return -ENOMEM;
}

/*
 * Public API to map a region by searching for available VA space.
 * This function searches for a contiguous free VA range and maps the given
 * PA at that location.
 *
 * Arguments:
 *   - ctx: Pointer to the translation context to use for mapping.
 *   - pa: Physical address to map
 *   - size: Size of the region to map
 *   - attr: Memory attributes for the mapping
 *   - mapped_va: Output pointer where the mapped VA will be stored
 *
 * Returns:
 *   - 0 on success, negative error code on failure.
 *   - On success, *mapped_va contains the virtual address where PA was mapped.
 */
int xlat_map_l3_region(struct xlat_ctx *ctx, uintptr_t pa, size_t size,
				uint64_t attr, uintptr_t *mapped_va)
{
	int ret;
	uintptr_t va;
	uintptr_t next_va = 0;
	struct xlat_mmap_region mm;

	assert(ctx != NULL);
	assert((ctx->cfg.init != false));
	assert((ctx->tbls.init != false));
	assert(mapped_va != NULL);
	assert(is_mmu_enabled());

	if (!GRANULE_ALIGNED(size) || !GRANULE_ALIGNED(pa)) {
		ERROR("%s: PA/size not aligned to granularity\n", __func__);
		return -EFAULT;
	}

	if (size == 0U) {
		ERROR("%s: Invalid size\n", __func__);
		return -EINVAL;
	}

	if (MT_TYPE(attr) == MT_TRANSIENT) {
		ERROR("%s: Transient attr should not be set.\n", __func__);
		return -EFAULT;
	}

	/* Find available VA space */
	ret = find_available_va(ctx, size, &va);
	if (ret != 0) {
		ERROR("%s: No available VA space for size 0x%zx\n", __func__, size);
		return ret;
	}

	/* Set up mmap region for mapping */
	mm.base_pa = pa;
	mm.base_va = va;
	mm.size = size;
	mm.granularity = GRANULE_SIZE;
	mm.attr = attr;

	/* Perform the actual mapping */
	ret = xlat_tables_update_level3(ctx, &mm, &next_va);
	if (ret != 0) {
		ERROR("%s: Failed to update level 3 tables\n", __func__);
		return -EFAULT;
	}

	assert(next_va >= mm.base_va);
	size_t mapped_size = next_va - mm.base_va;
	if (mapped_size != size) {
		ERROR("%s: Partial mapping (expected 0x%zx, got 0x%zx)\n",
			__func__, size, mapped_size);
		return -EFAULT;
	}

	*mapped_va = va;
	return 0;
}

/*
 * Public API to unmap a region described by 'mm' from the translation tables
 * in 'ctx'.
 * Assumes that the tables have been initialized and L3 tables corresponding
 * to the VA range have been created.
 * This function returns 0 on success or a POSIX error code otherwise.
 */
int xlat_unmap_l3_region(struct xlat_ctx *ctx, uintptr_t va, size_t unmap_size)
{
	struct xlat_mmap_region mm = {
		.base_va = va,
		.size = unmap_size,
		.base_pa = 0, /* PA is not needed for unmapping */
		.attr = MT_TRANSIENT, /* Use transient attr to indicate unmapping */
		.granularity = GRANULE_SIZE,
	};

	uintptr_t next_va = 0;
	int ret;

	assert((ctx != NULL) && (unmap_size != 0U));
	assert((ctx->cfg.init != false));
	assert((ctx->tbls.init != false));
	assert(is_mmu_enabled());

	if (!GRANULE_ALIGNED(mm.base_va) || !GRANULE_ALIGNED(unmap_size)) {
		ERROR("%s: VA/ unmap size not aligned to granularity\n", __func__);
		return -EFAULT;
	}

	ret = xlat_tables_update_level3(ctx, &mm, &next_va);
	assert(next_va >= mm.base_va);

	/* Invalidate TLB for affected VA range */
	XLAT_ARCH_TLBI_VA_RANGE(mm.base_va, next_va, ish, mm.granularity);
	XLAT_ARCH_TLBI_SYNC(ish);

	if ((ret != 0) || ((next_va - mm.base_va) != mm.size)) {
		ERROR("%s: Failed to update level 3 tables\n", __func__);
		return -EFAULT;
	}

	return 0;
}
