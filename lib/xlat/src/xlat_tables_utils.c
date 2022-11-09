/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 * SPDX-FileCopyrightText: Copyright Arm Limited and Contributors.
 */

/* This file is derived from xlat_table_v2 library in TF-A project */

#include <arch_helpers.h>
#include <debug.h>
#include <errno.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <utils_def.h>
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

	for (unsigned int i = 0U; i < ctx->cfg->mmap_num; i++) {
		uintptr_t base_va;

		base_va = ((ctx->cfg->region == VA_LOW_REGION) ?
				ctx->cfg->mmap[i].base_va :
				(ctx->cfg->mmap[i].base_va
					+ ctx->cfg->base_va));
		if (MT_TYPE(ctx->cfg->mmap[i].attr) != MT_TRANSIENT) {
			VERBOSE(" VA:0x%lx  PA:0x%lx  size:0x%zx  attr:0x%lx  granularity:0x%zx\n",
			       base_va, ctx->cfg->mmap[i].base_pa,
			       ctx->cfg->mmap[i].size, ctx->cfg->mmap[i].attr,
			       ctx->cfg->mmap[i].granularity);
		} else {
			VERBOSE(" VA:0x%lx  PA: TRANSIENT  size:0x%zx  granularity:0x%zx\n",
			       base_va, ctx->cfg->mmap[i].size,
			       ctx->cfg->mmap[i].granularity);
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
	} else if (mem_type_index == ATTR_NON_CACHEABLE_INDEX) {
		VERBOSE("NC");
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
	if ((desc & GP) != 0ULL) {
		VERBOSE("-GP");
	}
}

static const char * const level_spacers[] = {
	"[LV0] ",
	"  [LV1] ",
	"    [LV2] ",
	"      [LV3] "
};

static const char *invalid_descriptors_ommited =
		"%s(%d invalid descriptors omitted)\n";

/*
 * Recursive function that reads the translation tables passed as an argument
 * and prints their status.
 */
static void xlat_tables_print_internal(struct xlat_ctx *ctx, uintptr_t table_base_va,
		const uint64_t *table_base, unsigned int table_entries,
		unsigned int level)
{
	uint64_t *addr_inner;
	unsigned int invalid_row_count;
	unsigned int table_idx = 0U;
	size_t level_size;
	uintptr_t table_idx_va;

	if (level > XLAT_TABLE_LEVEL_MAX) {
		/* Level out of bounds */
		panic();
	}

	assert((ctx != NULL) &&
	       (ctx->cfg != NULL) &&
	       (ctx->tbls != NULL));

	level_size = XLAT_BLOCK_SIZE(level);
	table_idx_va = (ctx->cfg->region == (VA_LOW_REGION) ?
			(table_base_va) :
			(table_base_va + ctx->cfg->base_va));

	/*
	 * Keep track of how many invalid descriptors are counted in a row.
	 * Whenever multiple invalid descriptors are found, only the first one
	 * is printed, and a line is added to inform about how many descriptors
	 * have been omitted.
	 */
	invalid_row_count = 0U;

	while (table_idx < table_entries) {
		uint64_t desc;

		desc = table_base[table_idx];

		if ((desc & DESC_MASK) == INVALID_DESC) {

			if (invalid_row_count == 0U) {
				VERBOSE("%sVA:0x%lx size:0x%zx\n",
					level_spacers[level],
					table_idx_va, level_size);
			}
			invalid_row_count++;

		} else {

			if (invalid_row_count > 1U) {
				VERBOSE(invalid_descriptors_ommited,
				       level_spacers[level],
				       invalid_row_count - 1U);
			}
			invalid_row_count = 0U;

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
				       level_spacers[level],
				       table_idx_va, level_size);

				addr_inner = (uint64_t *)(void *)(desc & TABLE_ADDR_MASK);

				/* FIXME: Recursion. */
				xlat_tables_print_internal(ctx, table_idx_va,
					addr_inner, XLAT_TABLE_ENTRIES,
					level + 1U);
			} else {
				VERBOSE("%sVA:0x%lx PA:0x%lx size:0x%zx ",
				       level_spacers[level], table_idx_va,
				       (uint64_t)(desc & TABLE_ADDR_MASK),
				       level_size);
				xlat_desc_print(desc);
				VERBOSE("\n");
			}
		}

		table_idx++;
		table_idx_va += level_size;
	}

	if (invalid_row_count > 1U) {
		VERBOSE(invalid_descriptors_ommited,
			level_spacers[level], invalid_row_count - 1U);
	}
}

void xlat_tables_print(struct xlat_ctx *ctx)
{
	unsigned int used_page_tables;
	struct xlat_ctx_cfg *ctx_cfg = ctx->cfg;

	assert(ctx_cfg != NULL);

	uintptr_t max_mapped_va_offset = (ctx_cfg->region == (VA_LOW_REGION) ?
			(ctx_cfg->max_mapped_va_offset) :
			(ctx_cfg->max_mapped_va_offset + ctx_cfg->base_va));
	uintptr_t max_allowed_va = (ctx_cfg->region == (VA_LOW_REGION) ?
			(ctx_cfg->max_va_size) :
			(ctx_cfg->max_va_size + ctx_cfg->base_va));

	VERBOSE("Translation tables state:\n");
	VERBOSE("  Max allowed PA:  0x%lx\n", xlat_arch_get_max_supported_pa());
	VERBOSE("  Max allowed VA:  0x%lx\n", max_allowed_va);
	VERBOSE("  Max mapped PA:   0x%lx", ctx_cfg->max_mapped_pa);
	for (unsigned int i = 0U; i < ctx_cfg->mmap_num; i++) {
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

	VERBOSE("  Initial lookup level: %u\n", ctx_cfg->base_level);
	VERBOSE("  Entries @initial lookup level: %u\n",
					ctx->tbls->max_base_table_entries);

	used_page_tables = ctx->tbls->next_table;
	VERBOSE("  Used %d tables out of %d (spare: %d)\n",
				used_page_tables, ctx->tbls->tables_num,
				ctx->tbls->tables_num - used_page_tables);

	xlat_tables_print_internal(ctx, 0U, ctx->tbls->base_table,
				   ctx->tbls->max_base_table_entries,
				   ctx_cfg->base_level);
}

#endif /* LOG_LEVEL >= LOG_LEVEL_VERBOSE */

/*
 * Do a translation table walk to find the last level table that maps
 * virtual_addr.
 *
 * On success, return the address of the last level table within the
 * translation table. Its lookup level is stored in '*out_level'.
 * On error, return NULL.
 */
static uint64_t *find_xlat_last_table(uintptr_t virtual_addr,
				      const struct xlat_ctx * const ctx,
				      unsigned int * const out_level)
{
	unsigned int start_level;
	uint64_t *ret_table;
	unsigned int entries;
	struct xlat_ctx_tbls *ctx_tbls;
	struct xlat_ctx_cfg *ctx_cfg;


	assert(ctx != NULL);
	assert(ctx->cfg != NULL);
	assert(ctx->tbls != NULL);
	assert(out_level != NULL);

	ctx_tbls = ctx->tbls;
	ctx_cfg = ctx->cfg;
	start_level = ctx_cfg->base_level;
	ret_table = ctx_tbls->base_table;
	entries = ctx_tbls->max_base_table_entries;

	for (unsigned int level = start_level;
	     level <= XLAT_TABLE_LEVEL_MAX;
	     level++) {
		unsigned int idx;
		uint64_t desc;
		uint64_t desc_type;

		idx = XLAT_TABLE_IDX(virtual_addr, level);
		if (idx >= entries) {
			WARN("Missing xlat table entry at address 0x%lx\n",
			      virtual_addr);
			return NULL;
		}

		desc = ret_table[idx];
		desc_type = desc & DESC_MASK;

		if (desc_type != TABLE_DESC) {
			if (((desc_type == BLOCK_DESC) ||
			    (((desc_type == PAGE_DESC) || (desc_type == INVALID_DESC))
			      && (level == XLAT_TABLE_LEVEL_MAX)))) {
				*out_level = level;
				return ret_table;
			}
			return NULL;
		}

		ret_table = (uint64_t *)(void *)(desc & TABLE_ADDR_MASK);
		entries = XLAT_TABLE_ENTRIES;
	}

	/*
	 * This shouldn't be reached, the translation table walk should end at
	 * most at level XLAT_TABLE_LEVEL_MAX and return from inside the loop
	 * but we need this to avoid MISRA problems.
	 */
	return NULL;
}

/*****************************************************************************
 * Public part of the utility library for translation tables.
 ****************************************************************************/

/*
 * Function to unmap a physical memory page from the descriptor entry and
 * VA given.
 * This function implements the "Break" part of the Break-Before-Make semantics
 * needed by the Armv8.x architecture in order to update the page descriptors.
 *
 * This function returns 0 on success or an error code otherwise.
 *
 * For simplicity, this function will not take into consideration holes on the
 * table pointed by entry, as long as va belongs to the VA space owned by the
 * context.
 */
int xlat_unmap_memory_page(struct xlat_table_entry * const table,
			   const uintptr_t va)
{
	uint64_t *entry;

	assert(table != NULL);

	entry = xlat_get_pte_from_table(table, va);

	if (entry == NULL) {
		return -EFAULT;
	}

	/*
	 * No need to perform any checks on this page descriptor as it is going
	 * to be made invalid anyway.
	 */
	xlat_write_descriptor(entry, INVALID_DESC);

	/* Invalidate any cached copy of this mapping in the TLBs. */
	xlat_arch_tlbi_va(va);

	/* Ensure completion of the invalidation. */
	xlat_arch_tlbi_va_sync();

	return 0;
}

/*
 * Function to map a physical memory page from the descriptor table entry
 * and VA given. This function implements the "Make" part of the
 * Break-Before-Make semantics needed by the armv8.x architecture in order
 * to update the page descriptors.
 *
 * This function eturns 0 on success or an error code otherwise.
 *
 * For simplicity, this function will not take into consideration holes on the
 * table pointed by entry, as long as va belongs to the VA space owned by the
 * context.
 */
int xlat_map_memory_page_with_attrs(const struct xlat_table_entry * const table,
				    const uintptr_t va,
				    const uintptr_t pa,
				    const uint64_t attrs)
{
	uint64_t desc;
	uint64_t *desc_ptr;

	assert(table != NULL);

	desc_ptr = xlat_get_pte_from_table(table, va);

	if (desc_ptr == NULL) {
		return -EFAULT;
	}

	/* This function must only be called on invalid descriptors */
	if (xlat_read_descriptor(desc_ptr) != INVALID_DESC) {
		return -EFAULT;
	}

	/* Check that pa is within boundaries */
	if (pa > xlat_arch_get_max_supported_pa()) {
		return -EFAULT;
	}

	/* Generate the new descriptor */
	desc = xlat_desc(attrs, pa, table->level);

	xlat_write_descriptor(desc_ptr, desc);

	/* Ensure the translation table write has drained into memory */
	dsb(ishst);
	isb();

	return 0;
}

/*
 * Return a table entry structure given a context and a VA.
 * The return structure is populated on the retval field.
 *
 * This function returns 0 on success or a Linux error code otherwise.
 */
int xlat_get_table_from_va(struct xlat_table_entry * const retval,
			   const struct xlat_ctx * const ctx,
			   const uintptr_t va)
{
	uintptr_t page_va;
	uint64_t *table;
	unsigned int level;
	struct xlat_ctx_cfg *ctx_cfg;

	assert((ctx != NULL) &&
	       (ctx->cfg != NULL) &&
	       (ctx->tbls != NULL) &&
	       (retval != NULL) &&
	       (ctx->tbls->initialized == true));

	ctx_cfg = ctx->cfg;

	/* Check if the VA is within the mapped range */
	if (((va > (ctx_cfg->max_mapped_va_offset + ctx_cfg->base_va))
		|| (va < ctx_cfg->base_va))) {
		return -EFAULT;
	}

	/*
	 * From the translation tables point of view, the VA is actually an
	 * offset with regards to the base address of the VA space, so before
	 * using a VA, we need to extract the base VA from it.
	 */
	page_va = va - ctx_cfg->base_va;
	page_va &= ~PAGE_SIZE_MASK; /* Page address of the VA address passed. */

	table = find_xlat_last_table(page_va, ctx, &level);

	if (table == NULL) {
		WARN("Address 0x%lx is not mapped.\n", va);
		return -EFAULT;
	}

	/* Maximum number of entries used by this table. */
	if (level == ctx_cfg->base_level) {
		retval->entries = ctx->tbls->max_base_table_entries;
	} else {
		retval->entries = XLAT_TABLE_ENTRIES;
	}

	retval->table = table;
	retval->level = level;
	retval->base_va = ctx_cfg->base_va;

	return 0;
}

/*
 * This function finds the descriptor entry on a table given the corresponding
 * table entry structure and the VA for that descriptor.
 *
 * If va is not mapped by the table pointed by entry, it returns NULL.
 *
 * For simplicity and as long as va belongs to the VA space owned by the
 * translation context, this function will not take into consideration holes
 * on the table pointed by entry either because the address is not mapped by
 * the caller or left as INVALID_DESC for future dynamic mapping.
 */
uint64_t *xlat_get_pte_from_table(const struct xlat_table_entry * const entry,
				    const uintptr_t va)
{
	unsigned int index;
	uint64_t *table;
	uintptr_t va_offset;

	assert(entry != NULL);

	if (va < entry->base_va) {
		return NULL;
	}

	/*
	 * From the translation tables point of view, the VA is actually an
	 * offset with regards to the base address of the VA space, so before
	 * using a VA, we need to extract the base VA from it.
	 */

	va_offset = va - entry->base_va;
	table = entry->table;
	index = XLAT_TABLE_IDX(va_offset, entry->level);

	if (index >= entry->entries) {
		return NULL;
	}

	return &table[index];
}
