/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 * SPDX-FileCopyrightText: Copyright Arm Limited and Contributors.
 */

/* This file is derived from xlat_table_v2 library in TF-A project */

#ifndef XLAT_CONTEXTS_H
#define XLAT_CONTEXTS_H

#if !(defined(__ASSEMBLER__) || defined(__LINKER__))

#include <stdbool.h>
#include <xlat_defs.h>

/* Enumerator to identify the right address space within a context */
typedef enum xlat_addr_region_id {
	VA_LOW_REGION = 0,
	VA_HIGH_REGION,
	VA_REGIONS
} xlat_addr_region_id_t;

/*
 * Structure to hold all the xlat tables and related information within a
 * context. This allows to reuse the same xlat_ctx_cfg part of the context
 * on several PEs that share the same memory map region whilst keeping
 * private tables for each PE.
 *
 * Aligned on cacheline size as this data can be accessed on
 * secondaries with MMU off.
 */
struct xlat_ctx_tbls {
	/* Array of translation tables. */
	uint64_t *tables;
	unsigned int tables_num;
	unsigned int next_table;

	/* Set to true when the translation tables are initialized. */
	bool initialized;
}  __aligned(CACHE_WRITEBACK_GRANULE);

/*
 * Struct that holds the context configuration.
 * Aligned on cacheline size as this data can be accessed on
 * secondaries with MMU off.
 */
struct xlat_ctx_cfg {
	/*
	 * Maximum size allowed for the VA space handled by the context.
	 */
	uintptr_t max_va_size;

	/*
	 * Pointer to an array with all the memory regions stored in order
	 * of ascending base_va.
	 */
	struct xlat_mmap_region *mmap;

	/*
	 * Number of regions stored in the mmap array.
	 */
	unsigned int mmap_regions;

	/*
	 * Base address for the virtual space on this context.
	 */
	uintptr_t base_va;

	/*
	 * Max Physical and Virtual addresses currently in use by the
	 * current context. These will get updated as we map memory
	 * regions but it will never go beyond the maximum physical address
	 * or max_va_size respectively.
	 *
	 * max_mapped_pa is an absolute Physical Address.
	 */
	uintptr_t max_mapped_pa;
	uintptr_t max_mapped_va_offset;

	/* Level of the base translation table. */
	int base_level;

	/*
	 * Virtual address region handled by this context.
	 */
	xlat_addr_region_id_t region;

	bool initialized;
} __aligned(CACHE_WRITEBACK_GRANULE);

/*
 * Struct that holds the context itself, composed of
 * a pointer to the context config and a pointer to the
 * translation tables associated to it.
 *
 * Aligned on cacheline size as this data can be accessed on
 * secondaries with MMU off.
 */
struct xlat_ctx {
	struct xlat_ctx_cfg *cfg;
	struct xlat_ctx_tbls *tbls;
} __aligned(CACHE_WRITEBACK_GRANULE);

/*
 * The translation tables are aligned to their size. For 4KB graularity, this
 * is aligned to 4KB as well.
 */
#define XLAT_TABLES_ALIGNMENT		XLAT_TABLE_SIZE

/*
 * Compute the number of entries required at the initial lookup level to
 * address the whole virtual address space.
 */
#define GET_NUM_BASE_LEVEL_ENTRIES(addr_space_size)			\
	((addr_space_size) >>						\
		XLAT_ADDR_SHIFT(GET_XLAT_TABLE_LEVEL_BASE(addr_space_size)))

/*
 * Macro to check if the xlat_ctx_cfg part of a context is valid.
 */
#define XLAT_TABLES_CTX_CFG_VALID(_ctx)	((_ctx)->cfg != NULL)

/*
 * Macro to check if the xlat_ctx_tbls part of a context is valid.
 */
#define XLAT_TABLES_CTX_TBL_VALID(_ctx)	((_ctx)->tbls != NULL)

/*
 * Function to initialize the configuration structure for a
 * translation context. This function must be called before
 * the MMU is enabled.
 *
 * Arguments:
 *	- cfg: Pointer to a xlat_ctx_cfg structure to initialize.
 *	- region: xlat_addr_region_id_t descriptor indicating the memory
 *		  region for the configured context.
 *	- mm: List of memory map regions to add to the
 *	      context configuration.
 *	- mm_regions: Number of memory regions in the mm array.
 *	- va_size: Size of the VA space for the current context.
 *
 * Return:
 *	- 0 on success or a negative POSIX error otherwise.
 */
int xlat_ctx_cfg_init(struct xlat_ctx_cfg *cfg,
		      xlat_addr_region_id_t region,
		      struct xlat_mmap_region *mm,
		      unsigned int mm_regions,
		      size_t va_size);

/*
 * Initializes the translation context (xlat_ctx) and the xlat_ctx_tbls with
 * the given xlat_ctx_cfg. The tables are created according to the memory
 * map description available in the latter and stored in the tables area
 * pointed by `tables_ptr`.
 * Must be called before the MMU is enabled.
 *
 * Arguments:
 *	- ctx: Pointer to the xlat_ctx structure to initialize.
 *	- cfg: Pointer to the structure containing the context configuration.
 *	       This must have already been initialized via xlat_ctx_cfg_init().
 *	- tbls_ctx: Pointer to a xlat_ctx_tbls structure to configure the
 *		    associated table data for the translation context.
 *	- tables_ptr: Pointer to the memory for the translation tables,
 *		      the memory provided must be page aligned and multiple
 *		      of page size.
 *	- ntables: Number of pages passed in the `tables_ptr`.
 *
 * Return:
 *	- 0 on success.
 *	- -EALREADY if tbls_ctx is already initialized.
 *	- Negative POSIX error codes on all other errors.
 */
int xlat_ctx_init(struct xlat_ctx *ctx,
		  struct xlat_ctx_cfg *cfg,
		  struct xlat_ctx_tbls *tbls_ctx,
		  uint64_t *tables_ptr,
		  unsigned int ntables);

#endif /*__ASSEMBLER__*/
#endif /* XLAT_CONTEXTS_H */
