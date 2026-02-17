/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 * SPDX-FileCopyrightText: Copyright Arm Limited and Contributors.
 */

/* This file is derived from xlat_table_v2 library in TF-A project */

#ifndef XLAT_CONTEXTS_H
#define XLAT_CONTEXTS_H

#define RMM_ASID	U(0)

#if !(defined(__ASSEMBLER__) || defined(__LINKER__))

#include <stdbool.h>
#include <xlat_defs.h>

/* Enumerator to identify the right address space within a context */
typedef enum {
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

	/*
	 * Physical address of the base page table (i.e. PA of `tables[0]` in
	 * this structure)
	 */
	uint64_t base_table_pa;

	/*
	 * Difference between virtual and physical addresses
	 * for the translation tables when the MMU is enabled.
	 * This is used to translate a table PA to a VA when
	 * the MMU is on.
	 */
	long tbls_va_to_pa_diff;

	/* Set to true when the translation tables are initialized. */
	bool init;
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

	/*
	 * The ASID value associated with this translation context
	 */
	uint32_t asid;

	bool init;
} __aligned(CACHE_WRITEBACK_GRANULE);

/*
 * Struct that holds the context itself, composed of
 * the context config and the translation tables associated
 * to it, embedded directly.
 *
 * Aligned on cacheline size as this data can be accessed on
 * secondaries with MMU off.
 */
struct xlat_ctx {
	struct xlat_ctx_cfg cfg;
	struct xlat_ctx_tbls tbls;
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
 * Function to initialize the configuration structure for a
 * translation context. This function must be called before
 * the MMU is enabled.
 *
 * Arguments:
 *	- ctx: Pointer to a xlat_ctx structure whose cfg will be initialized.
 *	- region: xlat_addr_region_id_t descriptor indicating the memory
 *		  region for the configured context.
 *	- mm: List of memory map regions to add to the
 *	      context configuration.
 *	- mm_regions: Number of memory regions in the mm array.
 *	- partial_va_base: If tables are only being constructed for a part of
 *	      the VA region, this is the start address of that area. If the
 *	      tables are being constructed for the whole VA region, this should
 *	      be 0.
 *	- va_size: Size of the VA space for the current context.
 *	- asid: The Address Space ID associated with this context
 *
 * Return:
 *	- 0 on success or a negative POSIX error otherwise.
 */
int xlat_ctx_cfg_init(struct xlat_ctx *ctx,
		      xlat_addr_region_id_t region,
		      struct xlat_mmap_region *mm,
		      unsigned int mm_regions,
		      uint64_t partial_va_base,
		      size_t va_size,
		      uint32_t asid);

/*
 * Initializes the translation context (xlat_ctx) tables according to
 * the context configuration. The cfg must have already been initialized
 * via xlat_ctx_cfg_init(). The tables are created according to the memory
 * map description and stored in the tables area pointed by `tables_ptr`.
 * Must be called before the MMU is enabled.
 *
 * Arguments:
 *	- ctx: Pointer to the xlat_ctx structure to initialize.
 *	       The cfg must have already been initialized via xlat_ctx_cfg_init().
 *	- tables_ptr: Pointer to the memory for the translation tables,
 *		      the memory provided must be page aligned and multiple
 *		      of page size.
 *	- ntables: Number of pages passed in the `tables_ptr`.
 *	- base_table_pa: The PA of the base page table.
 *
 * Return:
 *	- 0 on success.
 *	- -EALREADY if tbls is already initialized.
 *	- Negative POSIX error codes on all other errors.
 */
int xlat_ctx_init(struct xlat_ctx *ctx,
		  uint64_t *tables_ptr,
		  unsigned int ntables,
		  uint64_t base_table_pa);

/*
 * Similar to xlat_ctx_init() but allows to create translation tables for
 * a context where the tables are not identity mapped and tables are created
 * with MMU disabled. The `tbls_array_va` argument specifies the VA of the
 * tables array, i.e., where the tbls themselves are mapped in the VA space.
 * This will be used when the tables need to be walked when MMU is enabled.
 *
 * The tables are assumed to allocated as a block and mapped as a single
 * block in the VA space.
 */
int xlat_ctx_init_remapped_tbls(struct xlat_ctx *ctx,
		  uint64_t *tables_ptr,
		  unsigned int ntables,
		  uint64_t base_table_pa,
		  uint64_t tbls_array_va);

#endif /*__ASSEMBLER__*/
#endif /* XLAT_CONTEXTS_H */
