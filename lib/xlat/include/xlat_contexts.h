/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 * SPDX-FileCopyrightText: Copyright Arm Limited and Contributors.
 */

/* This file is derived from xlat_table_v2 library in TF-A project */

#ifndef XLAT_CONTEXTS_H
#define XLAT_CONTEXTS_H

#ifndef __ASSEMBLER__

#include <assert.h>
#include <stdbool.h>
#include <stddef.h>
#include <utils_def.h>
#include <xlat_defs.h>

/* Forward declaration */
struct xlat_mmap_region;

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
 */
struct xlat_ctx_tbls {
	/*
	 * Array of finer-grain translation tables.
	 * For example, if the initial lookup level is 1 then this array would
	 * contain both level-2 and level-3 entries.
	 */
	uint64_t (*tables)[XLAT_TABLE_ENTRIES];
	unsigned int tables_num;
	unsigned int next_table;

	/*
	 * Base translation table.
	 * It has the same number of entries as the ones used for other levels
	 * although it is possible that not all the entries are used.
	 *
	 * If, as an example, the translation tables for the current context
	 * start at L1, then the *tables field will contain the L2 and L3
	 * tables.
	 */
	uint64_t *base_table;
	unsigned int max_base_table_entries;

	/* Set to true when the translation tables are initialized. */
	bool initialized;
};

/* Struct that holds the context configuration */
struct xlat_ctx_cfg {
	/*
	 * Maximum size allowed for the VA space handled by the context.
	 */
	uintptr_t max_va_size;

	/*
	 * Array of all memory regions stored in order of ascending base_va.
	 * The list is terminated by the first entry with
	 * size == 0 or when all entries are used (as specified by mmap_num).
	 */
	struct xlat_mmap_region *mmap;
	unsigned int mmap_num;

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
	unsigned int base_level;

	/*
	 * Virtual address region handled by this context.
	 */
	xlat_addr_region_id_t region;

	bool initialized;
};

/*
 * Struct that holds the context itself, composed of
 * a pointer to the context config and a pointer to the
 * translation tables associated to it.
 */
struct xlat_ctx {
	struct xlat_ctx_cfg *cfg;
	struct xlat_ctx_tbls *tbls;
};

/*
 * The translation tables are aligned to their size. For 4KB graularity, this
 * is aligned to 4KB as well.
 */
#define XLAT_TABLES_ALIGNMENT		XLAT_TABLE_SIZE

/*
 * Align the base tables to page boundary. This migh generate larger tables
 * than needed, but it simplifies the code, which is a good trade-off
 * since we have enough memory.
 */
#define BASE_XLAT_TABLES_ALIGNMENT	XLAT_TABLE_SIZE

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
#define XLAT_TABLES_CTX_TBL_VALID(_ctx)		((_ctx)->tbls != NULL)

/*
 * Macro to allocate translation tables to be used within a context.
 */
#define XLAT_CREATE_TABLES(_tblset_name,				\
			   _xlat_tables_count,				\
			   _virt_addr_space_size,			\
			   _tables_section)				\
									\
	static uint64_t _tblset_name##_base_xlat_table			\
		[(XLAT_TABLE_ENTRIES)]					\
		__aligned((BASE_XLAT_TABLES_ALIGNMENT))			\
		__section((_tables_section));				\
									\
	static uint64_t _tblset_name##_xlat_tables[(_xlat_tables_count)]\
		[(XLAT_TABLE_ENTRIES)]					\
		__aligned((XLAT_TABLES_ALIGNMENT))			\
		__section((_tables_section));				\
									\
	static struct xlat_ctx_tbls _tblset_name##_tbls = {		\
		.tables = _tblset_name##_xlat_tables,			\
		.tables_num = (_xlat_tables_count),			\
		.next_table = 0,					\
		.base_table = _tblset_name##_base_xlat_table,		\
		.max_base_table_entries =				\
			GET_NUM_BASE_LEVEL_ENTRIES(_virt_addr_space_size),\
		.initialized = false					\
	}								\

/*
 * Macro used to define the xlat_ctx_cfg and xlat_mmap_region array
 * associated with a context.
 */
#define XLAT_REGISTER_VA_SPACE(_ctx_name, _region, _mmap_count,		\
			_virt_addr_space_size)				\
	COMPILER_ASSERT(((_region) < VA_REGIONS));			\
	COMPILER_ASSERT(((unsigned long)(_virt_addr_space_size)		\
					% GRANULE_SIZE) == UL(0));	\
	COMPILER_ASSERT((unsigned long)(_virt_addr_space_size)		\
					<= (MAX_VIRT_ADDR_SPACE_SIZE));	\
									\
	static struct xlat_mmap_region _ctx_name##_mmap[(_mmap_count)];	\
									\
	static struct xlat_ctx_cfg _ctx_name##_xlat_ctx_cfg = {		\
		.max_va_size = (_virt_addr_space_size),			\
		.base_va = 0ULL,					\
		.mmap = _ctx_name##_mmap,				\
		.mmap_num = (_mmap_count),				\
		.max_mapped_va_offset = 0ULL,				\
		.max_mapped_pa = 0ULL,					\
		.base_level =						\
			(GET_XLAT_TABLE_LEVEL_BASE((_virt_addr_space_size))),\
		.region = (_region),					\
		.initialized = false					\
	}

/*
 * Macro to generate a context and associate the translation table set passed
 * to it by ref.
 */
#define XLAT_REGISTER_CONTEXT_FULL_SPEC(_ctx_name, _region, _mmap_count,\
			_virt_addr_space_size,				\
			_tables_set)					\
	XLAT_REGISTER_VA_SPACE(_ctx_name, (_region),			\
			       (_mmap_count), (_virt_addr_space_size));	\
									\
	static struct xlat_ctx _ctx_name##_xlat_ctx = {			\
		.cfg = &(_ctx_name##_xlat_ctx_cfg),			\
		.tbls = (_tables_set)					\
	}

/*
 * Statically allocate a translation context and associated translation
 * tables. Also initialize them.
 *
 * _ctx_name:
 *   Prefix for the translation context variable.
 *   E.g. If _ctx_name is 'foo', the variable will be called 'foo_xlat_ctx'.
 *   Useful to distinguish multiple contexts from one another.
 *
 * _region:
 *   Region mapped by this context (high or low address region).
 *   See @xlat_ctx_region_id_t for more info.
 *
 * _mmap_count:
 *   Number ofstruct xlat_mmap_region to allocate.
 *   Would be defined during the context creation.
 *
 * _xlat_tables_count:
 *   Number of non-base tables to allocate at level others than the
 *   initial lookup.
 *
 * _virt_addr_space_size:
 *   Size (in bytes) of the virtual address space that can be accessed by this
 *   context.
 *
 * _section_name:
 *   Specify the name of the section where the translation tables have to be
 *   placed by the linker.
 */
#define XLAT_REGISTER_CONTEXT(_ctx_name, _region, _mmap_count,		\
			      _xlat_tables_count,			\
			      _virt_addr_space_size,			\
			      _section_name)				\
		XLAT_CREATE_TABLES(_ctx_name, (_xlat_tables_count),	\
				   (_virt_addr_space_size),		\
				   (_section_name));			\
									\
		XLAT_REGISTER_CONTEXT_FULL_SPEC(_ctx_name, (_region),	\
						(_mmap_count),		\
						(_virt_addr_space_size),\
						&(_ctx_name##_tbls))

#endif /*__ASSEMBLER__*/

#endif /* XLAT_CONTEXTS_H */
