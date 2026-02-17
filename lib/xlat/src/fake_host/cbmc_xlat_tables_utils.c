/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

/* This file is only used for CBMC analysis. */

#ifdef CBMC

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <tb_common.h>
#include <xlat_contexts.h>
#include <xlat_tables.h>

int xlat_ctx_cfg_init(struct xlat_ctx *ctx,
		      xlat_addr_region_id_t region,
		      struct xlat_mmap_region *mm,
		      unsigned int mm_regions,
		      uint64_t partial_va_base,
		      size_t va_size,
		      uint32_t asid)
{
	ASSERT(false, "xlat_ctx_cfg_init");
	return 0;
}

int xlat_ctx_init_remapped_tbls(struct xlat_ctx *ctx,
				uint64_t *tables_ptr,
				unsigned int ntables,
				uint64_t base_table_pa,
				uint64_t tbls_array_va)
{
	ASSERT(false, "xlat_ctx_init_remapped_tbls");
	return 0;
}

int xlat_arch_setup_mmu_cfg(struct xlat_ctx * const ctx,
			    struct xlat_mmu_cfg *mmu_config)
{
	ASSERT(false, "xlat_arch_setup_mmu_cfg");
	return 0;
}

void xlat_arch_write_mmu_cfg(struct xlat_mmu_cfg *mmu_cfg)
{
	ASSERT(false, "xlat_arch_write_mmu_cfg");
}

int xlat_get_llt_from_va(struct xlat_llt_info * const llt,
			 const struct xlat_ctx * const ctx,
			 const uintptr_t va)
{
	ASSERT(false, "xlat_get_llt_from_va");
	return 0;
}

int xlat_unmap_memory_page(struct xlat_llt_info * const table,
			   const uintptr_t va)
{
	ASSERT(false, "xlat_unmap_memory_page");
	return 0;
}

int xlat_map_memory_page_with_attrs(const struct xlat_llt_info * const table,
				    const uintptr_t va,
				    const uintptr_t pa,
				    const uint64_t attrs)
{
	ASSERT(false, "xlat_map_memory_page_with_attrs");
	return 0;
}

uint64_t *xlat_get_tte_ptr(const struct xlat_llt_info * const llt,
			   const uintptr_t va)
{
	ASSERT(false, "xlat_get_tte_ptr");
	return 0;
}

#endif /* CBMC */
