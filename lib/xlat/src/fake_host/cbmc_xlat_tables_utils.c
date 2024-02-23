/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

/* This file is only used for CBMC analysis. */

#ifdef CBMC

#include <stdbool.h>
#include <tb_common.h>
#include <xlat_tables.h>

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
