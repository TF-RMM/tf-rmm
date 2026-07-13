/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <stdbool.h>
#include <tb_common.h>
#include <xlat_tables.h>

int xlat_low_va_setup(struct xlat_mmap_region *plat_regions,
	unsigned int nregions, uintptr_t rmm_img_start)
{
	ASSERT(false, "xlat_low_va_setup");
	return 0;
}

int xlat_low_va_mmu_cfg(void)
{
	ASSERT(false, "xlat_low_va_mmu_cfg");
	return 0;
}

int xlat_low_va_reserve(size_t size, uintptr_t *reserved_va)
{
	(void)size;
	(void)reserved_va;

	return 0;
}

int xlat_low_va_unreserve(uintptr_t va, size_t size)
{
	(void)va;
	(void)size;

	return 0;
}

int xlat_low_va_populate(uintptr_t va, uintptr_t pa, size_t size, uint64_t attr)
{
	(void)va;
	(void)pa;
	(void)size;
	(void)attr;

	return 0;
}

int xlat_low_va_depopulate(uintptr_t va, size_t size)
{
	(void)va;
	(void)size;

	return 0;
}

int xlat_low_va_commit(uintptr_t va, size_t size)
{
	(void)va;
	(void)size;

	return 0;
}

int xlat_low_va_decommit(uintptr_t va, size_t size)
{
	(void)va;
	(void)size;
	return 0;
}

uintptr_t xlat_low_va_to_pa(uintptr_t va)
{
	return va;
}
