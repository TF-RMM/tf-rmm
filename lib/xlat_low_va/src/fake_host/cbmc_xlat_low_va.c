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
