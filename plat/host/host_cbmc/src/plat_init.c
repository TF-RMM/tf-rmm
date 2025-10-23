/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <plat_compat_mem.h>
#include <tb_common.h>
#include <xlat_tables.h>

int plat_cmn_setup(struct xlat_mmap_region *plat_regions,
		   unsigned int nregions)
{
	ASSERT(false, "plat_cmn_setup");
	return 0;
}

int plat_cmn_warmboot_setup(void)
{
	ASSERT(false, "plat_cmn_warmboot_setup");
	return 0;
}

void plat_cmn_compat_reserve_mem_init(struct rmm_el3_compat_callbacks *cb,
		void *base_addr, size_t size)
{
	ASSERT(false, "plat_cmn_compat_reserve_mem_init");
}

int plat_compat_reserve_memory(size_t size, uint64_t *arg)
{
	ASSERT(false, "plat_compat_reserve_memory");
	return 0;
}
