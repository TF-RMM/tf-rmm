/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <tb_common.h>
#include <xlat_tables.h>

int plat_cmn_init_el3_ifc(unsigned long x0, unsigned long x1,
			  unsigned long x2, unsigned long x3)
{
	ASSERT(false, "plat_cmn_init_el3_ifc");
	return 0;
}

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
