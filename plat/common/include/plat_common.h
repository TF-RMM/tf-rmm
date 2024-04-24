/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef PLAT_COMMON_H
#define PLAT_COMMON_H

/* Forward declaration */
struct xlat_mmap_region;

int plat_cmn_init_el3_ifc(unsigned long x0, unsigned long x1,
		   unsigned long x2, unsigned long x3);
int plat_cmn_setup(struct xlat_mmap_region *plat_regions,
		   unsigned int nregions);
int plat_cmn_warmboot_setup(void);

#endif /* PLAT_COMMON_H */
