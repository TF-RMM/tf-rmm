/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef XLAT_LOW_VA_PVT_H
#define XLAT_LOW_VA_PVT_H


#define XLAT_LOW_VIRT_ADDR_SPACE_SIZE	(1UL << 41U)	/* 64TB */

/*
 * These funtions are internal to xlat_low_va and are declared in this
 * to enable unit-testing.
 */
void sort_mmap_region_array(struct xlat_mmap_region *regions,
			unsigned int region_count);
uintptr_t find_va_pool_base(struct xlat_mmap_region *regions,
				   unsigned int region_count);
int xlat_low_va_dyn_fixup(struct xlat_low_va_info *va_info);

#endif /* XLAT_LOW_VA_PVT_H */