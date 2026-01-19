/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef XLAT_CMN_ARCH_H
#define XLAT_CMN_ARCH_H

#define remap_table_address(table, tbls_va_to_pa_diff, is_mmu_en)	\
		((uint64_t *)((unsigned long)(table) & ~(VA_ALLOCATED_FLAG | TRANSIENT_DESC)))

#endif /* XLAT_CMN_ARCH_H */
