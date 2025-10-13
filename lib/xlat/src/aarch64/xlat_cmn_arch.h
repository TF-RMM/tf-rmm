/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef XLAT_CMN_ARCH_H
#define XLAT_CMN_ARCH_H

#include <import_sym.h>

#define get_shared_buf_pa()	rmm_el3_ifc_get_shared_buf_pa()

#define remap_table_address(table, tbls_va_to_pa_diff, is_mmu_en)	\
	((is_mmu_en) ?							\
		((uint64_t *)((uintptr_t)(table) + (unsigned long)(tbls_va_to_pa_diff))) : \
		(uint64_t *)(table))


#endif /* ARM_CMN_ARCH_H */
