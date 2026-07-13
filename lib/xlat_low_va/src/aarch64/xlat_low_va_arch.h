/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef XLAT_LOW_VA_ARCH_H
#define XLAT_LOW_VA_ARCH_H

#include <assert.h>
#include <import_sym.h>
#include <mapped_va_arch.h>

#define get_shared_buf_pa()	rmm_el3_ifc_get_shared_buf_pa()

/*
 * Translate a virtual address in the low VA region to the corresponding
 * physical address.
 *
 * The address is first rounded down to a granule boundary and resolved via
 * xlat_low_va_get_contig_pa(). The original offset within the granule is
 * then added to the returned granule PA.
 *
 * Arguments:
 *   - va: Virtual address to translate.
 *
 * Returns:
 *   - Physical address corresponding to 'va'.
 *
 * This function asserts if the granule containing 'va' is not validly
 * mapped in the low VA translation tables.
 */
static inline uintptr_t arch_xlat_low_va_to_pa(uintptr_t va)
{
	uintptr_t gran_pa, gran_va = va & GRANULE_MASK;
	size_t size __unused;

	size = xlat_low_va_get_contig_pa(gran_va, gran_va + GRANULE_SIZE, &gran_pa);
	assert(size != 0UL);

	return gran_pa + (va & (GRANULE_SIZE - 1UL));
}

#endif /* XLAT_LOW_VA_ARCH_H */
