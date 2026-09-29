/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef TRACKING_REGION_ARCH_H
#define TRACKING_REGION_ARCH_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <xlat_low_va.h>

/* Reserve an architectural VA for tracking metadata. */
static inline int tracking_region_arch_reserve(size_t size, uintptr_t *va)
{
	return xlat_low_va_reserve(size, va);
}

/* Populate and commit an architectural tracking-metadata mapping. */
static inline int tracking_region_arch_populate(uintptr_t va, uintptr_t pa,
						 size_t size)
{
	int ret;

	ret = xlat_low_va_populate(va, pa, size, MT_RW_DATA | MT_REALM);
	if (ret != 0) {
		return ret;
	}

	return xlat_low_va_commit(va, size);
}

/* Return the PA mapped at a committed tracking-metadata page. */
static inline uintptr_t tracking_region_arch_to_pa(uintptr_t va)
{
	return xlat_low_va_to_pa(va);
}

/* Return whether @va already has a tracking-metadata backing page. */
static inline bool tracking_region_arch_is_mapped(uintptr_t va)
{
	uintptr_t pa;

	return xlat_low_va_get_contig_pa(va, va + GRANULE_SIZE, &pa) != 0UL;
}

/* Remove committed tracking-metadata mappings while retaining their VA. */
static inline int tracking_region_arch_depopulate(uintptr_t va, size_t size)
{
	int ret;

	ret = xlat_low_va_decommit(va, size);
	if (ret != 0) {
		return ret;
	}

	return xlat_low_va_depopulate(va, size);
}

#endif /* TRACKING_REGION_ARCH_H */
