/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef XLAT_HIGH_VA_H
#define XLAT_HIGH_VA_H

#include <xlat_tables.h>

/* TTE attribute for per CPU private VA (nG) Data mapping) */
#define XLAT_NG_DATA_ATTR	(MT_RW_DATA | MT_NG)

/* TTE attribute for per CPU private VA (nG) Device mapping) */
#define XLAT_NG_DEV_ATTR	(MT_RW_DEV | MT_NG)

#define XLAT_HIGH_VA_SIZE	(XLAT_TABLE_ENTRIES * PAGE_SIZE)

#if !(defined(__ASSEMBLER__) || defined(__LINKER__))

/* Return a pointer to the High VA xlat context for the current CPU */
struct xlat_ctx *xlat_get_high_va_xlat_ctx(void);

/*
 * Initializes and enables the VMSA for the high va region.
 *
 * Create an empty translation context for the current PE.
 * If the context already exists (e.g. current PE was previously
 * turned on and therefore the context is already in memory),
 * nothing happens.
 */
int xlat_high_va_setup(struct xlat_mmap_region *mm, unsigned int regions);

#endif /* !(defined(__ASSEMBLER__) || defined(__LINKER__)) */

#endif /* XLAT_HIGH_VA_H */
