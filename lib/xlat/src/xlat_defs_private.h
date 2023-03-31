/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 * SPDX-FileCopyrightText: Copyright Arm Limited and Contributors.
 */

/* This file is derived from xlat_table_v2 library in TF-A project */

#ifndef XLAT_DEFS_PRIVATE_H
#define XLAT_DEFS_PRIVATE_H

#include <arch.h>
#include <utils_def.h>
#include <xlat_defs.h>

/* Miscellaneous MMU related constants */
#define NUM_2MB_IN_GB		(UL(1) << 9)
#define NUM_4K_IN_2MB		(UL(1) << 9)
#define NUM_GB_IN_4GB		(UL(1) << 2)

#define TWO_MB_SHIFT		UL(21)
#define ONE_GB_SHIFT		UL(30)
#define FOUR_KB_SHIFT		UL(12)

#define ONE_GB_INDEX(x)		((x) >> ONE_GB_SHIFT)
#define TWO_MB_INDEX(x)		((x) >> TWO_MB_SHIFT)
#define FOUR_KB_INDEX(x)	((x) >> FOUR_KB_SHIFT)

/*
 * A block descriptor points to a region of memory bigger than the granule size
 * (e.g. a 2MB region when the granule size is 4KB).
 */
/* Definition of a valid descriptor mask */
#define VALID_DESC		UL(0x1)
#define BLOCK_DESC		VALID_DESC /* Table levels 0-2 */
/* A table descriptor points to the next level of translation table. */
#define TABLE_DESC		(UL(0x2) | VALID_DESC) /* Table levels 0-2 */
/* Definition of an invalid descriptor */
#define INVALID_DESC		UL(0x0)
/*
 * A page descriptor points to a page, i.e. a memory region whose size is the
 * translation granule size (e.g. 4KB).
 */
#define PAGE_DESC		(UL(0x2) | VALID_DESC) /* Table level 3 */

#define DESC_MASK		UL(0x3)

#define FIRST_LEVEL_DESC_N	ONE_GB_SHIFT
#define SECOND_LEVEL_DESC_N	TWO_MB_SHIFT
#define THIRD_LEVEL_DESC_N	FOUR_KB_SHIFT

#define XN			(ULL(1) << 2)
#define UXN			(ULL(1) << 2)
#define PXN			(ULL(1) << 1)
#define CONT_HINT		(ULL(1) << 0)

#define UPPER_ATTRS_SHIFT	(52U)
#define UPPER_ATTRS_WIDTH	(3U)
#define UPPER_ATTRS_MASK	MASK(UPPER_ATTRS)
#define UPPER_ATTRS(x)		(INPLACE(UPPER_ATTRS, x) & (UPPER_ATTRS_MASK))

#define NON_GLOBAL		(UL(1) << 9)
#define ACCESS_FLAG		(UL(1) << 8)
#define NSH			(UL(0x0) << 6)
#define OSH			(UL(0x2) << 6)
#define ISH			(UL(0x3) << 6)

/* Guarded Page bit */
#define GP			(ULL(1) << 50)

#define TABLE_ADDR_MASK		XLAT_TTE_L3_PA_MASK

#define AP2_SHIFT			UL(0x7)
#define AP2_RO				ULL(0x1)
#define AP2_RW				ULL(0x0)

#define AP1_SHIFT			UL(0x6)

/*
 * The following definitions must all be passed to the LOWER_ATTRS() macro to
 * get the right bitmask.
 */
#define AP_RO				(AP2_RO << UL(5))
#define AP_RW				(AP2_RW << UL(5))
#define AP_ACCESS_UNPRIVILEGED		(AP1_ACCESS_UNPRIVILEGED    << UL(4))
#define AP_NO_ACCESS_UNPRIVILEGED	(AP1_NO_ACCESS_UNPRIVILEGED << UL(4))
#define ATTR_NON_CACHEABLE_INDEX	UL(0x2)
#define ATTR_DEVICE_INDEX		UL(0x1)
#define ATTR_IWBWA_OWBWA_NTR_INDEX	UL(0x0)
#define NG_HINT				(ULL(1) << 9)

/* Normal Memory, Outer Write-Through non-transient, Inner Non-cacheable */
#define ATTR_NON_CACHEABLE		MAKE_MAIR_NORMAL_MEMORY(MAIR_NORM_NC, MAIR_NORM_NC)
/* Device-nGnRE */
#define ATTR_DEVICE			MAIR_DEV_NGNRE
/* Normal Memory, Outer Write-Back non-transient, Inner Write-Back non-transient */
#define ATTR_IWBWA_OWBWA_NTR		MAKE_MAIR_NORMAL_MEMORY(MAIR_NORM_WB_NTR_RWA, MAIR_NORM_WB_NTR_RWA)
#define MAIR_ATTR_SET(attr, index)	((attr) << (index << UL(3)))
#define ATTR_INDEX_MASK			U(0x3)
#define ATTR_INDEX_GET(attr)		(((attr) >> UL(2)) & ATTR_INDEX_MASK)

/*
 * Shift values for the attributes fields in a block or page descriptor.
 * See section D4.3.3 in the ARMv8-A ARM (issue B.a).
 */

/* Memory attributes index field, AttrIndx[2:0]. */
#define ATTR_INDEX_SHIFT		2
/* Non-secure bit, NS. */
#define NS_SHIFT			5
/* Shareability field, SH[1:0] */
#define SHAREABILITY_SHIFT		8
/* The Access Flag, AF. */
#define ACCESS_FLAG_SHIFT		10
/* The not global bit, nG. */
#define NOT_GLOBAL_SHIFT		11
/* Non-secure extension bit. Only valid in the EL3 translation regime */
/* Contiguous hint bit. */
#define CONT_HINT_SHIFT			52
/* Execute-never bits, XN. */
#define PXN_SHIFT			53
#define XN_SHIFT			54
#define UXN_SHIFT			XN_SHIFT

#endif /* XLAT_DEFS_PRIVATE_H */
