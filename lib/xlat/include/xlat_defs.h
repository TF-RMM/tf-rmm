/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 * SPDX-FileCopyrightText: Copyright Arm Limited and Contributors.
 */

/* This file is derived from xlat_table_v2 library in TF-A project */

#ifndef XLAT_DEFS_H
#define XLAT_DEFS_H

#include <arch.h>
#include <utils_def.h>

/*
 * The ARMv8-A architecture allows translation granule sizes of 4KB, 16KB or 64KB.
 *
 * Only 4K granularities are allowed on this library.
 */
#define PAGE_SIZE		(UL(1) << XLAT_GRANULARITY_SIZE_SHIFT)
#define PAGE_SIZE_MASK		(PAGE_SIZE - UL(1))
#define IS_PAGE_ALIGNED(addr)	(((addr) & PAGE_SIZE_MASK) == U(0))

#define XLAT_ENTRY_SIZE_SHIFT	UL(3)	/* Each MMU table entry is 8 bytes */
#define XLAT_ENTRY_SIZE		(UL(1) << XLAT_ENTRY_SIZE_SHIFT)

/* Size of one complete table */
#define XLAT_TABLE_SIZE_SHIFT	XLAT_GRANULARITY_SIZE_SHIFT
#define XLAT_TABLE_SIZE		(UL(1) << XLAT_TABLE_SIZE_SHIFT)

#define XLAT_TABLE_LEVEL_MAX	UL(3)

/* Values for number of entries in each MMU translation table */
#define XLAT_TABLE_ENTRIES_SHIFT (XLAT_TABLE_SIZE_SHIFT - XLAT_ENTRY_SIZE_SHIFT)
#define XLAT_TABLE_ENTRIES	(UL(1) << XLAT_TABLE_ENTRIES_SHIFT)
#define XLAT_TABLE_ENTRIES_MASK	(XLAT_TABLE_ENTRIES - UL(1))

/* Values to convert a memory address to an index into a translation table */
#define L3_XLAT_ADDRESS_SHIFT	XLAT_GRANULARITY_SIZE_SHIFT
#define L2_XLAT_ADDRESS_SHIFT	(L3_XLAT_ADDRESS_SHIFT + XLAT_TABLE_ENTRIES_SHIFT)
#define L1_XLAT_ADDRESS_SHIFT	(L2_XLAT_ADDRESS_SHIFT + XLAT_TABLE_ENTRIES_SHIFT)
#define L0_XLAT_ADDRESS_SHIFT	(L1_XLAT_ADDRESS_SHIFT + XLAT_TABLE_ENTRIES_SHIFT)
#define XLAT_ADDR_SHIFT(level)	(XLAT_GRANULARITY_SIZE_SHIFT + \
		  ((XLAT_TABLE_LEVEL_MAX - (level)) * XLAT_TABLE_ENTRIES_SHIFT))

#define XLAT_BLOCK_SIZE(level)	(UL(1) << XLAT_ADDR_SHIFT(level))
/* Mask to get the bits used to index inside a block of a certain level */
#define XLAT_BLOCK_MASK(level)	(XLAT_BLOCK_SIZE(level) - UL(1))
/* Mask to get the address bits common to a block of a certain table level*/
#define XLAT_ADDR_MASK(level)	(~XLAT_BLOCK_MASK(level))
/*
 * Extract from the given virtual address the index into the given lookup level.
 * This macro assumes the system is using the 4KB translation granule.
 */
#define XLAT_TABLE_IDX(virtual_addr, level)	\
	(((virtual_addr) >> XLAT_ADDR_SHIFT(level)) & ULL(0x1FF))

/* Mask to get the PA given a L3 descriptor entry (4KB granularity) */
#define XLAT_TTE_L3_PA_MASK	ULL(0x0000FFFFFFFFF000)

/*
 * In AArch64 state, the MMU may support 4KB, 16KB and 64KB page
 * granularity. For 4KB granularity (the only one supported by
 * this library), a level 0 table descriptor doesn't support
 * block translation. See section D4.3.1 of the ARMv8-A Architecture
 * Reference Manual (DDI 0487A.k) for more information.
 *
 * The define below specifies the first table level that allows block
 * descriptors.
 */
#define MIN_LVL_BLOCK_DESC	U(1)
#define XLAT_TABLE_LEVEL_MIN	U(0)

/* Mask used to know if an address belongs to a high va region. */
#define HIGH_REGION_MASK	(ULL(0xFFFF) << 52)

/*
 * Define the architectural limits of the virtual address space in AArch64
 * state.
 *
 * TCR.TxSZ is calculated as 64 minus the width of said address space.
 * The value of TCR.TxSZ must be in the range 16 to 48 [1], which means that
 * the virtual address space width must be in the range 48 to 16 bits.
 *
 * [1] See the ARMv8-A Architecture Reference Manual (DDI 0487A.j) for more
 * information:
 * Page 1730: 'Input address size', 'For all translation stages'.
 * and section 12.2.55 in the ARMv8-A Architecture Reference Manual
 * (DDI 0487D.a)
 */
/*
 * Maximum value of TCR_ELx.T(0,1)SZ is 39 for a min VA size of 16 bits.
 * RMM is only supported with FEAT_TTST implemented.
 */
#define MIN_VIRT_ADDR_SPACE_SIZE	(UL(1) << (UL(64) - TCR_TxSZ_MAX))

/* Minimum value of TCR_ELx.T(0,1)SZ is 16, for a VA of 48 bits */
#define MAX_VIRT_ADDR_SPACE_SIZE	(UL(1) << (UL(64) - TCR_TxSZ_MIN))

/*
 * Here we calculate the initial lookup level from the value of the given
 * virtual address space size. For a 4 KB page size,
 * - level 0 supports virtual address spaces of widths 48 to 40 bits;
 * - level 1 from 39 to 31;
 * - level 2 from 30 to 22.
 * - level 3 from 21 to 16.
 *
 * Small Translation Table (Armv8.4-TTST) support allows the starting level
 * of the translation table from 3 for 4KB granularity. See section 12.2.55 in
 * the ARMv8-A Architecture Reference Manual (DDI 0487D.a). In Armv8.3 and below
 * wider or narrower address spaces are not supported. As a result, level 3
 * cannot be used as initial lookup level with 4 KB granularity. See section
 * D4.2.5 in the ARMv8-A Architecture Reference Manual (DDI 0487A.j) for more
 * information.
 *
 * For example, for a 35-bit address space (i.e. virt_addr_space_size ==
 * 1 << 35), TCR.TxSZ will be programmed to (64 - 35) = 29. According to Table
 * D4-11 in the ARM ARM, the initial lookup level for an address space like that
 * is 1.
 *
 * Note that this macro assumes that the given virtual address space size is
 * valid.
 */
#define GET_XLAT_TABLE_LEVEL_BASE(_virt_addr_space_sz)			\
	(((_virt_addr_space_sz) > (ULL(1) << L0_XLAT_ADDRESS_SHIFT))	\
	? 0U								\
	: (((_virt_addr_space_sz) > (ULL(1) << L1_XLAT_ADDRESS_SHIFT))	\
	? 1U								\
	: (((_virt_addr_space_sz) > (ULL(1) << L2_XLAT_ADDRESS_SHIFT))	\
	? 2U : 3U)))

#endif /* XLAT_DEFS_H */
