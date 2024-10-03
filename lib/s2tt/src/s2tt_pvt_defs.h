/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef S2TT_PVT_DEFS
#define S2TT_PVT_DEFS

/*
 * The type of stage 2 translation table entry (s2tte) is defined by:
 * 1. Table level where it resides
 * 2. DESC_TYPE field[1:0]
 * 4. HIPAS field [4:2]
 * 4. RIPAS field [6:5]
 * 5. NS field [55]
 *
 * ======================================================================================
 * s2tte type           level DESC_TYPE[1:0] HIPAS[4:2]    RIPAS[6:5]   NS  OA alignment
 * ======================================================================================
 * unassigned_empty     any   invalid[0]     unassigned[0] empty[0]     0   n/a
 * --------------------------------------------------------------------------------------
 * unassigned_ram       any   invalid[0]     unassigned[0] ram[1]       0   n/a
 * --------------------------------------------------------------------------------------
 * unassigned_destroyed any   invalid[0]     unassigned[0] destroyed[2] 0   n/a
 * --------------------------------------------------------------------------------------
 * assigned_empty       2,3   invalid[0]     assigned[1]   empty[0]     0   to level
 * --------------------------------------------------------------------------------------
 * assigned_ram         3     page[3]        n/a           n/a          0   to level
 *                      2     block[1]       n/a           n/a          0   to level
 * --------------------------------------------------------------------------------------
 * assigned_destroyed   any   invalid[0]     assigned[1]   destroyed[2] 0   n/a
 * ======================================================================================
 * unassigned_ns        any   invalid[0]     unassigned[0] n/a          1   n/a
 * --------------------------------------------------------------------------------------
 * assigned_ns	        3     page[3]        n/a           n/a          1   to level
 *                      2     block[1]       n/a           n/a          1   to level
 * ======================================================================================
 * table              <=2     table[3]       n/a           n/a          n/a to 4K
 * ======================================================================================
 */

#define S2TTE_INVALID_HIPAS_SHIFT	2
#define S2TTE_INVALID_HIPAS_WIDTH	3U
#define S2TTE_INVALID_HIPAS_MASK	MASK(S2TTE_INVALID_HIPAS)

#define S2TTE_INVALID_HIPAS_UNASSIGNED	(INPLACE(S2TTE_INVALID_HIPAS, RMI_UNASSIGNED))
#define S2TTE_INVALID_HIPAS_ASSIGNED	(INPLACE(S2TTE_INVALID_HIPAS, RMI_ASSIGNED))

#define S2TTE_INVALID_RIPAS_SHIFT	5
#define S2TTE_INVALID_RIPAS_WIDTH	2U
#define S2TTE_INVALID_RIPAS_MASK	MASK(S2TTE_INVALID_RIPAS)

#define S2TTE_INVALID_RIPAS_EMPTY	(INPLACE(S2TTE_INVALID_RIPAS, RMI_EMPTY))
#define S2TTE_INVALID_RIPAS_RAM		(INPLACE(S2TTE_INVALID_RIPAS, RMI_RAM))
#define S2TTE_INVALID_RIPAS_DESTROYED	(INPLACE(S2TTE_INVALID_RIPAS, RMI_DESTROYED))

#define S2TTE_NS			(1UL << 55)
#define S2TTE_AF			(1UL << 10)
#define S2TTE_XN			(2UL << 53)

/*
 * Descriptor types
 */
#define S2TT_DESC_TYPE_MASK		3UL
#define S2TTE_Lx_INVALID		0UL
#define S2TTE_L012_BLOCK		1UL
#define S2TTE_L012_TABLE		3UL
#define S2TTE_L3_PAGE			3UL

/* Only 4K pages supported */
#define BLOCK_L2_SIZE		(GRANULE_SIZE * S2TTES_PER_S2TT)

/*
 * The maximum number of bits supported by the RMM for a stage 2 translation
 * output address (including stage 2 table entries) with FEAT_LPA2 is 52 bits.
 */
#define S2TTE_OA_BITS			48UL
#define S2TTE_OA_BITS_LPA2		52UL

/*
 * When FEAT_LPA2 is enabled, the 2 MSB bits of the OA is not contiguous
 * to the rest of the address in the TTE.
 */
#define LPA2_OA_51_50_SHIFT		50U
#define LPA2_OA_51_50_WIDTH		2U

#define LPA2_OA_49_48_SHIFT		48U
#define LPA2_OA_49_48_WIDTH		2U

/* Where the 2 MSB bits of the OA are stored in the TTE */
#define LPA2_S2TTE_51_50_SHIFT		8U
#define LPA2_S2TTE_51_50_WIDTH		(LPA2_OA_51_50_WIDTH)

/*
 * The following constants for the mapping attributes (S2_TTE_MEMATTR_*)
 * assume that HCR_EL2.FWB is set.
 */
#define S2TTE_MEMATTR_SHIFT		2
#define S2TTE_MEMATTR_MASK		(0x7UL << S2TTE_MEMATTR_SHIFT)
#define S2TTE_MEMATTR_FWB_NORMAL_WB	((1UL << 4) | (2UL << 2))
#define S2TTE_MEMATTR_FWB_RESERVED	((1UL << 4) | (0UL << 2))

#define S2TTE_AP_SHIFT			6
#define S2TTE_AP_MASK			(3UL << S2TTE_AP_SHIFT)
#define S2TTE_AP_RW			(3UL << S2TTE_AP_SHIFT)

#define S2TTE_SH_SHIFT			8
#define S2TTE_SH_MASK			(3UL << S2TTE_SH_SHIFT)
#define S2TTE_SH_NS			(0UL << S2TTE_SH_SHIFT)
#define S2TTE_SH_RESERVED		(1UL << S2TTE_SH_SHIFT)
#define S2TTE_SH_OS			(2UL << S2TTE_SH_SHIFT)
#define S2TTE_SH_IS			(3UL << S2TTE_SH_SHIFT)	/* Inner Shareable */

/*
 * When FEAT_LPA2 is enabled, Shareability attributes are stored in VTCR_EL2
 * and they are not part of the S2TTE.
 */
#define S2TTE_ATTRS_LPA2	(S2TTE_MEMATTR_FWB_NORMAL_WB | S2TTE_AP_RW | \
				 S2TTE_AF)
#define S2TTE_ATTRS_LPA2_MASK	(S2TTE_MEMATTR_MASK | S2TTE_AP_MASK | S2TTE_AF)
#define S2TTE_ATTRS		(S2TTE_ATTRS_LPA2 | S2TTE_SH_IS)
#define S2TTE_ATTRS_MASK	(S2TTE_ATTRS_LPA2_MASK | S2TTE_SH_MASK)

/* NS attributes controlled by the host */
#define S2TTE_NS_ATTR_MASK	(S2TTE_MEMATTR_MASK | S2TTE_AP_MASK)

/*
 * Additional NS attributes set by RMM.
 * It does not include the descriptor type.
 */
#define S2TTE_NS_ATTR_RMM	(S2TTE_AF | S2TTE_NS | S2TTE_XN)

/* Descriptor templates */
#define S2TTE_TABLE		S2TTE_L012_TABLE
#define S2TTE_BLOCK		(S2TTE_ATTRS | S2TTE_L012_BLOCK)
#define S2TTE_BLOCK_LPA2	(S2TTE_ATTRS_LPA2 | S2TTE_L012_BLOCK)
#define S2TTE_PAGE		(S2TTE_ATTRS | S2TTE_L3_PAGE)
#define S2TTE_PAGE_LPA2		(S2TTE_ATTRS_LPA2 | S2TTE_L3_PAGE)
#define S2TTE_BLOCK_NS		((S2TTE_NS_ATTR_RMM) | S2TTE_L012_BLOCK)
#define S2TTE_PAGE_NS		((S2TTE_NS_ATTR_RMM) | S2TTE_L3_PAGE)
#define S2TTE_INVALID		S2TTE_Lx_INVALID

/* Maximum number of concatenated tables for the start level */
#define S2TTE_MAX_CONCAT_TABLES		(16U)

#define NR_RTT_LEVELS		(S2TT_PAGE_LEVEL -		\
					S2TT_MIN_STARTING_LEVEL + 1)
#define NR_RTT_LEVELS_LPA2	(S2TT_PAGE_LEVEL -		\
					S2TT_MIN_STARTING_LEVEL_LPA2 + 1)

#endif /* S2TT_PVT_DEFS */
