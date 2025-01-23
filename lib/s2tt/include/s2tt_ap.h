/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef S2TT_AP_H
#define S2TT_AP_H

#include <s2ap_ind.h>

/*
 * Instruction execution permissions when FEAT_XNX is available
 */
#define S2TTE_PERM_XU_XP		(INPLACE(S2TTE_PERM_XN, 0UL))
#define S2TTE_PERM_XU_XNP		(INPLACE(S2TTE_PERM_XN, 1UL))
#define S2TTE_PERM_XNU_XNP		(INPLACE(S2TTE_PERM_XN, 2UL))
#define S2TTE_PERM_XNU_XP		(INPLACE(S2TTE_PERM_XN, 3UL))

/* S2TTE Permission Overlay Index bits */
#define S2TTE_PO_INDEX_SHIFT		UL(59)
#define S2TTE_PO_INDEX_WIDTH		UL(4)

/* S2TTE Permission indirecton Index bits */
#define S2TTE_PI_INDEX_0_SHIFT		UL(6)
#define S2TTE_PI_INDEX_1_SHIFT		UL(51)
#define S2TTE_PI_INDEX_2_SHIFT		UL(53)
#define S2TTE_PI_INDEX_3_SHIFT		UL(54)
#define S2TTE_PI_INDEX_MASK		((1UL << S2TTE_PI_INDEX_0_SHIFT) | \
					 (1UL << S2TTE_PI_INDEX_1_SHIFT) | \
					 (1UL << S2TTE_PI_INDEX_2_SHIFT) | \
					 (1UL << S2TTE_PI_INDEX_3_SHIFT))

/* Possible permission access labels */
#define S2TTE_PERM_LABEL_NO_ACCESS		(S2AP_IND_PERM_NO_ACCESS)
#define S2TTE_PERM_LABEL_RESERVED_1		(S2AP_IND_PERM_RESERVED_1)
#define S2TTE_PERM_LABEL_MRO			(S2AP_IND_PERM_MRO)
#define S2TTE_PERM_LABEL_MRO_TL1		(S2AP_IND_PERM_MRO_TL1)
#define S2TTE_PERM_LABEL_WO			(S2AP_IND_PERM_WO)
#define S2TTE_PERM_LABEL_RESERVED_5		(S2AP_IND_PERM_RESERVED_5)
#define S2TTE_PERM_LABEL_MRO_TL0		(S2AP_IND_PERM_MRO_TL0)
#define S2TTE_PERM_LABEL_MRO_TL01		(S2AP_IND_PERM_MRO_TL01)
#define S2TTE_PERM_LABEL_RO			(S2AP_IND_PERM_RO)
#define S2TTE_PERM_LABEL_RO_uX			(S2AP_IND_PERM_RO_uX)
#define S2TTE_PERM_LABEL_RO_pX			(S2AP_IND_PERM_RO_pX)
#define S2TTE_PERM_LABEL_RO_upX			(S2AP_IND_PERM_RO_upX)
#define S2TTE_PERM_LABEL_RW			(S2AP_IND_PERM_RW)
#define S2TTE_PERM_LABEL_RW_uX			(S2AP_IND_PERM_RW_uX)
#define S2TTE_PERM_LABEL_RW_pX			(S2AP_IND_PERM_RW_pX)
#define S2TTE_PERM_LABEL_RW_upX			(S2AP_IND_PERM_RW_upX)

#define S2TTE_PERM_LABEL_COUNT			(S2AP_IND_PERM_COUNT)
#define S2TTE_PERM_INDEX_COUNT			(S2AP_IND_PERM_IDX_COUNT)

/* Default base permission for protected IPA space */
#define S2TTE_DEF_BASE_PERM_IDX				(S2AP_IND_BASE_PERM_IDX_RW_upX)

/* Default base permission for DEV IPA space */
#define S2TTE_DEV_DEF_BASE_PERM_IDX			(S2AP_IND_BASE_PERM_IDX_RW)

/* Default overlay permission index for Protected IPA space */
#define S2TTE_DEF_PROT_OVERLAY_IDX			(0UL)

/* Default overlay permission index for unprotected IPA space */
#define S2TTE_DEF_UNPROT_OVERLAY_IDX			(S2TTE_PERM_INDEX_COUNT - 1U)

/* get base permission index from s2tte */
static inline unsigned long s2tte_get_pi_index(const struct s2tt_context *s2_ctx,
						unsigned long s2tte)
{
	(void)s2_ctx;

	return	EXTRACT_BIT(S2TTE_PI_INDEX_0, s2tte) |
		(EXTRACT_BIT(S2TTE_PI_INDEX_1, s2tte) << 1U) |
		(EXTRACT_BIT(S2TTE_PI_INDEX_2, s2tte) << 2U) |
		(EXTRACT_BIT(S2TTE_PI_INDEX_3, s2tte) << 3U);
}

/* set base permission index in s2tte */
static inline unsigned long s2tte_set_pi_index(const struct s2tt_context *s2_ctx,
						unsigned long s2tte,
						unsigned long pi_index)
{
	(void)s2_ctx;

	s2tte &= ~S2TTE_PI_INDEX_MASK;

	s2tte |= INPLACE(S2TTE_PI_INDEX_0, pi_index & 1UL) |
		 INPLACE(S2TTE_PI_INDEX_1, (pi_index >> 1U) & 1UL) |
		 INPLACE(S2TTE_PI_INDEX_2, (pi_index >> 2U) & 1UL) |
		 INPLACE(S2TTE_PI_INDEX_3, (pi_index >> 3U) & 1UL);

	return s2tte;
}

/* set overlay permission index in s2tte */
static inline unsigned long s2tte_set_po_index(const struct s2tt_context *s2_ctx,
						unsigned long s2tte,
						unsigned long po_index)
{
	(void)s2_ctx;

	s2tte &= ~MASK(S2TTE_PO_INDEX);
	s2tte |= INPLACE(S2TTE_PO_INDEX, po_index);

	return s2tte;
}

#endif /* S2TT_AP_H */
