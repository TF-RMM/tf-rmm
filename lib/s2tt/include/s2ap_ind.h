/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef S2AP_IND_H
#define S2AP_IND_H

#include <arch_features.h>

/*
 * Indices for S2AP indirect base permissions as per RMM specification.
 * The base permissions corresponding to these indices will be setup as
 * part of s2ap_ind_init().
 */
enum s2ap_ind_base_perm_idx {
	S2AP_IND_BASE_PERM_IDX_NO_ACCESS,
	S2AP_IND_BASE_PERM_IDX_RO,
	S2AP_IND_BASE_PERM_IDX_WO,
	S2AP_IND_BASE_PERM_IDX_RW,
	S2AP_IND_BASE_PERM_IDX_RW_upX,
	S2AP_IND_BASE_PERM_IDX_COUNT
};

/*
 * S2AP Overlay permission values as per Arm ARM. These macros are also used
 * to construct the direct access permisssions encoding labels as well.
 */
#define S2AP_IND_PERM_NO_ACCESS			(0U)
#define S2AP_IND_PERM_RESERVED_1		(1U)
#define S2AP_IND_PERM_MRO			(2U)
#define S2AP_IND_PERM_MRO_TL1			(3U)
#define S2AP_IND_PERM_WO			(4U)
#define S2AP_IND_PERM_RESERVED_5		(5U)
#define S2AP_IND_PERM_MRO_TL0			(6U)
#define S2AP_IND_PERM_MRO_TL01			(7U)
#define S2AP_IND_PERM_RO			(8U)
#define S2AP_IND_PERM_RO_uX			(9U)
#define S2AP_IND_PERM_RO_pX			(10U)
#define S2AP_IND_PERM_RO_upX			(11U)
#define S2AP_IND_PERM_RW			(12U)
#define S2AP_IND_PERM_RW_uX			(13U)
#define S2AP_IND_PERM_RW_pX			(14U)
#define S2AP_IND_PERM_RW_upX			(15U)

/* Number of different permission values */
#define S2AP_IND_PERM_COUNT			(16U)

/*
 * Maximum number of Base or Overlay indices for indirect encodings as per
 * Arm ARM. Note that Base permission Index is further limited by
 * S2AP_BASE_PERM_INDEX_COUNT.
 */
#define S2AP_IND_PERM_IDX_COUNT			(16U)

/*
 * Maximum permitted overlay index for protected mappings.
 */
#define S2AP_NUM_PERM_OVERLAY_INDICES		(S2AP_IND_PERM_IDX_COUNT - 1U)

/*
 * S2AP Base permission values as per the RMM specification. These macros
 * are used to construct the direct access permissions based on S2AP Base
 * Indirection Indexes.
 */
#define S2AP_IND_PERM_BASE_NO_ACCESS		(S2AP_IND_BASE_PERM_IDX_NO_ACCESS)
#define S2AP_IND_PERM_BASE_RO			(S2AP_IND_BASE_PERM_IDX_RO)
#define S2AP_IND_PERM_BASE_WO			(S2AP_IND_BASE_PERM_IDX_WO)
#define S2AP_IND_PERM_BASE_RW			(S2AP_IND_BASE_PERM_IDX_RW)
#define S2AP_IND_PERM_BASE_RW_upX		(S2AP_IND_BASE_PERM_IDX_RW_upX)


/*
 * Size in bits and mask of the Permission Indirection Index value.
 */
#define S2AP_PII_WIDTH				(4U)
#define S2AP_PII_MASK				((UL(1) << S2AP_PII_WIDTH) - UL(1))

/*
 * Extract the access permission value given a permission indirection
 * register and an index.
 */
#define S2AP_IND_GET_PERM_VALUE(_reg, _index)				\
	(((_reg) >> ((unsigned long)(_index) * S2AP_PII_WIDTH)) & S2AP_PII_MASK)

static inline bool s2ap_is_base_perm_index_valid(unsigned long index)
{
	return !!(index < (unsigned int)S2AP_IND_BASE_PERM_IDX_COUNT);
}

static inline bool s2ap_is_ovrl_perm_index_valid(unsigned long index)
{
	return !!(index < S2AP_NUM_PERM_OVERLAY_INDICES);
}

/*
 * Update the Access Permission @perm[@index] with the value @perm.
 */
static inline unsigned long s2ap_set_overlay_perm(unsigned long reg,
						  unsigned int index,
						  unsigned long perm)
{
	assert(index < S2AP_IND_PERM_IDX_COUNT);
	assert(perm < S2AP_IND_PERM_COUNT);

	reg &= ~(S2AP_PII_MASK << ((unsigned long)S2AP_PII_WIDTH * index));
	perm = (perm << ((unsigned long)S2AP_PII_WIDTH * index));

	return reg | perm;
}

/*
 * Initialize the fixed Base Stage 2 Access Permissions.
 */
static inline void s2ap_ind_perm_init(void)
{
	unsigned long base_perms = (
		((unsigned long)S2AP_IND_PERM_NO_ACCESS <<
			((unsigned long)S2AP_IND_BASE_PERM_IDX_NO_ACCESS * S2AP_PII_WIDTH)) |
		((unsigned long)S2AP_IND_PERM_RO <<
			((unsigned long)S2AP_IND_BASE_PERM_IDX_RO * S2AP_PII_WIDTH)) |
		((unsigned long)S2AP_IND_PERM_WO <<
			((unsigned long)S2AP_IND_BASE_PERM_IDX_WO * S2AP_PII_WIDTH)) |
		((unsigned long)S2AP_IND_PERM_RW <<
			((unsigned long)S2AP_IND_BASE_PERM_IDX_RW * S2AP_PII_WIDTH)) |
		((unsigned long)S2AP_IND_PERM_RW_upX <<
			((unsigned long)S2AP_IND_BASE_PERM_IDX_RW_upX * S2AP_PII_WIDTH))
	);


	if (are_feat_s2pie_and_s2poe_present()) {
		/*
		 * There is no need to call isb() after configuring s2pir_el2
		 * as the boot sequence will synchronize this register
		 * update before it is used.
		 */
		write_s2pir_el2(base_perms);
	}
}

#endif /* S2AP_IND_H */
