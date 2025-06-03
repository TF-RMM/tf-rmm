/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef EL3_FEAT_STATUS_H
#define EL3_FEAT_STATUS_H

/*
 * Structure holding feature availability bitmasks
 * returned by EL3 via the SMCCC_ARCH_FEATURE_AVAILABILITY
 * smc call.
 */
struct el3_feat_en_status {
	u_register_t scr_bitmask;
	u_register_t cptr_bitmask;
	u_register_t mdcr_bitmask;
	u_register_t mpam3_bitmask;
};

/*
 * Feature offsets in scr_feat_bitmask
 * +--------------------+---------------+
 * | scr_bitmask[59]	| FEAT_FGT2	|
 * +--------------------+---------------+
 * | scr_bitmask[49]	| FEAT_MEC	|
 * +--------------------+---------------+
 * | scr_bitmask[47]	| FEAT_D128	|
 * +--------------------+---------------+
 * | scr_bitmask[45]	| FEAT_S1PIE	|
 * +--------------------+---------------+
 * | scr_bitmask[44]	| FEAT_SCTLR2	|
 * +--------------------+---------------+
 * | scr_bitmask[43]	| FEAT_TCR2	|
 * +--------------------+---------------+
 * | scr_bitmask[42]	| FEAT_THE	|
 * +--------------------+---------------+
 * | scr_bitmask[41]	| FEAT_SME	|
 * +--------------------+---------------+
 * | scr_bitmask[40]	| FEAT_RNG_TRAP	|
 * +--------------------+---------------+
 * | scr_bitmask[39]	| FEAT_GCS	|
 * +--------------------+---------------+
 * | scr_bitmask[38]	| FEAT_HCX	|
 * +--------------------+---------------+
 * | scr_bitmask[27]	| FEAT_FGT	|
 * +--------------------+---------------+
 * | scr_bitmask[26]	| FEAT_MTE2	|
 * +--------------------+---------------+
 * | scr_bitmask[25]	| FEAT_CSV2_2	|
 * +--------------------+---------------+
 */
#define SMC_FEAT_SCR_FGT2_SHIFT		U(59)
#define SMC_FEAT_SCR_MEC_SHIFT		U(49)
#define SMC_FEAT_SCR_D128_SHIFT		U(47)
#define SMC_FEAT_SCR_S1PIE_SHIFT	U(45)
#define SMC_FEAT_SCR_SCTLR2_SHIFT	U(44)
#define SMC_FEAT_SCR_TCR2_SHIFT		U(43)
#define SMC_FEAT_SCR_SME_SHIFT		U(41)
#define SMC_FEAT_SCR_RNG_TRAP_SHIFT	U(40)
#define SMC_FEAT_SCR_GCS_SHIFT		U(39)
#define SMC_FEAT_SCR_HCX_SHIFT		U(38)
#define SMC_FEAT_SCR_FGT_SHIFT		U(27)
#define SMC_FEAT_SCR_MTE2_SHIFT		U(26)
#define SMC_FEAT_SCR_CSV2_2_SHIFT	U(25)

/*
 * Feature offsets in cptr_feat_bitmask
 * +--------------------+---------------+
 * | cptr_bitmask[12]	| FEAT_SME	|
 * +--------------------+---------------+
 * | cptr_bitmask[8]	| FEAT_SVE	|
 * +--------------------+---------------+
 */
#define SMC_FEAT_CPTR_SME_SHIFT		U(12)
#define SMC_FEAT_CPTR_SVE_SHIFT		U(8)

/*
 * Feature offsets in mdcr_feat_bitmask
 * +--------------------+---------------+
 * | mdcr_bitmask[32]	| FEAT_BRBE	|
 * +--------------------+---------------+
 * | mdcr_bitmask[28]	| FEAT_MTPMU	|
 * +--------------------+---------------+
 * | mdcr_bitmask[24]	| FEAT_TRBE	|
 * +--------------------+---------------+
 * | mdcr_bitmask[19]	| FEAT_TRF	|
 * +--------------------+---------------+
 * | mdcr_bitmask[12]	| FEAT_SPE	|
 * +--------------------+---------------+
 * | mdcr_bitmask[6]	| FEAT_PMUv3	|
 * +--------------------+---------------+
 */
#define SMC_FEAT_MDCR_BRBE_SHIFT	U(32)
#define SMC_FEAT_MDCR_MTPMU_SHIFT	U(28)
#define SMC_FEAT_MDCR_TRBE_SHIFT	U(24)
#define SMC_FEAT_MDCR_TRF_SHIFT		U(19)
#define SMC_FEAT_MDCR_SPE_SHIFT		U(12)
#define SMC_FEAT_MDCR_PMUv3_SHIFT	U(6)

/*
 * Feature offsets in mpam_feat_bitmask
 * +--------------------+---------------+
 * | mpam_bitmask[62]	| FEAT_MPAM	|
 * +--------------------+---------------+
 */
#define MPAM3_FEAT_SHIFT		U(62)

#endif /* EL3_FEAT_STATUS_H */
