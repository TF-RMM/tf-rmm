/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch.h>
#include <arch_features.h>
#include <arch_helpers.h>
#include <assert.h>
#include <el3_feat_status.h>
#include <smc.h>
#include <stdint.h>
#include <utils_def.h>

#define WRITE_EL3_FEAT_EN_STATUS(obj, bitmask, value)	((obj).bitmask = (value))
#define READ_EL3_FEAT_EN_STATUS(obj, bitmask)		((obj).bitmask)

static struct el3_feat_en_status el3_feat_enb_status = {
	.scr_bitmask = UINT64_MAX,
	.cptr_bitmask = UINT64_MAX,
	.mdcr_bitmask = UINT64_MAX,
	.mpam3_bitmask = UINT64_MAX
};

/*
 * SMCCC_ARCH_FEATURE_AVAILABILITY: query EL3 from R-EL2 about the support
 * and availability of architectural features at EL3
 */

void arch_features_query_el3_support(void)
{
	unsigned long val;
	struct smc_result smc_res = {0};

	/* check if arch_feature_availability is supported */
	val = monitor_call(SMCCC_ARCH_FEATURES,
			      SMCCC_ARCH_FEATURE_AVAILABILITY,
			      0UL, 0UL, 0UL, 0UL, 0UL);

	if (val != SMC_SUCCESS) {
		goto smc_failed;
	}
	monitor_call_with_res(SMCCC_ARCH_FEATURE_AVAILABILITY,
			      SCR_EL3_OPCODE,
			      0UL, 0UL, 0UL, 0UL, 0UL,
			      &smc_res);

	if (smc_res.x[0] == SMC_SUCCESS) {
		WRITE_EL3_FEAT_EN_STATUS(el3_feat_enb_status, scr_bitmask, smc_res.x[1]);
	}

	monitor_call_with_res(SMCCC_ARCH_FEATURE_AVAILABILITY,
			      CPTR_EL3_OPCODE,
			      0UL, 0UL, 0UL, 0UL, 0UL,
			      &smc_res);

	if (smc_res.x[0] == SMC_SUCCESS) {
		WRITE_EL3_FEAT_EN_STATUS(el3_feat_enb_status, cptr_bitmask, smc_res.x[1]);
	}

	monitor_call_with_res(SMCCC_ARCH_FEATURE_AVAILABILITY,
			      MDCR_EL3_OPCODE,
			      0UL, 0UL, 0UL, 0UL, 0UL,
			      &smc_res);

	if (smc_res.x[0] == SMC_SUCCESS) {
		WRITE_EL3_FEAT_EN_STATUS(el3_feat_enb_status, mdcr_bitmask, smc_res.x[1]);
	}

	monitor_call_with_res(SMCCC_ARCH_FEATURE_AVAILABILITY,
			      MPAM3_EL3_OPCODE,
			      0UL, 0UL, 0UL, 0UL, 0UL,
			      &smc_res);

	if (smc_res.x[0] != SMC_SUCCESS) {
		WRITE_EL3_FEAT_EN_STATUS(el3_feat_enb_status, mpam3_bitmask, smc_res.x[1]);
	}
	return;

smc_failed:
	return;
}

#ifndef CBMC
/*
 * Return the PA width supported by the current system.
 */
unsigned int arch_feat_get_pa_width(void)
{
	/*
	 * Physical Address ranges supported in the AArch64 Memory Model.
	 * Each array index is a valid PARange [0:3] in ID_AA64MMFR0_EL1.
	 */
	const unsigned int pa_range_bits_arr[] = {
		[0x0] = PARANGE_WIDTH_32BITS,
		[0x1] = PARANGE_WIDTH_36BITS,
		[0x2] = PARANGE_WIDTH_40BITS,
		[0x3] = PARANGE_WIDTH_42BITS,
		[0x4] = PARANGE_WIDTH_44BITS,
		[0x5] = PARANGE_WIDTH_48BITS,
		[0x6] = PARANGE_WIDTH_52BITS
	};

	unsigned long pa_range = EXTRACT(ID_AA64MMFR0_EL1_PARANGE,
					read_id_aa64mmfr0_el1());

	/*
	 * If a valid encoding is not found in the ID reg, default to a
	 * sensible value. This can happen if RMM is running on a version of
	 * Architecture which is not supported yet. If LPA2 is present,
	 * default to 52 bit PA range else to 48 bit PA range. Assume
	 * both Stage 1 and Stage 2 have identical LPA2 support.
	 */
	/* cppcheck-suppress [misra-c2012-17.3] */
	if (pa_range >= ARRAY_SIZE(pa_range_bits_arr)) {
		return (is_feat_lpa2_4k_present() ?
			PARANGE_WIDTH_52BITS : PARANGE_WIDTH_48BITS);
	}

	return pa_range_bits_arr[pa_range];
}
#endif
