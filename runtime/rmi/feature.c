/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch_features.h>
#include <assert.h>
#include <feature.h>
#include <simd.h>
#include <smc-handler.h>
#include <smc-rmi.h>
#include <status.h>
#include <table.h>
#include <utils_def.h>

#define RMM_FEATURE_MIN_IPA_SIZE	PARANGE_0000_WIDTH

static unsigned long get_feature_register_0(void)
{
	/* TODO: Announce FEAT_LPA2 through feat_reg0 when supported for S2TTE */

	/* Set S2SZ field */
	unsigned long s2sz = max_ipa_size();
	unsigned long feat_reg0 = INPLACE(RMM_FEATURE_REGISTER_0_S2SZ, s2sz);

	/* Set support for SHA256 and SHA512 hash algorithms */
	feat_reg0 |= INPLACE(RMM_FEATURE_REGISTER_0_HASH_SHA_256,
				RMI_FEATURE_TRUE);
	feat_reg0 |= INPLACE(RMM_FEATURE_REGISTER_0_HASH_SHA_512,
				RMI_FEATURE_TRUE);

	/* RMM supports PMUv3p7+ */
	assert(read_pmu_version() >= ID_AA64DFR0_EL1_PMUv3p7);

	/* Set support for PMUv3 */
	feat_reg0 |= INPLACE(RMM_FEATURE_REGISTER_0_PMU_EN,
				RMI_FEATURE_TRUE);

	/* Set number of PMU counters available */
	feat_reg0 |= INPLACE(RMM_FEATURE_REGISTER_0_PMU_NUM_CTRS,
				EXTRACT(PMCR_EL0_N, read_pmcr_el0()));

	/* Set SVE fields */
	if (is_feat_sve_present()) {
		feat_reg0 |= INPLACE(RMM_FEATURE_REGISTER_0_SVE_EN,
				     RMI_FEATURE_TRUE);

		feat_reg0 |= INPLACE(RMM_FEATURE_REGISTER_0_SVE_VL,
				     simd_sve_get_max_vq());
	}

	return feat_reg0;
}

void smc_read_feature_register(unsigned long index,
				struct smc_result *ret_struct)
{
	switch (index) {
	case RMM_FEATURE_REGISTER_0_INDEX:
		ret_struct->x[0] = RMI_SUCCESS;
		ret_struct->x[1] = get_feature_register_0();
		break;
	default:
		ret_struct->x[0] = RMI_ERROR_INPUT;
		ret_struct->x[1] = 0UL;
	}
}

static bool validate_feature_register_0(unsigned long value)
{
	unsigned long feat_reg0 = get_feature_register_0();
	unsigned long s2sz = EXTRACT(RMM_FEATURE_REGISTER_0_S2SZ, value);

	/* Validate S2SZ field */
	if ((s2sz < RMM_FEATURE_MIN_IPA_SIZE) ||
	    (s2sz > EXTRACT(RMM_FEATURE_REGISTER_0_S2SZ, feat_reg0))) {
		return false;
	}

	/* Validate LPA2 flag */
	if ((EXTRACT(RMM_FEATURE_REGISTER_0_LPA2, value) == RMI_LPA2) &&
	    (EXTRACT(RMM_FEATURE_REGISTER_0_LPA2, feat_reg0) == RMI_NO_LPA2)) {
		return false;
	}

	/*
	 * Skip validation of RMM_FEATURE_REGISTER_0_PMU_EN flag
	 * as RMM always assumes that PMUv3p7+ is present.
	 */

	/* Validate number of PMU counters if PMUv3 is enabled */
	if ((EXTRACT(RMM_FEATURE_REGISTER_0_PMU_EN, value) ==
					RMI_FEATURE_TRUE) &&
	    (EXTRACT(RMM_FEATURE_REGISTER_0_PMU_NUM_CTRS, value) !=
	     EXTRACT(RMM_FEATURE_REGISTER_0_PMU_NUM_CTRS, feat_reg0))) {
		return false;
	}

	/* Validate SVE flag */
	if ((EXTRACT(RMM_FEATURE_REGISTER_0_SVE_EN, value) == RMI_FEATURE_TRUE)) {
		if (!is_feat_sve_present()) {
			return false;
		}

		/* Validate SVE_VL value */
		if (EXTRACT(RMM_FEATURE_REGISTER_0_SVE_VL, value) >
		    simd_sve_get_max_vq()) {
			return false;
		}
	}

	return true;
}

bool validate_feature_register(unsigned long index, unsigned long value)
{
	switch (index) {
	case RMM_FEATURE_REGISTER_0_INDEX:
		return validate_feature_register_0(value);
	default:
		assert(false);
		return false;
	}
}
