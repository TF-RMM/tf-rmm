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

unsigned long get_feature_register_0(void)
{
	/* TODO: Announce FEAT_LPA2 through feat_reg0 when supported for S2TTE */

	/* Set S2SZ field */
	unsigned long s2sz = max_ipa_size();
	unsigned long feat_reg0 = INPLACE(RMM_FEATURE_REGISTER_0_S2SZ, s2sz);
	struct simd_config simd_cfg = { 0 };

	/* Set support for SHA256 and SHA512 hash algorithms */
	feat_reg0 |= INPLACE(RMM_FEATURE_REGISTER_0_HASH_SHA_256,
						RMI_FEATURE_TRUE) |
		     INPLACE(RMM_FEATURE_REGISTER_0_HASH_SHA_512,
						RMI_FEATURE_TRUE);

	/* RMM supports PMUv3p7+ */
	assert(read_pmu_version() >= ID_AA64DFR0_EL1_PMUv3p7);

	/* Set support for PMUv3 */
	feat_reg0 |= INPLACE(RMM_FEATURE_REGISTER_0_PMU_EN,
				RMI_FEATURE_TRUE);

	/* Set number of PMU counters available */
	feat_reg0 |= INPLACE(RMM_FEATURE_REGISTER_0_PMU_NUM_CTRS,
				EXTRACT(PMCR_EL0_N, read_pmcr_el0()));

	/* Get CPU simd configuration and set SVE fields if SVE is present */
	(void)simd_get_cpu_config(&simd_cfg);
	if (simd_cfg.sve_en) {
		feat_reg0 |= INPLACE(RMM_FEATURE_REGISTER_0_SVE_EN,
				     RMI_FEATURE_TRUE) |
			     INPLACE(RMM_FEATURE_REGISTER_0_SVE_VL,
				     simd_cfg.sve_vq);
	}

	return feat_reg0;
}

void smc_read_feature_register(unsigned long index,
				struct smc_result *res)
{
	res->x[0] = RMI_SUCCESS;

	if (index == RMM_FEATURE_REGISTER_0_INDEX) {
		res->x[1] = get_feature_register_0();
	} else {
		res->x[1] = 0UL;
	}
}
