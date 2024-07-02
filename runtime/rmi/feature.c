/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch_features.h>
#include <assert.h>
#include <feature.h>
#include <gic.h>
#include <s2tt.h>
#include <simd.h>
#include <smc-handler.h>
#include <smc-rmi.h>
#include <utils_def.h>

unsigned long get_feature_register_0(void)
{
	/* Set S2SZ field */
	unsigned long s2sz = arch_feat_get_pa_width();
	unsigned long feat_reg0 = INPLACE(RMI_FEATURE_REGISTER_0_S2SZ, s2sz);
	unsigned long num_bps = EXTRACT(ID_AA64DFR0_EL1_BRPs, read_id_aa64dfr0_el1());
	unsigned long num_wps = EXTRACT(ID_AA64DFR0_EL1_WRPs, read_id_aa64dfr0_el1());
	struct simd_config simd_cfg = { 0 };

	/* Set LPA2 field. RMM needs both Stage 1 and Stage 2 to support LPA2 */
	if ((is_feat_lpa2_4k_2_present() && is_feat_lpa2_4k_present()) == true) {
		feat_reg0 |=
			INPLACE(RMI_FEATURE_REGISTER_0_LPA2, RMI_FEATURE_TRUE);
	}

	/* Set support for SHA256 and SHA512 hash algorithms */
	feat_reg0 |= INPLACE(RMI_FEATURE_REGISTER_0_HASH_SHA_256,
						RMI_FEATURE_TRUE) |
		     INPLACE(RMI_FEATURE_REGISTER_0_HASH_SHA_512,
						RMI_FEATURE_TRUE);

	/* RMM supports PMUv3p7+ */
	assert(read_pmu_version() >= ID_AA64DFR0_EL1_PMUv3p7);

	/* Set support for PMUv3 */
	feat_reg0 |= INPLACE(RMI_FEATURE_REGISTER_0_PMU_EN,
				RMI_FEATURE_TRUE);

	/* Set number of PMU counters available */
	feat_reg0 |= INPLACE(RMI_FEATURE_REGISTER_0_PMU_NUM_CTRS,
				EXTRACT(PMCR_EL0_N, read_pmcr_el0()));

	/*
	 * If FEAT_Debugv8p9 is implemented and 16 or more breakpoints or
	 * watchpoints are implemented, then BRPs and WRPs fields read as
	 * 0b1111 and ID_AA64DFR1_EL1 indicates the number of breakpoints
	 * and watchpoints.
	 */
	if (num_bps == 15UL) {
		num_bps = EXTRACT(ID_AA64DFR1_EL1_BRPs, read_id_aa64dfr1_el1());
		if (num_bps == 0UL) {
			num_bps = 15UL;
		}
	}

	if (num_wps == 15UL) {
		num_wps = EXTRACT(ID_AA64DFR1_EL1_WRPs, read_id_aa64dfr1_el1());
		if (num_wps == 0UL) {
			num_wps = 15UL;
		}
	}

	/* Set number of breakpoints and watchpoints supported, minus 1 */
	feat_reg0 |= (INPLACE(RMI_FEATURE_REGISTER_0_NUM_BPS, num_bps) |
			INPLACE(RMI_FEATURE_REGISTER_0_NUM_WPS, num_wps));

	/* Get CPU simd configuration and set SVE fields if SVE is present */
	(void)simd_get_cpu_config(&simd_cfg);
	if (simd_cfg.sve_en) {
		feat_reg0 |= INPLACE(RMI_FEATURE_REGISTER_0_SVE_EN,
				     RMI_FEATURE_TRUE) |
			     INPLACE(RMI_FEATURE_REGISTER_0_SVE_VL,
				     simd_cfg.sve_vq);
	}

	/* Set number of List registers implemented, minus 1 */
	feat_reg0 |= INPLACE(RMI_FEATURE_REGISTER_0_GICV3_NUM_LRS,
				gic_vgic_get_num_lrs());

	/*
	 * Set the order of the maximum number of RECs which
	 * can be created per Realm.
	 * It is set to the width of 'refcount' field of the granule descriptor.
	 *
	 * The maximum number of RECs is computed as follows:
	 * MAX_RECS = (2 ^ GRN_REFCOUNT_WIDTH) - 1.
	 */
	feat_reg0 |= INPLACE(RMI_FEATURE_REGISTER_0_MAX_RECS_ORDER,
				GRN_REFCOUNT_WIDTH);

#ifdef RMM_V1_1
	feat_reg0 |= INPLACE(RMI_FEATURE_REGISTER_0_DA_EN, RMI_FEATURE_TRUE);
#else
	feat_reg0 |= INPLACE(RMI_FEATURE_REGISTER_0_DA_EN, RMI_FEATURE_FALSE);
#endif

	return feat_reg0;
}

void smc_read_feature_register(unsigned long index,
				struct smc_result *res)
{
	res->x[0] = RMI_SUCCESS;

	if (index == RMI_FEATURE_REGISTER_0_INDEX) {
		res->x[1] = get_feature_register_0();
	} else {
		res->x[1] = 0UL;
	}
}
