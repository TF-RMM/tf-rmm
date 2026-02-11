/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch_features.h>
#include <assert.h>
#include <feature.h>
#include <gic.h>
#include <mec.h>
#include <s2tt.h>
#include <simd.h>
#include <smc-handler.h>
#include <smc-rmi.h>
#include <utils_def.h>

/*
 * Indicates whether the DA feature is supported.
 */
/*
 * This is set to 'RMI_FEATURE_FALSE' by rmm_main() calling
 * feature_da_disable() if SMMUs fail to initialise.
 */
static unsigned long feat_da_supported = RMI_FEATURE_TRUE;

unsigned long get_feature_register_0(void)
{
	/* Set S2SZ field */
	unsigned long s2sz = arch_feat_get_pa_width();
	unsigned long feat_reg0 = INPLACE(RMI_FEATURE_REGISTER_0_S2SZ, s2sz);
	struct simd_config simd_cfg = { 0 };

	/*
	 * If FEAT_Debugv8p9 is implemented and 16 or more breakpoints or
	 * watchpoints are implemented, then BRPs and WRPs fields read as
	 * 0b1111 and ID_AA64DFR1_EL1 indicates the number of breakpoints
	 * and watchpoints.
	 */
	unsigned long num_bps = EXTRACT(ID_AA64DFR0_EL1_BRPs, READ_CACHED_REG(id_aa64dfr0_el1));

	if (num_bps == 15UL) {
		num_bps = EXTRACT(ID_AA64DFR1_EL1_BRPs, READ_CACHED_REG(id_aa64dfr1_el1));
		if (num_bps == 0UL) {
			num_bps = 15UL;
		}
	}

	unsigned long num_wps = EXTRACT(ID_AA64DFR0_EL1_WRPs, READ_CACHED_REG(id_aa64dfr0_el1));

	if (num_wps == 15UL) {
		num_wps = EXTRACT(ID_AA64DFR1_EL1_WRPs, READ_CACHED_REG(id_aa64dfr1_el1));
		if (num_wps == 0UL) {
			num_wps = 15UL;
		}
	}

	/* Set LPA2 field. RMM needs both Stage 1 and Stage 2 to support LPA2 */
	if ((is_feat_lpa2_4k_2_present() && is_feat_lpa2_4k_present()) == true) {
		feat_reg0 |=
			INPLACE(RMI_FEATURE_REGISTER_0_LPA2, RMI_FEATURE_TRUE);
	}


	/* RMM supports PMUv3p7+ */
	assert(read_pmu_version() >= ID_AA64DFR0_EL1_PMUv3p7);
	/* TODO: disable PMU temporarily for v2.0 */
#if 0
	/* Set support for PMUv3 */
	feat_reg0 |= INPLACE(RMI_FEATURE_REGISTER_0_PMU_EN,
				RMI_FEATURE_TRUE);

	/* Set number of PMU counters available */
	feat_reg0 |= INPLACE(RMI_FEATURE_REGISTER_0_PMU_NUM_CTRS,
				EXTRACT(PMCR_EL0_N, read_pmcr_el0()));
#endif

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

	return feat_reg0;
}

unsigned long get_feature_register_1(void)
{
	unsigned long feat_reg1;

	/* We only support 4K */
	feat_reg1 = INPLACE(RMI_FEATURE_REGISTER_1_RMI_GRAN_SZ_4K, RMI_FEATURE_TRUE);
	/* Set support for SHA256 and SHA512 hash algorithms */
	feat_reg1 |= INPLACE(RMI_FEATURE_REGISTER_1_HASH_SHA_256,
			    RMI_FEATURE_TRUE) |
			INPLACE(RMI_FEATURE_REGISTER_1_HASH_SHA_512,
			    RMI_FEATURE_TRUE);
	/*
	 * Set the order of the maximum number of RECs which
	 * can be created per Realm.
	 * It is set to the width of 'refcount' field of the granule descriptor.
	 *
	 * The maximum number of RECs is computed as follows:
	 * MAX_RECS = (2 ^ GRN_REFCOUNT_WIDTH) - 1.
	 */
	feat_reg1 |= INPLACE(RMI_FEATURE_REGISTER_1_MAX_RECS_ORDER,
				GRN_REFCOUNT_WIDTH);

	/* FIXME: These values may need to come from FIRME ABI */
	feat_reg1 |= INPLACE(RMI_FEATURE_REGISTER_1_L0GPTSZ, RMI_L0GPTSZ_30BITS);
	feat_reg1 |= INPLACE(RMI_FEATURE_REGISTER_1_PPS, RMI_PPS_48BITS);

	return feat_reg1;
}

unsigned long get_feature_register_2(void)
{
	unsigned long feat_reg2 = 0UL;

	feat_reg2 |= INPLACE(RMI_FEATURE_REGISTER_2_DA_EN, feat_da_supported);
	return feat_reg2;
}

unsigned long get_feature_register_3(void)
{
	unsigned long feat_reg3 = 0;

	if (s2tt_indirect_ap_supported()) {
		feat_reg3 |= INPLACE(RMI_FEATURE_REGISTER_3_RTT_PLANE, RMI_RTT_PLANE_AUX_SINGLE);
		feat_reg3 |= INPLACE(RMI_FEATURE_REGISTER_3_RTT_S2AP_INDIRECT, RMI_FEATURE_TRUE);
	} else {
		feat_reg3 |= INPLACE(RMI_FEATURE_REGISTER_3_RTT_PLANE, RMI_RTT_PLANE_AUX);
	}

	feat_reg3 |= INPLACE(RMI_FEATURE_REGISTER_3_MAX_NUM_AUX_PLANES, MAX_AUX_PLANES);

	return feat_reg3;
}

unsigned long get_feature_register_4(void)
{
	unsigned long feat_reg4 = 0UL;
	unsigned int mec_count;

	/* Get the maximum number of MECs supported by the hardware */
	mec_count = mecid_max();

	/* Report the MEC count (the full 64-bit field is used for MEC_COUNT) */
	feat_reg4 = (unsigned long)mec_count;

	return feat_reg4;
}

void smc_read_feature_register(unsigned long index,
				struct smc_result *res)
{
	res->x[0] = RMI_SUCCESS;

	if (index == RMI_FEATURE_REGISTER_0_INDEX) {
		res->x[1] = get_feature_register_0();
	} else if (index == RMI_FEATURE_REGISTER_1_INDEX) {
		res->x[1] = get_feature_register_1();
	} else if (index == RMI_FEATURE_REGISTER_2_INDEX) {
		res->x[1] = get_feature_register_2();
	} else if (index == RMI_FEATURE_REGISTER_3_INDEX) {
		res->x[1] = get_feature_register_3();
	} else if (index == RMI_FEATURE_REGISTER_4_INDEX) {
		res->x[1] = get_feature_register_4();
	} else {
		res->x[1] = 0UL;
	}
}

void feature_da_disable(void)
{
	feat_da_supported = RMI_FEATURE_FALSE;
}
