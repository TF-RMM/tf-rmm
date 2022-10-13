/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch_features.h>
#include <assert.h>
#include <feature.h>
#include <smc-handler.h>
#include <smc-rmi.h>
#include <status.h>

#define RMM_FEATURE_MIN_IPA_SIZE		PARANGE_0000_WIDTH

static unsigned long get_feature_register_0(void)
{
	/* Set S2SZ field */
	unsigned long s2sz = arch_feat_get_pa_width();
	unsigned long feat_reg0 = INPLACE(RMM_FEATURE_REGISTER_0_S2SZ, s2sz);

	/* Set LPA2 field */
	if (is_feat_lpa2_4k_present()) {
		feat_reg0 |= INPLACE(RMM_FEATURE_REGISTER_0_LPA2, RMI_LPA2);
	}

	/* Set support for SHA256 and SHA512 hash algorithms */
	feat_reg0 |= INPLACE(RMM_FEATURE_REGISTER_0_HASH_SHA_256, 1);
	feat_reg0 |= INPLACE(RMM_FEATURE_REGISTER_0_HASH_SHA_512, 1);

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
	    !is_feat_lpa2_4k_present()) {
		return false;
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
