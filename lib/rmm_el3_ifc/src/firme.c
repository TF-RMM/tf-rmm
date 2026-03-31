/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <assert.h>
#include <debug.h>
#include <firme.h>
#include <smc.h>
#include <stdint.h>

/* cppcheck-suppress misra-c2012-9.3 */
static const unsigned int supported_firme_service_versions[FIRME_NUM_SERVICES] = {
	[FIRME_BASE_SERVICE_ID] = SUPPORTED_FIRME_BASE_VERSION,
	[FIRME_GM_SERVICE_ID] = SUPPORTED_FIRME_GM_VERSION
};

/* cppcheck-suppress misra-c2012-9.3 */
static const unsigned long firme_abis_masks[FIRME_NUM_SERVICES] = {
	[FIRME_GM_SERVICE_ID] = FIRME_GM_FR0_MASK
};

/* FIRME status variables. */
static unsigned int firme_el3_svc_version[FIRME_NUM_SERVICES] = {0U, 0U};
static unsigned long firme_el3_svc_present_abis[FIRME_NUM_SERVICES] = {0UL, 0UL};

static bool firme_feature_discovery(unsigned int svc_id)
{
	unsigned long res;
	/* coverity[var_decl:SUPPRESS] */
	struct smc_result smc_res;
	unsigned long svc_id_bit = FIRME_BASE_FR1_SVC_BIT(svc_id);
	unsigned long mask;

	assert(svc_id < ARRAY_SIZE(firme_abis_masks));

	mask = firme_abis_masks[svc_id];

	/* Read base service feature reg 1 to see if the service is supported. */
	/* cppcheck-suppress misra-c2012-9.3 */
	struct smc_args smc_args_1 = SMC_ARGS_2(FIRME_BASE_SERVICE_ID, 1U);
	monitor_call_with_arg_res(SMC_FIRME_BASE_FEATURES, &smc_args_1, &smc_res);
	if ((smc_res.x[0] != FIRME_SUCCESS) || ((smc_res.x[1] & svc_id_bit) == 0UL)) {
		return false;
	}

	/* Get service version. */
	res = monitor_call(SMC_FIRME_BASE_VERSION, svc_id, 0UL, 0UL, 0UL, 0UL, 0UL);
	if (res == FIRME_NOT_SUPPORTED) {
		return false;
	}
	firme_el3_svc_version[svc_id] = (unsigned int)res & FIRME_VERSION_MASK;

	/* Check if the feature's version is supported. */
	if (FIRME_VERSION_MAJOR(firme_el3_svc_version[svc_id]) !=
	    FIRME_VERSION_MAJOR(supported_firme_service_versions[svc_id])) {
		return false;
	}

	/*
	 * The feature is supported, so get the supported ABIs.
	 * Supported ABIs are returned as a bitfield in feature register 0 for all
	 * services.
	 */
	/* cppcheck-suppress misra-c2012-9.3 */
	struct smc_args smc_args_2 = SMC_ARGS_2(svc_id, 0U);
	monitor_call_with_arg_res(SMC_FIRME_BASE_FEATURES, &smc_args_2, &smc_res);
	if (smc_res.x[0] != FIRME_SUCCESS) {
		return false;
	}
	firme_el3_svc_present_abis[svc_id] = smc_res.x[1] & mask;

	return true;
}

/*
 * This function queries EL3 for FIRME support and stores the version number
 * and feature capabilities for use by the RMM EL3 interface.
 */
/* cppcheck-suppress misra-c2012-8.7 */
bool firme_init(void)
{
	unsigned long res;

	/* Check FIRME base version support. */
	res = monitor_call(SMC_FIRME_BASE_VERSION, FIRME_BASE_SERVICE_ID,
				0UL, 0UL, 0UL, 0UL, 0UL);
	if (res == SMC_UNKNOWN) {
		INFO("FIRME is not supported by EL3\n");
		return false;
	}

	firme_el3_svc_version[FIRME_BASE_SERVICE_ID] =
			(unsigned int)res & FIRME_VERSION_MASK;

	/* Check that we support this version. */
	if (FIRME_VERSION_MAJOR(firme_el3_svc_version[FIRME_BASE_SERVICE_ID]) !=
	    FIRME_VERSION_MAJOR(SUPPORTED_FIRME_BASE_VERSION)) {
		INFO("FIRME base version 0x%X is not supported\n",
		     firme_el3_svc_version[FIRME_BASE_SERVICE_ID]);
		return false;
	}

	/* Discover features for all services except the base service. */
	for (unsigned int svc_id = 1U; svc_id < FIRME_NUM_SERVICES; svc_id++) {
		if (!firme_feature_discovery(svc_id)) {
			INFO("FIRME service ID 0x%X is not supported\n", svc_id);
		}
	}

	NOTICE("FIRME version 0x%X is supported\n", firme_el3_svc_version[FIRME_BASE_SERVICE_ID]);
	return true;
}

unsigned long get_present_abis(unsigned int service_id)
{
	assert(service_id < FIRME_NUM_SERVICES);

	return firme_el3_svc_present_abis[service_id];
}

/* cppcheck-suppress misra-c2012-8.7 */
uint32_t firme_get_version(unsigned char service_id)
{
	return firme_el3_svc_version[service_id];
}
