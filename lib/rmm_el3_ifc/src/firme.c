/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <firme.h>
#include <smc.h>
#include <stdint.h>

/* Supported FIRME service versions */
#define SUPPORTED_FIRME_BASE_VERSION	0x10000U /* 1.0 */
#define SUPPORTED_FIRME_GM_VERSION	0x10000U /* 1.0 */

/* FIRME status variables. */
static bool firme_gpi_set_present;
static unsigned int firme_service_version[6] = {0U, 0U, 0U, 0U, 0U, 0U};

/*
 * This function queries EL3 for FIRME support and stores the version number
 * and feature capabilities for use by the RMM EL3 interface.
 */
/* cppcheck-suppress misra-c2012-8.7 */
bool firme_init(void)
{
	unsigned long res;
	/* coverity[var_decl:SUPPRESS] */
	struct smc_result smc_res;

	/* Check FIRME base version support. */
	res = monitor_call(SMC_FIRME_BASE_VERSION, FIRME_BASE_SERVICE_ID, 0UL, 0UL, 0UL, 0UL, 0UL);
	if (res == SMC_UNKNOWN) {
		return false;
	} else {
		firme_service_version[FIRME_BASE_SERVICE_ID] = (unsigned int)res & FIRME_VERSION_MASK;
	}

	/* Check that we support this version. */
	if (FIRME_VERSION_MAJOR(firme_service_version[FIRME_BASE_SERVICE_ID]) !=
	    FIRME_VERSION_MAJOR(SUPPORTED_FIRME_BASE_VERSION)) {
		return false;
	}

	/* Read base service feature reg 1 to see if GM is supported. */
	/* cppcheck-suppress misra-c2012-9.3 */
	struct smc_args smc_args_1 = SMC_ARGS_2(FIRME_BASE_SERVICE_ID, 1U);
	monitor_call_with_arg_res(SMC_FIRME_BASE_FEATURES, &smc_args_1, &smc_res);
	if ((smc_res.x[0] != FIRME_SUCCESS) || ((smc_res.x[1] & FIRME_BASE_FR1_GM_SVC_BIT) == 0UL)) {
		return false;
	}

	/* Get GM version. */
	res = monitor_call(SMC_FIRME_BASE_VERSION, FIRME_GM_SERVICE_ID, 0UL, 0UL, 0UL, 0UL, 0UL);
	if (res == FIRME_NOT_SUPPORTED) {
		return false;
	} else {
		firme_service_version[FIRME_GM_SERVICE_ID] = (unsigned int)res & FIRME_VERSION_MASK;
	}

	/* Check if GM version is supported. */
	if (FIRME_VERSION_MAJOR(firme_service_version[FIRME_GM_SERVICE_ID]) !=
	    FIRME_VERSION_MAJOR(SUPPORTED_FIRME_GM_VERSION)) {
		return false;
	}

	/* GM is supported, so make sure GPI_SET is present. */
	/* cppcheck-suppress misra-c2012-9.3 */
	struct smc_args smc_args_2 = SMC_ARGS_2(FIRME_GM_SERVICE_ID, 0U);
	monitor_call_with_arg_res(SMC_FIRME_BASE_FEATURES, &smc_args_2, &smc_res);
	if ((smc_res.x[0] != FIRME_SUCCESS) || ((smc_res.x[1] & FIRME_GM_FRO_GPI_SET_BIT) == 0UL)) {
		return false;
	}
	firme_gpi_set_present = true;

	return true;
}

/* cppcheck-suppress misra-c2012-8.7 */
bool firme_supports_gpi_set(void)
{
	return firme_gpi_set_present;
}

/* cppcheck-suppress misra-c2012-8.7 */
uint32_t firme_get_version(unsigned char service_id)
{
	return firme_service_version[service_id];
}
