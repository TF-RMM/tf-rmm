/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <CppUTest/CommandLineTestRunner.h>
#include <CppUTest/TestHarness.h>

extern "C" {
#include <arch_helpers.h>
#include <debug.h>
#include <host_utils.h>
#include <psci.h>
#include <rsi-logger.h>
#include <smc-rsi.h>
#include <stdlib.h>
#include <string.h>
#include <test_helpers.h>
#include <utils_def.h>
}

#define LOG_SUCCESS	0U
#define LOG_ERROR	1U
#define LOG_RANDOM	2U

TEST_GROUP(rsi_logger_tests) {
	TEST_SETUP()
	{
		test_helpers_init();

		/* Enable the platform with support for multiple PEs */
		test_helpers_rmm_start(true);

		/* Make sure current CPU Id is 0 (primary processor) */
		host_util_set_cpuid(0U);
		test_helpers_expect_assert_fail(false);
	}
	TEST_TEARDOWN()
	{}
};

#if (RSI_LOG_LEVEL > LOG_LEVEL_NONE) && (RSI_LOG_LEVEL <= LOG_LEVEL)
static void rsi_log_test(unsigned int id, unsigned int status)
{
	unsigned long args[10];
	unsigned long regs[5];
	unsigned int i;

	/* Fill input arguments */
	for (i = 0U; i < ARRAY_SIZE(args); i++) {
		args[i] = rand();
	}

	/* Fill output values */
	switch (status) {
	case LOG_SUCCESS:
		regs[0] = RSI_SUCCESS;
		break;
	case LOG_ERROR:
		regs[0] = test_helpers_get_rand_in_range(RSI_ERROR_INPUT, RSI_INCOMPLETE);
		break;
	default:
		regs[0]	= rand();
	}

	for (i = 1U; i < ARRAY_SIZE(regs); i++) {
		regs[i] = rand();
	}

	rsi_log_on_exit(id, args, regs);
}

TEST(rsi_logger_tests, RSI_LOGGER_TC1)
{
	unsigned int status, id;

	for (status = LOG_SUCCESS; status <= LOG_RANDOM; status++) {
		for (id = SMC_RSI_VERSION; id <= SMC_RSI_HOST_CALL; id++) {
			rsi_log_test(id, status);
		}
	}

	rsi_log_test(SMC32_PSCI_FID_MIN, LOG_RANDOM);
	rsi_log_test(SMC64_PSCI_FID_MAX, LOG_RANDOM);
	rsi_log_test(SMC64_PSCI_FID_MAX + rand(), LOG_RANDOM);

	TEST_EXIT;
}
#else
IGNORE_TEST(rsi_logger_tests, RSI_LOGGER_TC1)
{
}
#endif
