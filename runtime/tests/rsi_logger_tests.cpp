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
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <test_helpers.h>
#include <utils_def.h>
}

#define LOG_SUCCESS	0U
#define LOG_ERROR	1U
#define LOG_RANDOM	2U

TEST_GROUP(rsi_logger_tests) {
	FILE *saved_stdout;
	FILE *log_output;

	TEST_SETUP()
	{
		saved_stdout = stdout;
		log_output = NULL;

		test_helpers_init();

		/* Enable the platform with support for multiple PEs */
		test_helpers_rmm_start(true);

		/* Make sure current CPU Id is 0 (primary processor) */
		host_util_set_cpuid(0U);
		test_helpers_expect_assert_fail(false);
	}
	TEST_TEARDOWN()
	{
		stdout = saved_stdout;
		if (log_output != NULL) {
			fclose(log_output);
		}
	}
};

#if (RSI_LOG_LEVEL > LOG_LEVEL_NONE) && (RSI_LOG_LEVEL <= LOG_LEVEL)
static FILE *capture_log(void)
{
	FILE *log_output = tmpfile();

	CHECK(log_output != NULL);
	stdout = log_output;
	return log_output;
}

static void read_log(FILE *log_output, FILE *saved_stdout,
		     char *buf, size_t size)
{
	stdout = saved_stdout;
	CHECK_EQUAL(0, fflush(log_output));
	rewind(log_output);
	size_t count = fread(buf, 1U, size - 1U, log_output);

	CHECK_EQUAL(0, ferror(log_output));
	CHECK(feof(log_output));
	buf[count] = '\0';
}

static void rsi_log_test(unsigned int id, unsigned int status, bool ret_to_rec)
{
	unsigned long args[10];
	unsigned long regs[9];	/* Status and up to eight output values */
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

	rsi_log_on_exit(id, args, regs, ret_to_rec);
}

TEST(rsi_logger_tests, RSI_LOGGER_TC1)
{
	unsigned int status, id;

	for (unsigned int i = 0U; i < 2U; i++) {
		bool ret_to_rec = ((i & 1U) != 0U);

		for (status = LOG_SUCCESS; status <= LOG_RANDOM; status++) {
			for (id = SMC_RSI_VERSION; id <= SMC_RSI_PLANE_SYSREG_WRITE; id++) {
				rsi_log_test(id, status, ret_to_rec);
			}
		}

		rsi_log_test(SMC32_PSCI_FID_MIN, LOG_RANDOM, ret_to_rec);
		rsi_log_test(SMC64_PSCI_FID_MAX, LOG_RANDOM, ret_to_rec);
		rsi_log_test(SMC64_PSCI_FID_MAX + rand(), LOG_RANDOM, ret_to_rec);
	}

	TEST_EXIT;
}

TEST(rsi_logger_tests, suppressed_calls_do_not_read_arguments)
{
	unsigned long regs[] = {RSI_SUCCESS};
	char output[64];

	log_output = capture_log();
	/* Suppressed calls must return before formatting or reading arguments. */
	rsi_log_on_exit(SMC_RSI_MEASUREMENT_READ, NULL, regs, true);
	regs[0] = RSI_INCOMPLETE;
	rsi_log_on_exit(SMC_RSI_ATTEST_TOKEN_CONTINUE, NULL, regs, true);
	/* Dispatch paths must not read return registers either. */
	rsi_log_on_exit(SMC_RSI_HOST_CALL, NULL, NULL, false);
	rsi_log_on_exit(SMC_RSI_ATTEST_TOKEN_CONTINUE, NULL, NULL, false);
	rsi_log_on_exit(SMC_RSI_VDEV_DMA_DISABLE, NULL, NULL, false);
	read_log(log_output, saved_stdout, output, sizeof(output));

	STRCMP_EQUAL("", output);
}

TEST(rsi_logger_tests, logs_errors_and_selected_successes)
{
	unsigned long args[10] = {0UL};
	unsigned long regs[9] = {RSI_SUCCESS};
	char output[512];

	log_output = capture_log();
	rsi_log_on_exit(SMC_RSI_VERSION, args, regs, true);
	regs[0] = RSI_ERROR_STATE;
	rsi_log_on_exit(SMC_RSI_ATTEST_TOKEN_CONTINUE, args, regs, true);
	regs[0] = RSI_ERROR_INPUT;
	rsi_log_on_exit(SMC_RSI_HOST_CALL, args, regs, true);
	regs[0] = RSI_ERROR_DEVICE;
	rsi_log_on_exit(SMC_RSI_VDEV_DMA_DISABLE, args, regs, true);
	read_log(log_output, saved_stdout, output, sizeof(output));

	STRCMP_CONTAINS("SMC_RSI_VERSION", output);
	STRCMP_CONTAINS(" > RSI_SUCCESS 0 0\n", output);
	STRCMP_CONTAINS("SMC_RSI_ATTEST_TOKEN_CONTINUE", output);
	STRCMP_CONTAINS(" > RSI_ERROR_STATE\n", output);
	STRCMP_CONTAINS("SMC_RSI_HOST_CALL", output);
	STRCMP_CONTAINS(" > RSI_ERROR_INPUT\n", output);
	STRCMP_CONTAINS("SMC_RSI_VDEV_DMA_DISABLE", output);
	STRCMP_CONTAINS(" > RSI_ERROR_DEVICE\n", output);
}

TEST(rsi_logger_tests, terminates_unsupported_dispatch_entries)
{
	unsigned long args[10] = {0xdeadbeefUL};
	char output[512];

	log_output = capture_log();
	/* Seed the log buffer to catch stale arguments after an empty entry. */
	rsi_log_on_exit(SMC_RSI_VERSION, args, NULL, false);
	rsi_log_on_exit(SMC64_RSI_FID(0xAU), args, NULL, false);
	rsi_log_on_exit(SMC64_RSI_FID(0x15U), args, NULL, false);
	rsi_log_on_exit(SMC64_RSI_FID(0x1DU), args, NULL, false);
	read_log(log_output, saved_stdout, output, sizeof(output));

	char *entries = strchr(output, '\n');

	CHECK(entries != NULL);
	entries++;
	for (unsigned int i = 0U; i < 3U; i++) {
		const char *name = "SMC_RSI_<unsupported>";

		STRNCMP_EQUAL(name, entries, strlen(name));
		entries += strlen(name);
		while (*entries == ' ') {
			entries++;
		}
		CHECK_EQUAL('\n', *entries);
		entries++;
	}
	STRCMP_EQUAL("", entries);
}

TEST(rsi_logger_tests, logs_non_rsi_fids_and_table_boundaries)
{
	unsigned long args[10] = {0UL};
	unsigned long regs[4] = {SMC_UNKNOWN};
	const unsigned int ids[] = {
		0U, ~0U, SMC_RSI_VERSION - 1U,
		SMC_RSI_PLANE_SYSREG_WRITE + 1U, SMC32_PSCI_FID_MIN
	};
	char output[1024];

	log_output = capture_log();
	for (unsigned int id : ids) {
		rsi_log_on_exit(id, args, regs, true);
	}
	rsi_log_on_exit(SMC64_PSCI_FID_MAX, args, NULL, false);
	read_log(log_output, saved_stdout, output, sizeof(output));

	STRCMP_CONTAINS("SMC_00000000", output);
	STRCMP_CONTAINS("SMC_ffffffff", output);
	STRCMP_CONTAINS("SMC_c400018f", output);
	STRCMP_CONTAINS("SMC_c40001b0", output);
	STRCMP_CONTAINS("PSCI_84000000", output);
	STRCMP_CONTAINS("PSCI_c4000014", output);
	STRCMP_CONTAINS(" > ffffffffffffffff 0 0 0\n", output);
}
#else
IGNORE_TEST(rsi_logger_tests, RSI_LOGGER_TC1)
{
}
#endif
