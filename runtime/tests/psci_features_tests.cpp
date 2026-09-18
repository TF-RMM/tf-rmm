/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <CppUTest/CommandLineTestRunner.h>
#include <CppUTest/TestHarness.h>

extern "C" {
#include <arch_features.h>
#include <arch_helpers.h>
#include <esr.h>
#include <exit.h>
#include <host_utils.h>
#include <psci.h>
#include <rec.h>
#include <smc-rmi.h>
#include <smc.h>
#include <string.h>
#include <test_helpers.h>
#include <utils_def.h>
}

/*
 * PSCI_FEATURES function discovery.
 *
 * DEN0137 2.0-bet3 B6.3.5.3 (func_ok): PSCI_FEATURES returns PSCI_SUCCESS
 * for a supported PSCI function. DEN0022 (PSCI) 5.15.2 requires
 * NOT_SUPPORTED only for functions that are not implemented, and Table 18
 * lists PSCI_VERSION as mandatory from PSCI 1.0, which DEN0137 RTFCVF
 * requires the RMM to implement (version 1.1 or later).
 *
 * These tests drive handle_realm_exit() with an SMC syndrome the way
 * exit_esr_tests.cpp drives it with abort and WFx syndromes: Plane 0
 * issues the PSCI call, the RMM handles it internally and returns to the
 * Realm with the result in X0.
 */

/* PSCI_CPU_FREEZE (DEN0022 5.1.1) is not implemented by the RMM. */
#define TEST_PSCI_FID_UNSUPPORTED	SMC32_PSCI_CPU_FREEZE

struct psci_test_context {
	STRUCT_TYPE sysreg_state sysregs[1];
	struct rec rec;
	struct rmi_rec_exit rec_exit;
};

static void init_syndrome_sysregs(void)
{
	LONGS_EQUAL(0, host_util_set_default_sysreg_cb((char *)"far_el2", 0UL));
	LONGS_EQUAL(0, host_util_set_default_sysreg_cb((char *)"hpfar_el2", 0UL));
	LONGS_EQUAL(0, host_util_set_default_sysreg_cb((char *)"par_el1", 0UL));
	LONGS_EQUAL(0, host_util_set_default_sysreg_cb((char *)"spsr_el2", 0UL));
}

static void init_context(struct psci_test_context *ctx)
{
	(void)memset(ctx, 0, sizeof(*ctx));

	ctx->rec.active_plane_id = PLANE_0_ID;
	ctx->rec.gic_owner = PLANE_0_ID;
	ctx->rec.aux_data.sysregs = &ctx->sysregs[0];
	ctx->rec.realm_info.num_aux_planes = 0U;
	ctx->rec.realm_info.primary_s2_ctx.ipa_bits = GRANULE_SHIFT + 2U;
}

/*
 * Run a Plane 0 PSCI call through the real exit handler and return the
 * value the Realm reads back in X0. Seed X1..X3 with the call arguments
 * and X4 with a marker to detect writes beyond the result registers.
 */
static unsigned long run_psci_call(struct psci_test_context *ctx,
				   unsigned long fid, unsigned long arg1)
{
	init_context(ctx);
	ctx->rec.plane[0].regs[0] = fid;
	ctx->rec.plane[0].regs[1] = arg1;
	ctx->rec.plane[0].regs[4] = 0xa5a5a5a5UL;

	write_elr_el2(0x1000UL);
	write_esr_el2(ESR_EL2_EC_SMC | MASK(ESR_EL2_IL));

	/* The RMM handles the call and returns to the Realm. */
	CHECK_TRUE(handle_realm_exit(&ctx->rec, &ctx->rec_exit,
				     ARM_EXCEPTION_SYNC_LEL));
	UNSIGNED_LONGS_EQUAL(0x1004UL, read_elr_el2());
	UNSIGNED_LONGS_EQUAL(0xa5a5a5a5UL, ctx->rec.plane[0].regs[4]);

	return ctx->rec.plane[0].regs[0];
}

TEST_GROUP(psci_features_tests) {
	TEST_SETUP()
	{
		test_helpers_init();
		test_helpers_rmm_start(true);
		host_util_set_cpuid(0U);
		test_helpers_expect_assert_fail(false);
		init_syndrome_sysregs();
	}

	TEST_TEARDOWN()
	{}
};

/* Control: the RMM implements PSCI_VERSION and reports PSCI 1.1. */
TEST(psci_features_tests, psci_version_reports_1_1)
{
	struct psci_test_context ctx;
	unsigned long ret = run_psci_call(&ctx, SMC32_PSCI_VERSION, 0UL);

	UNSIGNED_LONGS_EQUAL(0x10001UL, ret);
}

/* Control: a function the RMM implements is reported as supported. */
TEST(psci_features_tests, features_reports_cpu_on_supported)
{
	struct psci_test_context ctx;
	unsigned long ret = run_psci_call(&ctx, SMC32_PSCI_FEATURES,
					  SMC64_PSCI_CPU_ON);

	UNSIGNED_LONGS_EQUAL(PSCI_RETURN_SUCCESS, ret);
}

/* Control: a function the RMM does not implement is NOT_SUPPORTED. */
TEST(psci_features_tests, features_reports_cpu_freeze_unsupported)
{
	struct psci_test_context ctx;
	unsigned long ret = run_psci_call(&ctx, SMC32_PSCI_FEATURES,
					  TEST_PSCI_FID_UNSUPPORTED);

	UNSIGNED_LONGS_EQUAL(PSCI_RETURN_NOT_SUPPORTED, ret);
}

/*
 * B6.3.5.3 func_ok: PSCI_VERSION is implemented by this RMM (see the
 * control above), so PSCI_FEATURES must report it as supported.
 */
TEST(psci_features_tests, features_reports_psci_version_supported)
{
	struct psci_test_context ctx;
	unsigned long ret = run_psci_call(&ctx, SMC32_PSCI_FEATURES,
					  SMC32_PSCI_VERSION);

	UNSIGNED_LONGS_EQUAL(PSCI_RETURN_SUCCESS, ret);
}
