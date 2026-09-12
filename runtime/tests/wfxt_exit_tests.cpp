/*
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

/*
 * REC exit due to WFI or WFE for the timed variants (FEAT_WFxT).
 *
 * DEN0137 A4.3.4.1: rec_exit.esr.ISS.TI holds the trapped instruction
 * identifier (RYQWST), RN is zero and RV equals TI[1] (RYQWST, 2.0-bet3),
 * and for WFIT/WFET rec_exit.gprs[0] holds the timeout value (RBPYBC).
 * Arm ARM ESR_EL2 WFx syndrome: TI is ISS[1:0], RV is ISS[2], RN is ISS[9:5].
 *
 * These tests drive handle_realm_exit() with a WFIT/WFET syndrome the way
 * exit_esr_tests.cpp drives it with a WFI/WFE syndrome.
 */

#include <CppUTest/CommandLineTestRunner.h>
#include <CppUTest/TestHarness.h>

extern "C" {
#include <arch_features.h>
#include <arch_helpers.h>
#include <esr.h>
#include <exit.h>
#include <host_utils.h>
#include <rec.h>
#include <smc-rmi.h>
#include <string.h>
#include <test_helpers.h>
#include <utils_def.h>
}

namespace {

/* Architectural WFx syndrome fields (Arm ARM, ESR_EL2 WF* ISS encoding). */
#define WFX_ISS_TI_MASK		(0x3UL)
#define WFX_ISS_TI_WFI		(0x0UL)
#define WFX_ISS_TI_WFE		(0x1UL)
#define WFX_ISS_TI_WFIT		(0x2UL)
#define WFX_ISS_TI_WFET		(0x3UL)
#define WFX_ISS_RV_BIT		(1UL << 2)
#define WFX_ISS_RN_SHIFT	(5U)
#define WFX_ISS_RN_MASK		(0x1FUL << WFX_ISS_RN_SHIFT)

#define TEST_TIMEOUT_RN		(7U)
#define TEST_TIMEOUT_VALUE	(0x12345678UL)

struct wfxt_test_context {
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

static void init_context(struct wfxt_test_context *ctx)
{
	(void)memset(ctx, 0, sizeof(*ctx));

	ctx->rec.active_plane_id = PLANE_0_ID;
	ctx->rec.gic_owner = PLANE_0_ID;
	ctx->rec.aux_data.sysregs = &ctx->sysregs[0];
	ctx->rec.realm_info.num_aux_planes = 0U;
	ctx->rec.realm_info.primary_s2_ctx.ipa_bits = GRANULE_SHIFT + 2U;
}

/* Run a Plane 0 WFx trap with the given TI through the real exit handler. */
static void run_wfx_exit(struct wfxt_test_context *ctx, unsigned long ti,
			 bool include_rv = true)
{
	unsigned long raw_esr = ESR_EL2_EC_WFX | MASK(ESR_EL2_IL) | ti;

	if ((ti & 0x2UL) != 0UL) {
		/* Timed variant: RV valid, RN names the timeout register. */
		raw_esr |=
			(unsigned long)TEST_TIMEOUT_RN << WFX_ISS_RN_SHIFT;
		if (include_rv) {
			raw_esr |= WFX_ISS_RV_BIT;
		}
	}

	init_context(ctx);
	ctx->rec.plane[0].regs[TEST_TIMEOUT_RN] = TEST_TIMEOUT_VALUE;

	write_elr_el2(0x1000UL);
	write_esr_el2(raw_esr);

	CHECK_FALSE(handle_realm_exit(&ctx->rec, &ctx->rec_exit,
				      ARM_EXCEPTION_SYNC_LEL));
	UNSIGNED_LONGS_EQUAL(RMI_EXIT_SYNC, ctx->rec_exit.exit_reason);
	UNSIGNED_LONGS_EQUAL(ESR_EL2_EC_WFX, ctx->rec_exit.esr & MASK(ESR_EL2_EC));
	UNSIGNED_LONGS_EQUAL(0x1004UL, read_elr_el2());
}

} /* namespace */

TEST_GROUP(wfxt_exit_tests) {
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

/* Controls: untimed WFI and WFE keep TI, report RV = 0 and no timeout. */
TEST(wfxt_exit_tests, wfi_control_ti_rv_timeout)
{
	struct wfxt_test_context ctx;

	run_wfx_exit(&ctx, WFX_ISS_TI_WFI);
	UNSIGNED_LONGS_EQUAL(WFX_ISS_TI_WFI, ctx.rec_exit.esr & WFX_ISS_TI_MASK);
	UNSIGNED_LONGS_EQUAL(0UL, ctx.rec_exit.esr & WFX_ISS_RV_BIT);
	UNSIGNED_LONGS_EQUAL(0UL, ctx.rec_exit.esr & WFX_ISS_RN_MASK);
	UNSIGNED_LONGS_EQUAL(0UL, ctx.rec_exit.gprs[0]);
}

TEST(wfxt_exit_tests, wfe_control_ti_rv_timeout)
{
	struct wfxt_test_context ctx;

	run_wfx_exit(&ctx, WFX_ISS_TI_WFE);
	UNSIGNED_LONGS_EQUAL(WFX_ISS_TI_WFE, ctx.rec_exit.esr & WFX_ISS_TI_MASK);
	UNSIGNED_LONGS_EQUAL(0UL, ctx.rec_exit.esr & WFX_ISS_RV_BIT);
	UNSIGNED_LONGS_EQUAL(0UL, ctx.rec_exit.esr & WFX_ISS_RN_MASK);
	UNSIGNED_LONGS_EQUAL(0UL, ctx.rec_exit.gprs[0]);
}

/* RYQWST: TI must be preserved for WFIT (value 2). */
TEST(wfxt_exit_tests, wfit_exit_preserves_ti)
{
	struct wfxt_test_context ctx;

	run_wfx_exit(&ctx, WFX_ISS_TI_WFIT);
	UNSIGNED_LONGS_EQUAL(WFX_ISS_TI_WFIT, ctx.rec_exit.esr & WFX_ISS_TI_MASK);
}

/* RYQWST (2.0-bet3): RV is 1 when TI[1] is 1. */
TEST(wfxt_exit_tests, wfit_exit_sets_rv)
{
	struct wfxt_test_context ctx;

	/* RMM derives RV from TI[1], rather than trusting ESR_EL2.ISS.RV. */
	run_wfx_exit(&ctx, WFX_ISS_TI_WFIT, false);
	UNSIGNED_LONGS_EQUAL(WFX_ISS_RV_BIT, ctx.rec_exit.esr & WFX_ISS_RV_BIT);
}

/* RYQWST: RN is zero in the reported syndrome. */
TEST(wfxt_exit_tests, wfit_exit_clears_rn)
{
	struct wfxt_test_context ctx;

	run_wfx_exit(&ctx, WFX_ISS_TI_WFIT);
	UNSIGNED_LONGS_EQUAL(0UL, ctx.rec_exit.esr & WFX_ISS_RN_MASK);
}

/* RBPYBC: gprs[0] contains the timeout value for WFIT. */
TEST(wfxt_exit_tests, wfit_exit_reports_timeout_in_gprs0)
{
	struct wfxt_test_context ctx;

	run_wfx_exit(&ctx, WFX_ISS_TI_WFIT);
	UNSIGNED_LONGS_EQUAL(TEST_TIMEOUT_VALUE, ctx.rec_exit.gprs[0]);
}

/* Same two requirements for WFET (TI value 3). */
TEST(wfxt_exit_tests, wfet_exit_preserves_ti)
{
	struct wfxt_test_context ctx;

	run_wfx_exit(&ctx, WFX_ISS_TI_WFET);
	UNSIGNED_LONGS_EQUAL(WFX_ISS_TI_WFET, ctx.rec_exit.esr & WFX_ISS_TI_MASK);
}

TEST(wfxt_exit_tests, wfet_exit_reports_timeout_in_gprs0)
{
	struct wfxt_test_context ctx;

	run_wfx_exit(&ctx, WFX_ISS_TI_WFET);
	UNSIGNED_LONGS_EQUAL(TEST_TIMEOUT_VALUE, ctx.rec_exit.gprs[0]);
}
