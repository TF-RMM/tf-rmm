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
 * Each test injects a Plane 0 WFx syndrome into handle_realm_exit(). The
 * shared helper checks that execution exits to the Host with RMI_EXIT_SYNC,
 * preserves the WFx exception class and advances the PC past the trapped
 * instruction. Individual tests check instruction identification, syndrome
 * sanitization and timeout reporting, including XZR and the last saved GPR.
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
#define TEST_TIMEOUT_64BIT	(0xfedcba9876543210UL)

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
			 bool include_rv = true,
			 unsigned int timeout_rn = TEST_TIMEOUT_RN,
			 unsigned long timeout_value = TEST_TIMEOUT_VALUE)
{
	unsigned long raw_esr = ESR_EL2_EC_WFX | MASK(ESR_EL2_IL) | ti;
	unsigned int i;

	if ((ti & 0x2UL) != 0UL) {
		/* Timed variant: RV valid, RN names the timeout register. */
		raw_esr |= (unsigned long)timeout_rn << WFX_ISS_RN_SHIFT;
		if (include_rv) {
			raw_esr |= WFX_ISS_RV_BIT;
		}
	}

	init_context(ctx);
	if (timeout_rn < 31U) {
		ctx->rec.plane[0].regs[timeout_rn] = timeout_value;
	}
	/* The state after X30 must not be mistaken for XZR's value. */
	ctx->rec.plane[0].pstate = SPSR_EL2_MODE_EL1h;
	if ((ti & 0x2UL) != 0UL) {
		/* Require an explicit timeout write, including for XZR. */
		ctx->rec_exit.gprs[0] = ~timeout_value;
	}

	write_elr_el2(0x1000UL);
	write_esr_el2(raw_esr);

	CHECK_FALSE(handle_realm_exit(&ctx->rec, &ctx->rec_exit,
				      ARM_EXCEPTION_SYNC_LEL));
	UNSIGNED_LONGS_EQUAL(RMI_EXIT_SYNC, ctx->rec_exit.exit_reason);
	UNSIGNED_LONGS_EQUAL(ESR_EL2_EC_WFX, ctx->rec_exit.esr & MASK(ESR_EL2_EC));
	UNSIGNED_LONGS_EQUAL(0UL, ctx->rec_exit.far);
	UNSIGNED_LONGS_EQUAL(0UL, ctx->rec_exit.hpfar);
	UNSIGNED_LONGS_EQUAL(0UL, ctx->rec_exit.rtt_tree);
	LONGS_EQUAL(0L, ctx->rec_exit.rtt_level);
	for (i = 1U; i < REC_EXIT_NR_GPRS; ++i) {
		UNSIGNED_LONGS_EQUAL(0UL, ctx->rec_exit.gprs[i]);
	}
	UNSIGNED_LONGS_EQUAL(0UL, ctx->rec_exit.ripas_base);
	UNSIGNED_LONGS_EQUAL(0UL, ctx->rec_exit.ripas_top);
	UNSIGNED_LONGS_EQUAL(0UL, ctx->rec_exit.ripas_value);
	UNSIGNED_LONGS_EQUAL(0UL, ctx->rec_exit.s2ap_base);
	UNSIGNED_LONGS_EQUAL(0UL, ctx->rec_exit.s2ap_top);
	UNSIGNED_LONGS_EQUAL(0UL, ctx->rec_exit.vdev_id_1);
	UNSIGNED_LONGS_EQUAL(0UL, ctx->rec_exit.vdev_id_2);
	UNSIGNED_LONGS_EQUAL(0UL, ctx->rec_exit.dev_mem_base);
	UNSIGNED_LONGS_EQUAL(0UL, ctx->rec_exit.dev_mem_top);
	UNSIGNED_LONGS_EQUAL(0UL, ctx->rec_exit.dev_mem_pa);
	UNSIGNED_LONGS_EQUAL(0UL, ctx->rec_exit.imm);
	UNSIGNED_LONGS_EQUAL(0UL, ctx->rec_exit.plane);
	UNSIGNED_LONGS_EQUAL(0x1004UL, read_elr_el2());
}

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

/*
 * Exercise untimed WFI as a control for the timed-instruction tests. The
 * Host-visible syndrome must retain TI = 0, with RV and RN both zero
 * (RYQWST). Although the helper seeds X7 with a timeout-like value, the
 * zero-initialized gprs[0] must remain zero because WFI has no timeout
 * operand to report.
 */
TEST(wfxt_exit_tests, wfi_control_ti_rv_timeout)
{
	struct wfxt_test_context ctx;

	run_wfx_exit(&ctx, WFX_ISS_TI_WFI);
	UNSIGNED_LONGS_EQUAL(WFX_ISS_TI_WFI, ctx.rec_exit.esr & WFX_ISS_TI_MASK);
	UNSIGNED_LONGS_EQUAL(0UL, ctx.rec_exit.esr & WFX_ISS_RV_BIT);
	UNSIGNED_LONGS_EQUAL(0UL, ctx.rec_exit.esr & WFX_ISS_RN_MASK);
	UNSIGNED_LONGS_EQUAL(0UL, ctx.rec_exit.gprs[0]);
}

/*
 * Exercise untimed WFE as a control for the timed-instruction tests. The
 * Host-visible syndrome must retain TI = 1, identifying the event variant,
 * with RV and RN both zero (RYQWST). The value seeded in X7 must not be
 * reported as a timeout: the zero-initialized gprs[0] must remain zero.
 */
TEST(wfxt_exit_tests, wfe_control_ti_rv_timeout)
{
	struct wfxt_test_context ctx;

	run_wfx_exit(&ctx, WFX_ISS_TI_WFE);
	UNSIGNED_LONGS_EQUAL(WFX_ISS_TI_WFE, ctx.rec_exit.esr & WFX_ISS_TI_MASK);
	UNSIGNED_LONGS_EQUAL(0UL, ctx.rec_exit.esr & WFX_ISS_RV_BIT);
	UNSIGNED_LONGS_EQUAL(0UL, ctx.rec_exit.esr & WFX_ISS_RN_MASK);
	UNSIGNED_LONGS_EQUAL(0UL, ctx.rec_exit.gprs[0]);
}

/*
 * Inject a WFIT trap with TI = 2, RV set and RN selecting X7. Verify that
 * both TI bits survive in the Host-visible syndrome (RYQWST). In particular,
 * dropping TI[1] would misidentify the timed instruction as untimed WFI.
 */
TEST(wfxt_exit_tests, wfit_exit_preserves_ti)
{
	struct wfxt_test_context ctx;

	run_wfx_exit(&ctx, WFX_ISS_TI_WFIT);
	UNSIGNED_LONGS_EQUAL(WFX_ISS_TI_WFIT, ctx.rec_exit.esr & WFX_ISS_TI_MASK);
}

/*
 * Inject a WFIT trap with TI = 2 but deliberately leave the input RV bit
 * clear. Verify that the reported RV is set from TI[1], as required by
 * RYQWST in DEN0137 2.0-bet3. This checks that the exit handler constructs
 * the required output instead of simply copying ESR_EL2.ISS.RV.
 */
TEST(wfxt_exit_tests, wfit_exit_sets_rv)
{
	struct wfxt_test_context ctx;

	/* RMM derives RV from TI[1], rather than trusting ESR_EL2.ISS.RV. */
	run_wfx_exit(&ctx, WFX_ISS_TI_WFIT, false);
	UNSIGNED_LONGS_EQUAL(WFX_ISS_RV_BIT, ctx.rec_exit.esr & WFX_ISS_RV_BIT);
}

/*
 * Inject a WFIT trap whose nonzero RN field selects X7 as the timeout
 * source. Verify that the Host-visible RN field is cleared (RYQWST), so
 * the Realm's timeout-register index is not exposed in the exit syndrome.
 */
TEST(wfxt_exit_tests, wfit_exit_clears_rn)
{
	struct wfxt_test_context ctx;

	run_wfx_exit(&ctx, WFX_ISS_TI_WFIT);
	UNSIGNED_LONGS_EQUAL(0UL, ctx.rec_exit.esr & WFX_ISS_RN_MASK);
}

/*
 * Inject a WFIT trap with RN selecting X7, which contains TEST_TIMEOUT_VALUE.
 * Verify that the saved register value is copied to rec_exit.gprs[0]
 * (RBPYBC). The helper seeds the output with the complement of the timeout,
 * so the assertion also detects a missing write to the exit structure.
 */
TEST(wfxt_exit_tests, wfit_exit_reports_timeout_in_gprs0)
{
	struct wfxt_test_context ctx;

	run_wfx_exit(&ctx, WFX_ISS_TI_WFIT);
	UNSIGNED_LONGS_EQUAL(TEST_TIMEOUT_VALUE, ctx.rec_exit.gprs[0]);
}

/*
 * Inject a WFET trap with TI = 3, RV set and RN selecting X7. Verify that
 * both TI bits survive in the Host-visible syndrome (RYQWST), preserving
 * both the timed-instruction bit and the bit identifying the event variant.
 */
TEST(wfxt_exit_tests, wfet_exit_preserves_ti)
{
	struct wfxt_test_context ctx;

	run_wfx_exit(&ctx, WFX_ISS_TI_WFET);
	UNSIGNED_LONGS_EQUAL(WFX_ISS_TI_WFET, ctx.rec_exit.esr & WFX_ISS_TI_MASK);
}

/*
 * Inject a WFET trap with TI = 3 but deliberately leave the input RV bit
 * clear. Verify that the reported RV is derived from TI[1] (RYQWST), rather
 * than copied from ESR_EL2.ISS.RV. This is the event-variant counterpart of
 * wfit_exit_sets_rv.
 */
TEST(wfxt_exit_tests, wfet_exit_sets_rv)
{
	struct wfxt_test_context ctx;

	run_wfx_exit(&ctx, WFX_ISS_TI_WFET, false);
	UNSIGNED_LONGS_EQUAL(WFX_ISS_RV_BIT, ctx.rec_exit.esr & WFX_ISS_RV_BIT);
}

/*
 * Inject a WFET trap with RN selecting X7, which contains TEST_TIMEOUT_VALUE.
 * Verify that the saved register value is copied to rec_exit.gprs[0]
 * (RBPYBC), covering timeout reporting for the event variant. The output is
 * prefilled with the complement of the timeout to detect a missing write.
 */
TEST(wfxt_exit_tests, wfet_exit_reports_timeout_in_gprs0)
{
	struct wfxt_test_context ctx;

	run_wfx_exit(&ctx, WFX_ISS_TI_WFET);
	UNSIGNED_LONGS_EQUAL(TEST_TIMEOUT_VALUE, ctx.rec_exit.gprs[0]);
}

/*
 * Inject a WFIT trap with RN = 31, denoting XZR. Verify that gprs[0] is
 * explicitly overwritten with zero (RBPYBC). The helper seeds the state
 * after X30 with a nonzero PSTATE value to catch indexing past the saved
 * GPR array. Also check the complete reported ESR: only the WFx exception
 * class, WFIT TI and RV may remain, with RN and IL cleared (RYQWST).
 */
TEST(wfxt_exit_tests, wfit_exit_xzr_reports_zero)
{
	struct wfxt_test_context ctx;

	run_wfx_exit(&ctx, WFX_ISS_TI_WFIT, true, 31U);
	UNSIGNED_LONGS_EQUAL(ESR_EL2_EC_WFX | WFX_ISS_TI_WFIT | WFX_ISS_RV_BIT,
			    ctx.rec_exit.esr);
	UNSIGNED_LONGS_EQUAL(0UL, ctx.rec_exit.gprs[0]);
}

/*
 * Inject a WFET trap with RN = 31, denoting XZR. Verify that gprs[0] is
 * explicitly overwritten with zero (RBPYBC), even though the state after
 * X30 contains a nonzero PSTATE value. This covers the saved-GPR boundary
 * for the event variant. The complete reported ESR must contain only the
 * WFx exception class, WFET TI and RV, with RN and IL cleared (RYQWST).
 */
TEST(wfxt_exit_tests, wfet_exit_xzr_reports_zero)
{
	struct wfxt_test_context ctx;

	run_wfx_exit(&ctx, WFX_ISS_TI_WFET, true, 31U);
	UNSIGNED_LONGS_EQUAL(ESR_EL2_EC_WFX | WFX_ISS_TI_WFET | WFX_ISS_RV_BIT,
			    ctx.rec_exit.esr);
	UNSIGNED_LONGS_EQUAL(0UL, ctx.rec_exit.gprs[0]);
}

/*
 * Inject a WFIT trap with RN = 30, selecting the last saved GPR, and a
 * timeout with nonzero upper bits. Verify that gprs[0] preserves the full
 * TEST_TIMEOUT_64BIT value without truncation or treating X30 as XZR
 * (RBPYBC). The complete reported ESR must contain only the WFx exception
 * class, WFIT TI and RV, with RN and IL cleared (RYQWST).
 */
TEST(wfxt_exit_tests, wfit_exit_x30_preserves_64bit_timeout)
{
	struct wfxt_test_context ctx;

	run_wfx_exit(&ctx, WFX_ISS_TI_WFIT, true, 30U, TEST_TIMEOUT_64BIT);
	UNSIGNED_LONGS_EQUAL(ESR_EL2_EC_WFX | WFX_ISS_TI_WFIT | WFX_ISS_RV_BIT,
			    ctx.rec_exit.esr);
	UNSIGNED_LONGS_EQUAL(TEST_TIMEOUT_64BIT, ctx.rec_exit.gprs[0]);
}

/*
 * Inject a WFET trap with RN = 30, selecting the last saved GPR, and a
 * timeout with nonzero upper bits. Verify that gprs[0] preserves the full
 * TEST_TIMEOUT_64BIT value for the event variant (RBPYBC), covering both
 * the register-array boundary and 64-bit timeout handling. The complete
 * reported ESR must contain only the WFx exception class, WFET TI and RV,
 * with RN and IL cleared (RYQWST).
 */
TEST(wfxt_exit_tests, wfet_exit_x30_preserves_64bit_timeout)
{
	struct wfxt_test_context ctx;

	run_wfx_exit(&ctx, WFX_ISS_TI_WFET, true, 30U, TEST_TIMEOUT_64BIT);
	UNSIGNED_LONGS_EQUAL(ESR_EL2_EC_WFX | WFX_ISS_TI_WFET | WFX_ISS_RV_BIT,
			    ctx.rec_exit.esr);
	UNSIGNED_LONGS_EQUAL(TEST_TIMEOUT_64BIT, ctx.rec_exit.gprs[0]);
}
