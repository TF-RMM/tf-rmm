/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <CppUTest/CommandLineTestRunner.h>
#include <CppUTest/TestHarness.h>

extern "C"
{
	#include <arch_helpers.h>
	#include <simd.h>	  /* API to test */
	#include <simd_callbacks.h>
	#include <simd_private.h>
	#include <simd_test_helpers.h>
	#include <stdlib.h>
	#include <string.h>
	#include <test_helpers.h>
	#include <utils_def.h>
}

static uint32_t sve_vq;
static unsigned int helpers_times_called[SIMD_CB_IDS_MAX];

static void increment_times_called(enum simd_cb_ids id)
{
	helpers_times_called[id]++;
}

static void reset_times_called(void)
{
	(void)memset(&helpers_times_called, 0, sizeof(helpers_times_called));
}

static void fpu_save_regs_cb(struct fpu_regs *regs)
{
	increment_times_called(FPU_SAVE_REGS);
}

static void sve_save_regs_cb(struct sve_regs *regs, bool save_ffr)
{
	increment_times_called(SVE_SAVE_REGS);
}

static void fpu_restore_regs_cb(struct fpu_regs *regs)
{
	increment_times_called(FPU_RESTORE_REGS);
}

static void sve_restore_regs_cb(struct sve_regs *regs, bool restore_ffr)
{
	increment_times_called(SVE_RESTORE_REGS);
}

static void sve_clear_p_ffr_regs_cb(void)
{
	increment_times_called(SVE_CLEAR_P_FFR_REGS);
}

static uint32_t sve_rdvl_cb(void)
{
	return sve_vq;
}

TEST_GROUP(simd) {
	TEST_SETUP()
	{
		simd_test_helpers_init();
	}

	TEST_TEARDOWN()
	{
		simd_test_helpers_teardown();
	}
};

TEST(simd, simd_init_TC1)
{
	int ret;
	struct simd_config simd_cfg = { 0 };

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Call simd_init() when SVE and SME are disabled. Expect that the
	 * discovered CPU SIMD configuration will have SVE and SME
	 * disabled.
	 ******************************************************************/

	simd_test_helpers_setup_id_regs(false, false);

	simd_init();

	ret = simd_get_cpu_config(&simd_cfg);

	CHECK_TRUE(ret == 0);

	CHECK_TRUE(!simd_cfg.sve_en);
	CHECK_TRUE(simd_cfg.sve_vq == 0);
	CHECK_TRUE(!simd_cfg.sme_en);
}

TEST(simd, simd_init_TC2)
{
	u_register_t saved_cptr;
	int ret;
	struct simd_config simd_cfg = { 0 };
	union simd_cbs cb;

	/******************************************************************
	 * TEST CASE 2:
	 *
	 * Call simd_init() when SVE is enabled. Expect that the discovered
	 * CPU SIMD configuration will have SVE enabled, and the LEN field
	 * of ZCR_EL2 will have the correct value.
	 ******************************************************************/

	saved_cptr = read_cptr_el2();
	sve_vq = SVE_VQ_ARCH_MAX;
	cb.sve_rdvl = sve_rdvl_cb;

	simd_test_helpers_setup_id_regs(true, false);
	simd_test_register_callback(SVE_RDVL, cb);

	simd_init();

	ret = simd_get_cpu_config(&simd_cfg);

	CHECK_TRUE(ret == 0);

	CHECK_TRUE(simd_cfg.sve_en);
	CHECK_TRUE(simd_cfg.sve_vq == SVE_VL_TO_VQ(sve_rdvl()));
	CHECK_TRUE(!simd_cfg.sme_en);
	BYTES_EQUAL(SVE_VQ_ARCH_MAX, EXTRACT(ZCR_EL2_LEN, read_zcr_el2()));

	/* Verify that CPTR_EL2 was not altered by init */
	BYTES_EQUAL(saved_cptr, read_cptr_el2());
}

/*
 * Custom read callback for SMCR_EL2. Since we are interested in unit testing
 * simd.c rather than exactly emulating the hardware behaviour, we simply return
 * the max architecturally supported SVQ, regardless of the value that was
 * written.
 *
 * This custom callback is required to pass the assert() in sme_init_once().
 */
static u_register_t smcr_el2_rd_cb(u_register_t *reg)
{
	u_register_t smcr_el2_ret = *reg & ~MASK(SMCR_EL2_RAZ_LEN);

	smcr_el2_ret |= INPLACE(SMCR_EL2_RAZ_LEN, SVE_VQ_ARCH_MAX);

	return smcr_el2_ret;
}

/*
 * Write callback for SMCR_EL2. This simply writes a value to the register.
 */
static void smcr_el2_wr_cb(u_register_t val, u_register_t *reg)
{
	*reg = val;
}

TEST(simd, simd_init_TC3)
{
	u_register_t saved_cptr;
	int ret1;
	int ret2;
	struct simd_config simd_cfg = { 0 };

	/******************************************************************
	 * TEST CASE 3:
	 *
	 * Call simd_init() when SME is enabled. Expect that the discovered
	 * CPU SIMD configuration will have SME enabled.
	 ******************************************************************/

	saved_cptr = read_cptr_el2();

	simd_test_helpers_setup_id_regs(false, true);

	/*
	 * Install custom read callback for smcr_el2 to pass the assert() in
	 * sme_init_once().
	 */
	ret1 = host_util_set_sysreg_cb("smcr_el2", &smcr_el2_rd_cb,
				&smcr_el2_wr_cb, 0UL);

	CHECK_TRUE(ret1 == 0);

	simd_init();

	ret2 = simd_get_cpu_config(&simd_cfg);

	CHECK_TRUE(ret2 == 0);

	CHECK_TRUE(simd_cfg.sme_en);
	BYTES_EQUAL(saved_cptr, read_cptr_el2());
}

TEST(simd, simd_get_cpu_config_TC1)
{
	int ret;

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Call simd_get_cpu_config() when simd_init() has not yet been
	 * called. Expect the function to exit early with exit code -1.
	 ******************************************************************/

	ret = simd_get_cpu_config(NULL);

	CHECK_TRUE(ret == -1);
}

ASSERT_TEST(simd, simd_get_cpu_config_TC2)
{
	/******************************************************************
	 * TEST CASE 2:
	 *
	 * Call simd_get_cpu_config() with NULL. Expect assertion to fail.
	 ******************************************************************/

	simd_test_helpers_setup_id_regs(false, false);

	/*
	 * Must call simd_init() first to allow simd_get_cpu_config() to run
	 * without exiting early.
	 */
	simd_init();

	test_helpers_expect_assert_fail(true);

	(void)simd_get_cpu_config(NULL);

	test_helpers_fail_if_no_assert_failed();
}

TEST(simd, simd_context_init_TC1)
{
	int ret;
	struct simd_context test_simd_ctx;
	struct simd_config test_simd_cfg = { 0 };

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Call simd_context_init() before simd_init() is called. Expect
	 * the function to exit early with exit code -1.
	 ******************************************************************/

	(void)memset(&test_simd_ctx, 0, sizeof(struct simd_context));

	ret = simd_context_init(SIMD_OWNER_NWD, &test_simd_ctx, &test_simd_cfg);

	CHECK_TRUE(ret == -1);
}

TEST(simd, simd_context_init_TC2)
{
	int ret;
	struct simd_config test_simd_cfg = { 0 };
	struct simd_context test_simd_ctx;

	/******************************************************************
	 * TEST CASE 2:
	 *
	 * Call simd_context_init() twice with the same context. Expect the
	 * second call to exit early with exit code -1.
	 ******************************************************************/

	(void)memset(&test_simd_ctx, 0, sizeof(struct simd_context));
	simd_test_helpers_setup_id_regs(false, false);

	/*
	 * Must call simd_init() first to allow simd_context_init() to run
	 * without exiting early.
	 */
	simd_init();

	ret = simd_context_init(SIMD_OWNER_NWD, &test_simd_ctx, &test_simd_cfg);

	CHECK_TRUE(ret == 0);

	ret = simd_context_init(SIMD_OWNER_NWD, &test_simd_ctx, &test_simd_cfg);

	CHECK_TRUE(ret == -1);
}

TEST(simd, simd_context_init_TC3)
{
	int ret;
	struct simd_config test_simd_cfg = { 0 };
	struct simd_context test_simd_ctx;

	/******************************************************************
	 * TEST CASE 3:
	 *
	 * Call simd_context_init() with an invalid simd_cfg (try enabling
	 * SVE in simd_cfg but SVE is not present in CPU). Expect the
	 * function to exit early with exit code -1.
	 ******************************************************************/

	(void)memset(&test_simd_ctx, 0, sizeof(struct simd_context));
	simd_test_helpers_setup_id_regs(false, false);

	/*
	 * Initialise the CPU SIMD config with SVE disabled.
	 */
	simd_init();

	test_simd_cfg.sve_en = true;

	ret = simd_context_init(SIMD_OWNER_NWD, &test_simd_ctx, &test_simd_cfg);

	CHECK_TRUE(ret == -1);
}

TEST(simd, simd_context_init_TC4)
{
	int ret1, ret2;
	struct simd_config test_simd_cfg = { 0 };
	struct simd_context test_simd_ctx;
	struct simd_config cpu_simd_cfg;
	union simd_cbs cb;

	/******************************************************************
	 * TEST CASE 4:
	 *
	 * Call simd_context_init() with an invalid simd_cfg (try enabling
	 * SVE VQ in simd_cfg higher than SVE VQ of CPU). Expect the
	 * function to exit early with exit code -1.
	 ******************************************************************/

	sve_vq = (SVE_VQ_ARCH_MAX - 1U) * 128U;
	cb.sve_rdvl = sve_rdvl_cb;

	(void)memset(&test_simd_ctx, 0, sizeof(struct simd_context));
	simd_test_helpers_setup_id_regs(true, false);
	simd_test_register_callback(SVE_RDVL, cb);

	/*
	 * Initialise the CPU SIMD config with SVE enabled.
	 */
	simd_init();

	ret1 = simd_get_cpu_config(&cpu_simd_cfg);

	CHECK_TRUE(ret1 == 0);

	/*
	 * Create a SIMD config that has SVE VQ larger than CPU SIMD config's
	 * SVE VQ.
	 */
	test_simd_cfg.sve_en = true;
	test_simd_cfg.sve_vq = cpu_simd_cfg.sve_vq + 1U;

	ret2 = simd_context_init(SIMD_OWNER_NWD, &test_simd_ctx, &test_simd_cfg);

	CHECK_TRUE(ret2 == -1);
}

TEST(simd, simd_context_init_TC5)
{
	int ret;
	struct simd_config test_simd_cfg = { 0 };
	struct simd_context test_simd_ctx;
	union simd_cbs cb;

	/******************************************************************
	 * TEST CASE 5:
	 *
	 * Call simd_context_init() with an invalid simd_cfg (try enabling
	 * SME in simd_cfg but SME is not present in CPU). Expect the
	 * function to exit early with exit code -1.
	 ******************************************************************/

	sve_vq = SVE_VQ_ARCH_MAX * 128U;
	cb.sve_rdvl = sve_rdvl_cb;

	(void)memset(&test_simd_ctx, 0, sizeof(struct simd_context));
	simd_test_helpers_setup_id_regs(true, false);
	simd_test_register_callback(SVE_RDVL, cb);

	/*
	 * Initialise the CPU SIMD config with SVE enabled and SME disabled.
	 */
	simd_init();

	/*
	 * Create a SIMD config that has SME enabled.
	 */
	test_simd_cfg.sme_en = true;

	ret = simd_context_init(SIMD_OWNER_NWD, &test_simd_ctx, &test_simd_cfg);

	CHECK_TRUE(ret == -1);
}

TEST(simd, simd_context_init_TC6)
{
	int ret;
	struct simd_config test_simd_cfg = { 0 };
	struct simd_context test_simd_ctx;

	/******************************************************************
	 * TEST CASE 6:
	 *
	 * Call simd_context_init() with an invalid owner. Expect the
	 * function to exit early with exit code -1.
	 ******************************************************************/

	(void)memset(&test_simd_ctx, 0, sizeof(struct simd_context));
	simd_test_helpers_setup_id_regs(false, false);

	simd_init();

	test_simd_ctx.sflags &= ~SIMD_SFLAG_INIT_DONE;

	/* Generate a random integer greater than 2. */
	int invalid_owner = rand() % (INT_MAX - 2) + 3;

	ret = simd_context_init((simd_owner_t)invalid_owner, &test_simd_ctx,
				&test_simd_cfg);

	CHECK_TRUE(ret == -1);
}

TEST(simd, simd_context_save_TC1)
{
	struct simd_context test_simd_ctx;
	struct simd_config test_simd_cfg = { 0 };
	u_register_t cptr_el2;
	int ret;
	union simd_cbs cb;
	int times_called_prev;

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Initialise a test SIMD FPU context that belongs to NS world.
	 * Call simd_context_save() with this test context. Expect the
	 * save to complete successfully. In addition, the SIMD helper
	 * function fpu_save_registers() should be called exactly once.
	 ******************************************************************/

	cptr_el2 = read_cptr_el2();
	times_called_prev = helpers_times_called[FPU_SAVE_REGS];
	cb.fpu_save_restore_regs = fpu_save_regs_cb;

	(void)memset(&test_simd_ctx, 0, sizeof(struct simd_context));
	simd_test_register_callback(FPU_SAVE_REGS, cb);
	simd_test_helpers_setup_id_regs(false, false);

	simd_init();

	/* Initialise NS ctx. */
	ret = simd_get_cpu_config(&test_simd_cfg);
	CHECK_TRUE(ret == 0);

	ret = simd_context_init(SIMD_OWNER_NWD, &test_simd_ctx, &test_simd_cfg);

	CHECK_TRUE(ret == 0);

	simd_context_save(&test_simd_ctx);

	CHECK_TRUE(helpers_times_called[FPU_SAVE_REGS] - times_called_prev == 1);
	CHECK_TRUE(simd_is_state_saved());

	/* Check that CPTR_EL2 was restored correctly. */
	BYTES_EQUAL(cptr_el2, read_cptr_el2());
}

ASSERT_TEST(simd, simd_context_save_TC2)
{
	struct simd_context test_simd_ctx;

	/******************************************************************
	 * TEST CASE 2:
	 *
	 * Call simd_context_save() with an uninitialised context. Expect
	 * an assertion to fail.
	 ******************************************************************/

	(void)memset(&test_simd_ctx, 0, sizeof(struct simd_context));

	test_helpers_expect_assert_fail(true);
	simd_context_save(&test_simd_ctx);
	test_helpers_fail_if_no_assert_failed();
}

ASSERT_TEST(simd, simd_context_save_TC3)
{
	struct simd_context test_simd_ctx;
	struct simd_config test_simd_cfg = { 0 };
	int ret;

	/******************************************************************
	 * TEST CASE 3:
	 *
	 * Initialise a test SIMD FPU context that belongs to Realm. Call
	 * simd_context_save() with this test context. As lazy enablement
	 * is used, the (initially empty) Realm SIMD context is considered
	 * to be saved as part of initialisation. Therefore, a call to
	 * simd_context_save() to save it again should cause an assertion
	 * to fail.
	 ******************************************************************/

	(void)memset(&test_simd_ctx, 0, sizeof(struct simd_context));
	simd_test_helpers_setup_id_regs(false, false);
	simd_init();

	ret = simd_context_init(SIMD_OWNER_REL1, &test_simd_ctx, &test_simd_cfg);

	CHECK_TRUE(ret == 0);

	test_helpers_expect_assert_fail(true);
	simd_context_save(&test_simd_ctx);
	test_helpers_fail_if_no_assert_failed();
}

ASSERT_TEST(simd, simd_context_save_TC4)
{
	struct simd_context test_simd_ctx;
	struct simd_config test_simd_cfg = { 0 };
	int ret;

	/******************************************************************
	 * TEST CASE 4:
	 *
	 * Call simd_context_save() twice on the same context. Expect an
	 * assertion to fail on the second call.
	 ******************************************************************/

	(void)memset(&test_simd_ctx, 0, sizeof(struct simd_context));
	simd_test_helpers_setup_id_regs(false, false);
	simd_init();

	/* Initialise NS ctx. */
	ret = simd_get_cpu_config(&test_simd_cfg);
	CHECK_TRUE(ret == 0);

	ret = simd_context_init(SIMD_OWNER_NWD, &test_simd_ctx, &test_simd_cfg);

	CHECK_TRUE(ret == 0);

	simd_context_save(&test_simd_ctx);

	CHECK_TRUE(simd_is_state_saved());

	test_helpers_expect_assert_fail(true);
	simd_context_save(&test_simd_ctx);
	test_helpers_fail_if_no_assert_failed();
}

ASSERT_TEST(simd, simd_context_restore_TC1)
{
	struct simd_context test_simd_ctx;

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Call simd_context_restore() with an uninitialised context.
	 * Expect an assertion to fail.
	 ******************************************************************/

	(void)memset(&test_simd_ctx, 0, sizeof(struct simd_context));
	simd_test_helpers_setup_id_regs(false, false);
	simd_init();

	test_helpers_expect_assert_fail(true);
	simd_context_restore(&test_simd_ctx);
	test_helpers_fail_if_no_assert_failed();
}

ASSERT_TEST(simd, simd_context_restore_TC2)
{
	struct simd_context test_simd_ctx;
	struct simd_config test_simd_cfg = { 0 };
	int ret;

	/******************************************************************
	 * TEST CASE 2:
	 *
	 * Call simd_context_restore() with a context that has not been
	 * previously saved. Expect an assertion to fail.
	 ******************************************************************/

	(void)memset(&test_simd_ctx, 0, sizeof(struct simd_context));
	simd_test_helpers_setup_id_regs(false, false);
	simd_init();

	/* Initialise NS ctx. */
	ret = simd_get_cpu_config(&test_simd_cfg);
	CHECK_TRUE(ret == 0);

	ret = simd_context_init(SIMD_OWNER_NWD, &test_simd_ctx, &test_simd_cfg);

	CHECK_TRUE(ret == 0);

	test_helpers_expect_assert_fail(true);
	simd_context_restore(&test_simd_ctx);
	test_helpers_fail_if_no_assert_failed();
}

ASSERT_TEST(simd, simd_context_restore_TC3)
{
	struct simd_context test_simd_ctx;
	struct simd_config test_simd_cfg = { 0 };
	int ret;

	/******************************************************************
	 * TEST CASE 3:
	 *
	 * Call simd_context_restore() when the CPU still has unsaved live
	 * SIMD state. Expect an assertion to fail.
	 ******************************************************************/

	(void)memset(&test_simd_ctx, 0, sizeof(struct simd_context));
	simd_test_helpers_setup_id_regs(false, false);
	simd_init();

	/*
	 * Initialise a test SIMD context with Realm as owner. Since Realm's
	 * SIMD state is assumed to be saved as part of initialisation, this
	 * allows us to pass the assertion that Test Case 2 fails.
	 */
	ret = simd_context_init(SIMD_OWNER_REL1, &test_simd_ctx, &test_simd_cfg);

	CHECK_TRUE(ret == 0);

	test_helpers_expect_assert_fail(true);
	simd_context_restore(&test_simd_ctx);
	test_helpers_fail_if_no_assert_failed();
}

ASSERT_TEST(simd, simd_context_restore_TC4)
{
	struct simd_context test_simd_ctx;
	struct simd_config test_simd_cfg = { 0 };
	int ret;

	/******************************************************************
	 * TEST CASE 4:
	 *
	 * Call simd_context_restore() on the same context twice. Expect
	 * an assertion to fail on the second call.
	 ******************************************************************/

	(void)memset(&test_simd_ctx, 0, sizeof(struct simd_context));
	simd_test_helpers_setup_id_regs(false, false);
	simd_init();

	/* Initialise NS ctx. */
	ret = simd_get_cpu_config(&test_simd_cfg);
	CHECK_TRUE(ret == 0);

	ret = simd_context_init(SIMD_OWNER_NWD, &test_simd_ctx, &test_simd_cfg);
	CHECK_TRUE(ret == 0);

	/*
	 * Restore the context for the first time. However, a context save must
	 * be performed first so that the CPU doesn't have unsaved live SIMD
	 * state.
	 */
	simd_context_save(&test_simd_ctx);
	simd_context_restore(&test_simd_ctx);

	/* Restore the context for the second time. */
	test_helpers_expect_assert_fail(true);
	simd_context_restore(&test_simd_ctx);
	test_helpers_fail_if_no_assert_failed();
}

TEST(simd, simd_context_switch_TC1)
{
	struct simd_context simd_ctx_nwd;
	struct simd_context simd_ctx_rl;
	struct simd_config test_simd_cfg = { 0 };
	union simd_cbs cb_save;
	union simd_cbs cb_restore;
	int ret1, ret2;

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Initialise two FPU contexts, one with NWD owner and one with
	 * Realm owner. Call simd_context_switch() to save the NS context
	 * and restore the Realm context. Then, call simd_context_switch()
	 * again to do the opposite. Verify that the correct helper
	 * routines are called.
	 ******************************************************************/

	reset_times_called();
	(void)memset(&simd_ctx_nwd, 0, sizeof(struct simd_context));
	(void)memset(&simd_ctx_rl, 0, sizeof(struct simd_context));
	simd_test_helpers_setup_id_regs(false, false);

	simd_init();

	/* Initialise NS ctx. */
	ret1 = simd_get_cpu_config(&test_simd_cfg);
	CHECK_TRUE(ret1 == 0);

	ret1 = simd_context_init(SIMD_OWNER_NWD, &simd_ctx_nwd, &test_simd_cfg);
	CHECK_TRUE(ret1 == 0);

	/* Initialise RL FPU contexts */
	ret2 = simd_context_init(SIMD_OWNER_REL1, &simd_ctx_rl, &test_simd_cfg);
	CHECK_TRUE(ret2 == 0);

	/* Set callbacks for the save and restore helper routines */

	cb_save.fpu_save_restore_regs = fpu_save_regs_cb;
	cb_restore.fpu_save_restore_regs = fpu_restore_regs_cb;

	simd_test_register_callback(FPU_SAVE_REGS, cb_save);
	simd_test_register_callback(FPU_RESTORE_REGS, cb_restore);

	/*
	 * Call simd_context_switch() to do the NS FPU -> RL FPU switch.
	 */
	(void)simd_context_switch(&simd_ctx_nwd, &simd_ctx_rl);

	CHECK_TRUE(helpers_times_called[FPU_SAVE_REGS] == 1U);
	CHECK_TRUE(helpers_times_called[FPU_RESTORE_REGS] == 1U);

	/*
	 * Do the RL FPU -> NS FPU switch.
	 */
	(void)simd_context_switch(&simd_ctx_rl, &simd_ctx_nwd);

	CHECK_TRUE(helpers_times_called[FPU_SAVE_REGS] == 2U);
	CHECK_TRUE(helpers_times_called[FPU_RESTORE_REGS] == 2U);
}

TEST(simd, simd_context_switch_TC2)
{
	struct simd_context simd_ctx_nwd;
	struct simd_context simd_ctx_rl;
	struct simd_config test_simd_cfg = { 0 };
	union simd_cbs cb_save;
	union simd_cbs cb_restore;
	int ret;

	/******************************************************************
	 * TEST CASE 2:
	 *
	 * Initialise an SVE context with NS owner and an FPU context with
	 * Realm owner. Call simd_context_switch() to save the NS SVE
	 * context and restore the Realm FPU context. Then, call
	 * simd_context_switch() again to do the opposite. Verify that the
	 * correct helper routines are called.
	 ******************************************************************/

	reset_times_called();
	(void)memset(&simd_ctx_nwd, 0, sizeof(struct simd_context));
	(void)memset(&simd_ctx_rl, 0, sizeof(struct simd_context));
	simd_test_helpers_setup_id_regs(true, false);

	simd_init();

	/* Initialise RL FPU ctx */
	ret = simd_context_init(SIMD_OWNER_REL1, &simd_ctx_rl, &test_simd_cfg);

	CHECK_TRUE(ret == 0);

	/* Initialise NS SVE ctx with the CPU SIMD config */
	ret = simd_get_cpu_config(&test_simd_cfg);

	CHECK_TRUE(ret == 0);

	ret = simd_context_init(SIMD_OWNER_NWD, &simd_ctx_nwd, &test_simd_cfg);

	CHECK_TRUE(ret == 0);

	/*
	 * Explicitly disable SVE hint bit as we are testing the case where NS
	 * world has SVE-specific live state.
	 */
	simd_update_smc_sve_hint(&simd_ctx_nwd, false);

	/* Do the NS SVE -> RL FPU switch */
	cb_save.sve_save_restore_regs = sve_save_regs_cb;
	cb_restore.fpu_save_restore_regs = fpu_restore_regs_cb;

	simd_test_register_callback(SVE_SAVE_REGS, cb_save);
	simd_test_register_callback(FPU_RESTORE_REGS, cb_restore);

	(void)simd_context_switch(&simd_ctx_nwd, &simd_ctx_rl);

	CHECK_TRUE(helpers_times_called[SVE_SAVE_REGS] == 1);
	CHECK_TRUE(helpers_times_called[FPU_RESTORE_REGS] == 1);

	/* Do the RL FPU -> NS SVE switch */
	cb_save.fpu_save_restore_regs = fpu_save_regs_cb;
	cb_restore.sve_save_restore_regs = sve_restore_regs_cb;

	simd_test_register_callback(FPU_SAVE_REGS, cb_save);
	simd_test_register_callback(SVE_RESTORE_REGS, cb_restore);

	(void)simd_context_switch(&simd_ctx_rl, &simd_ctx_nwd);

	CHECK_TRUE(helpers_times_called[FPU_SAVE_REGS] == 1);
	CHECK_TRUE(helpers_times_called[SVE_RESTORE_REGS] == 1);
}

TEST(simd, simd_context_switch_TC3)
{
	struct simd_context simd_ctx_nwd;
	struct simd_context simd_ctx_rl;
	struct simd_config test_simd_cfg;
	union simd_cbs cb_save;
	union simd_cbs cb_restore;
	int ret1, ret2;

	/******************************************************************
	 * TEST CASE 3:
	 *
	 * Initialise two SVE contexts, one with NS owner and one with
	 * Realm owner. Call simd_context_switch() to save the NS context
	 * and restore the Realm context. Then, call simd_context_switch()
	 * again to do the opposite. Verify that the correct helper
	 * routines are called.
	 ******************************************************************/

	reset_times_called();
	(void)memset(&simd_ctx_nwd, 0, sizeof(struct simd_context));
	(void)memset(&simd_ctx_rl, 0, sizeof(struct simd_context));
	simd_test_helpers_setup_id_regs(true, false);

	simd_init();

	/* Initialise two SVE contexts */
	ret1 = simd_get_cpu_config(&test_simd_cfg);

	CHECK_TRUE(ret1 == 0);

	ret1 = simd_context_init(SIMD_OWNER_NWD, &simd_ctx_nwd, &test_simd_cfg);
	ret2 = simd_context_init(SIMD_OWNER_REL1, &simd_ctx_rl, &test_simd_cfg);

	CHECK_TRUE(ret1 == 0);
	CHECK_TRUE(ret2 == 0);

	simd_update_smc_sve_hint(&simd_ctx_nwd, false);

	/* Set callbacks for the save and restore helper routines */

	cb_save.sve_save_restore_regs = sve_save_regs_cb;
	cb_restore.sve_save_restore_regs = sve_restore_regs_cb;

	simd_test_register_callback(SVE_SAVE_REGS, cb_save);
	simd_test_register_callback(SVE_RESTORE_REGS, cb_restore);

	/* Do the NS SVE -> RL SVE switch */
	(void)simd_context_switch(&simd_ctx_nwd, &simd_ctx_rl);

	CHECK_TRUE(helpers_times_called[SVE_SAVE_REGS] == 1U);
	CHECK_TRUE(helpers_times_called[SVE_RESTORE_REGS] == 1U);

	/* Do the RL SVE -> NS SVE switch */
	(void)simd_context_switch(&simd_ctx_rl, &simd_ctx_nwd);

	CHECK_TRUE(helpers_times_called[SVE_SAVE_REGS] == 2U);
	CHECK_TRUE(helpers_times_called[SVE_RESTORE_REGS] == 2U);
}

TEST(simd, simd_context_switch_TC4)
{
	struct simd_context simd_ctx_nwd;
	struct simd_context simd_ctx_rl;
	struct simd_config test_simd_cfg = { 0 };
	union simd_cbs cb_save;
	union simd_cbs cb_restore;
	int ret;

	/******************************************************************
	 * TEST CASE 4:
	 *
	 * Initialise an SME context (SVE disabled, SVE streaming mode
	 * disabled) with NS owner and an FPU context with Realm owner.
	 * Call simd_context_switch() to save the NS SME context and
	 * restore the Realm FPU context. Then, call simd_context_switch()
	 * again to do the opposite. Verify that the correct helper
	 * routines are called.
	 ******************************************************************/

	reset_times_called();
	(void)memset(&simd_ctx_nwd, 0, sizeof(struct simd_context));
	(void)memset(&simd_ctx_rl, 0, sizeof(struct simd_context));
	simd_test_helpers_setup_id_regs(false, true);

	simd_init();

	/* Initialise RL FPU ctx */
	ret = simd_context_init(SIMD_OWNER_REL1, &simd_ctx_rl, &test_simd_cfg);

	CHECK_TRUE(ret == 0);

	/* Initialise NS SME ctx */
	ret = simd_get_cpu_config(&test_simd_cfg);

	CHECK_TRUE(ret == 0);

	ret = simd_context_init(SIMD_OWNER_NWD, &simd_ctx_nwd, &test_simd_cfg);

	CHECK_TRUE(ret == 0);

	/* Do the NS SME -> RL FPU switch
	 *
	 * Since SVE is disabled and SVE streaming mode is disabled, expect the
	 * FPU registers to be saved when the NS SME context is saved.
	 */
	cb_save.fpu_save_restore_regs = fpu_save_regs_cb;
	cb_restore.fpu_save_restore_regs = fpu_restore_regs_cb;

	simd_test_register_callback(FPU_SAVE_REGS, cb_save);
	simd_test_register_callback(FPU_RESTORE_REGS, cb_restore);

	(void)simd_context_switch(&simd_ctx_nwd, &simd_ctx_rl);

	CHECK_TRUE(helpers_times_called[FPU_SAVE_REGS] == 1);
	CHECK_TRUE(helpers_times_called[FPU_RESTORE_REGS] == 1);

	/* Do the RL FPU -> NS SME switch */
	(void)simd_context_switch(&simd_ctx_rl, &simd_ctx_nwd);

	CHECK_TRUE(helpers_times_called[FPU_SAVE_REGS] == 2);
	CHECK_TRUE(helpers_times_called[FPU_RESTORE_REGS] == 2);
}

TEST(simd, simd_context_switch_TC5)
{
	struct simd_context simd_ctx_nwd;
	struct simd_context simd_ctx_rl;
	struct simd_config test_simd_cfg = { 0 };
	union simd_cbs cb_save;
	union simd_cbs cb_restore;
	int ret;

	/******************************************************************
	 * TEST CASE 5:
	 *
	 * Initialise an SME context (SVE enabled, SVE streaming mode
	 * enabled) with NS owner and an FPU context with Realm owner.
	 * Call simd_context_switch() to save the NS SME context and
	 * restore the Realm FPU context. Then, call simd_context_switch()
	 * again to do the opposite. Verify that the correct helper
	 * routines are called.
	 ******************************************************************/

	reset_times_called();
	(void)memset(&simd_ctx_nwd, 0, sizeof(struct simd_context));
	(void)memset(&simd_ctx_rl, 0, sizeof(struct simd_context));
	simd_test_helpers_setup_id_regs(true, true);

	/* Enable SVE streaming mode */
	write_svcr(read_svcr() | SVCR_SM_BIT);

	simd_init();

	/* Initialise RL FPU ctx */
	ret = simd_context_init(SIMD_OWNER_REL1, &simd_ctx_rl, &test_simd_cfg);

	CHECK_TRUE(ret == 0);

	/* Initialise NS SME ctx with the CPU SIMD config */
	ret = simd_get_cpu_config(&test_simd_cfg);

	CHECK_TRUE(ret == 0);

	ret = simd_context_init(SIMD_OWNER_NWD, &simd_ctx_nwd, &test_simd_cfg);

	CHECK_TRUE(ret == 0);

	/* Do the NS SME -> RL FPU switch.
	 *
	 * Since SVE is enabled and SVE streaming mode is enabled, expect the
	 * SVE registers to be saved when the NS SME context is saved.
	 */
	cb_save.sve_save_restore_regs = sve_save_regs_cb;
	cb_restore.fpu_save_restore_regs = fpu_restore_regs_cb;

	simd_test_register_callback(SVE_SAVE_REGS, cb_save);
	simd_test_register_callback(FPU_RESTORE_REGS, cb_restore);

	(void)simd_context_switch(&simd_ctx_nwd, &simd_ctx_rl);

	CHECK_TRUE(helpers_times_called[SVE_SAVE_REGS] == 1);
	CHECK_TRUE(helpers_times_called[FPU_RESTORE_REGS] == 1);

	/* Do the RL FPU -> NS SME switch */
	cb_save.fpu_save_restore_regs = fpu_save_regs_cb;
	cb_restore.sve_save_restore_regs = sve_restore_regs_cb;

	simd_test_register_callback(FPU_SAVE_REGS, cb_save);
	simd_test_register_callback(SVE_RESTORE_REGS, cb_restore);

	(void)simd_context_switch(&simd_ctx_rl, &simd_ctx_nwd);

	CHECK_TRUE(helpers_times_called[FPU_SAVE_REGS] == 1);
	CHECK_TRUE(helpers_times_called[SVE_RESTORE_REGS] == 1);
}

TEST(simd, simd_context_switch_TC6)
{
	struct simd_context simd_ctx_nwd;
	struct simd_context simd_ctx_rl;
	struct simd_config test_simd_cfg = { 0 };
	union simd_cbs cb_save;
	union simd_cbs cb_restore;
	int ret1, ret2;

	/******************************************************************
	 * TEST CASE 6:
	 *
	 * Test setup
	 * NS world : SVE + SME. PSTATE.SM=0
	 * Realm    : SVE
	 *
	 * Call simd_context_switch() to save the NS SVE context and
	 * restore the Realm SVE context. Then, call simd_context_switch()
	 * again to do the opposite. Verify that the correct helper
	 * routines are called.
	 ******************************************************************/

	reset_times_called();
	(void)memset(&simd_ctx_nwd, 0, sizeof(struct simd_context));
	(void)memset(&simd_ctx_rl, 0, sizeof(struct simd_context));
	simd_test_helpers_setup_id_regs(true, true);

	simd_init();

	/* Initialise RL SVE ctx */
	test_simd_cfg.sve_en = true;

	ret1 = simd_context_init(SIMD_OWNER_REL1, &simd_ctx_rl, &test_simd_cfg);
	CHECK_TRUE(ret1 == 0);

	/* Initialise NS SME ctx. */
	ret1 = simd_get_cpu_config(&test_simd_cfg);
	CHECK_TRUE(ret1 == 0);

	ret2 = simd_context_init(SIMD_OWNER_NWD, &simd_ctx_nwd, &test_simd_cfg);
	CHECK_TRUE(ret2 == 0);
	write_svcr(read_svcr() & ~SVCR_SM_BIT);

	cb_save.sve_save_restore_regs = sve_save_regs_cb;
	cb_restore.sve_save_restore_regs = sve_restore_regs_cb;
	simd_test_register_callback(SVE_SAVE_REGS, cb_save);
	simd_test_register_callback(SVE_RESTORE_REGS, cb_restore);

	/* Do the NS SME -> RL SVE switch. */
	(void)simd_context_switch(&simd_ctx_nwd, &simd_ctx_rl);

	CHECK_TRUE(helpers_times_called[SVE_SAVE_REGS] == 1);
	CHECK_TRUE(helpers_times_called[SVE_RESTORE_REGS] == 1);

	/* Do the RL SVE -> NS SME switch */
	(void)simd_context_switch(&simd_ctx_rl, &simd_ctx_nwd);

	CHECK_TRUE(helpers_times_called[SVE_SAVE_REGS] == 2);
	CHECK_TRUE(helpers_times_called[SVE_RESTORE_REGS] == 2);
}

TEST(simd, simd_context_switch_TC7)
{
	struct simd_context simd_ctx_nwd;
	struct simd_context simd_ctx_rl;
	struct simd_config test_simd_cfg = { 0 };
	union simd_cbs cb_save;
	union simd_cbs cb_restore;
	int ret;

	/******************************************************************
	 * TEST CASE 7:
	 *
	 * Initialise an SME context (SVE enabled, SVE streaming mode
	 * enabled) with NS owner and an SVE context with Realm owner.
	 * Call simd_context_switch() to save the NS SME context and
	 * restore the Realm SVE context. Then, call simd_context_switch()
	 * again to do the opposite. Verify that the correct helper
	 * routines are called.
	 ******************************************************************/

	reset_times_called();
	(void)memset(&simd_ctx_nwd, 0, sizeof(struct simd_context));
	(void)memset(&simd_ctx_rl, 0, sizeof(struct simd_context));
	simd_test_helpers_setup_id_regs(true, true);
	write_svcr(read_svcr() | SVCR_SM_BIT);

	simd_init();

	/* Initialise RL SVE ctx */
	test_simd_cfg.sve_en = true;

	ret = simd_context_init(SIMD_OWNER_REL1, &simd_ctx_rl, &test_simd_cfg);

	CHECK_TRUE(ret == 0);

	/* Initialise NS SME ctx */
	ret = simd_get_cpu_config(&test_simd_cfg);

	CHECK_TRUE(ret == 0);

	ret = simd_context_init(SIMD_OWNER_NWD, &simd_ctx_nwd, &test_simd_cfg);

	CHECK_TRUE(ret == 0);

	/* Do the NS SME -> RL SVE switch.
	 *
	 * Since SVE is enabled and SVE streaming mode is enabled, expect the
	 * SVE registers to be saved when the NS SME context is saved.
	 */
	cb_save.sve_save_restore_regs = sve_save_regs_cb;
	cb_restore.sve_save_restore_regs = sve_restore_regs_cb;

	simd_test_register_callback(SVE_SAVE_REGS, cb_save);
	simd_test_register_callback(SVE_RESTORE_REGS, cb_restore);

	(void)simd_context_switch(&simd_ctx_nwd, &simd_ctx_rl);

	CHECK_TRUE(helpers_times_called[SVE_SAVE_REGS] == 1);
	CHECK_TRUE(helpers_times_called[SVE_RESTORE_REGS] == 1);

	/* Do the RL SVE -> NS SME switch */
	(void)simd_context_switch(&simd_ctx_rl, &simd_ctx_nwd);

	CHECK_TRUE(helpers_times_called[SVE_SAVE_REGS] == 2);
	CHECK_TRUE(helpers_times_called[SVE_RESTORE_REGS] == 2);
}

TEST(simd, simd_context_switch_TC8)
{
	struct simd_context simd_ctx_nwd;
	struct simd_context simd_ctx_rl;
	struct simd_config test_simd_cfg = { 0 };
	union simd_cbs cb_fpu_save;
	union simd_cbs cb_fpu_restore;
	union simd_cbs cb_sve_save;
	union simd_cbs cb_sve_restore;
	union simd_cbs cb_sve_clear_p_ffr;
	int ret;

	/******************************************************************
	 * TEST CASE 8:
	 *
	 * Initialise an SVE context with NS owner, with SVE hint bit
	 * enabled, and an FPU context with Realm owner. Call
	 * simd_context_switch() to save the NS SVE context and restore
	 * the Realm FPU context. Then, call simd_context_switch() again to
	 * do the opposite. Verify that the correct helper routines are
	 * called.
	 ******************************************************************/

	reset_times_called();
	(void)memset(&simd_ctx_nwd, 0, sizeof(struct simd_context));
	(void)memset(&simd_ctx_rl, 0, sizeof(struct simd_context));
	simd_test_helpers_setup_id_regs(true, false);

	simd_init();

	/* Initialise RL FPU ctx */
	ret = simd_context_init(SIMD_OWNER_REL1, &simd_ctx_rl, &test_simd_cfg);

	CHECK_TRUE(ret == 0);

	/* Initialise NS SVE ctx with the CPU SIMD config */
	ret = simd_get_cpu_config(&test_simd_cfg);

	CHECK_TRUE(ret == 0);

	ret = simd_context_init(SIMD_OWNER_NWD, &simd_ctx_nwd, &test_simd_cfg);

	CHECK_TRUE(ret == 0);

	/*
	 * Set SVE hint bit for NS SVE ctx. This denotes that there is no live
	 * SVE-specific live state in NS world.
	 */
	simd_update_smc_sve_hint(&simd_ctx_nwd, true);

	/* Set callbacks for relevant helper routines */
	cb_fpu_save.fpu_save_restore_regs = fpu_save_regs_cb;
	cb_fpu_restore.fpu_save_restore_regs = fpu_restore_regs_cb;
	cb_sve_save.sve_save_restore_regs = sve_save_regs_cb;
	cb_sve_restore.sve_save_restore_regs = sve_restore_regs_cb;
	cb_sve_clear_p_ffr.sve_clear_regs = sve_clear_p_ffr_regs_cb;

	simd_test_register_callback(FPU_SAVE_REGS, cb_fpu_save);
	simd_test_register_callback(FPU_RESTORE_REGS, cb_fpu_restore);
	simd_test_register_callback(SVE_SAVE_REGS, cb_sve_save);
	simd_test_register_callback(SVE_RESTORE_REGS, cb_sve_restore);
	simd_test_register_callback(SVE_CLEAR_P_FFR_REGS, cb_sve_clear_p_ffr);

	/*
	 * Do the NS SVE -> RL FPU switch. Since SVE hint bit is set, expect the
	 * FPU Q registers to be saved, as opposed to the SVE Z registers.
	 */
	(void)simd_context_switch(&simd_ctx_nwd, &simd_ctx_rl);

	CHECK_TRUE(helpers_times_called[FPU_SAVE_REGS] == 1);
	CHECK_TRUE(helpers_times_called[FPU_RESTORE_REGS] == 1);
	CHECK_TRUE(helpers_times_called[SVE_SAVE_REGS] == 0);

	reset_times_called();

	/*
	 * Do the RL FPU -> NS SVE switch. Since SVE hint bit is set, expect the
	 * FPU Q registers to be restored, as opposed to the SVE Z registers. In
	 * addition, expect the sve_clear_p_ffr_registers() helper routine to be
	 * called. The P and FFR registers hold values from previous usage, so
	 * they should be explicitly cleared.
	 */
	(void)simd_context_switch(&simd_ctx_rl, &simd_ctx_nwd);

	CHECK_TRUE(helpers_times_called[FPU_SAVE_REGS] == 1);
	CHECK_TRUE(helpers_times_called[FPU_RESTORE_REGS] == 1);
	CHECK_TRUE(helpers_times_called[SVE_CLEAR_P_FFR_REGS] == 1);
	CHECK_TRUE(helpers_times_called[SVE_RESTORE_REGS == 0]);
}

TEST(simd, simd_context_switch_TC9)
{
	struct simd_context simd_ctx_nwd;
	struct simd_context simd_ctx_rl;
	struct simd_config test_simd_cfg = { 0 };
	union simd_cbs cb_fpu_save;
	union simd_cbs cb_fpu_restore;
	union simd_cbs cb_sve_save;
	union simd_cbs cb_sve_restore;
	union simd_cbs cb_sve_clear_p_ffr;
	int ret1, ret2;

	/******************************************************************
	 * TEST CASE 9:
	 *
	 * Initialise two SVE contexts, one with NS owner and one with
	 * Realm owner. Enable SVE hint bit for NS SVE context. Call
	 * simd_context_switch() to save the NS context and restore the
	 * Realm context. Then, call simd_context_switch() again to do the
	 * opposite. Verify that the correct helper routines are called.
	 ******************************************************************/

	reset_times_called();
	(void)memset(&simd_ctx_nwd, 0, sizeof(struct simd_context));
	(void)memset(&simd_ctx_rl, 0, sizeof(struct simd_context));
	simd_test_helpers_setup_id_regs(true, false);

	simd_init();

	ret1 = simd_get_cpu_config(&test_simd_cfg);

	CHECK_TRUE(ret1 == 0);

	/* Initialise NS and RL SVE contexts with the CPU SIMD config */
	ret1 = simd_context_init(SIMD_OWNER_REL1, &simd_ctx_rl, &test_simd_cfg);
	ret2 = simd_context_init(SIMD_OWNER_NWD, &simd_ctx_nwd, &test_simd_cfg);

	CHECK_TRUE(ret1 == 0);
	CHECK_TRUE(ret2 == 0);

	/*
	 * Set SVE hint bit for NS SVE ctx. This denotes that there is no live
	 * SVE-specific live state in NS world.
	 */
	simd_update_smc_sve_hint(&simd_ctx_nwd, true);

	/* Set callbacks for relevant helper routines */
	cb_fpu_save.fpu_save_restore_regs = fpu_save_regs_cb;
	cb_fpu_restore.fpu_save_restore_regs = fpu_restore_regs_cb;
	cb_sve_save.sve_save_restore_regs = sve_save_regs_cb;
	cb_sve_restore.sve_save_restore_regs = sve_restore_regs_cb;
	cb_sve_clear_p_ffr.sve_clear_regs = sve_clear_p_ffr_regs_cb;

	simd_test_register_callback(FPU_SAVE_REGS, cb_fpu_save);
	simd_test_register_callback(FPU_RESTORE_REGS, cb_fpu_restore);
	simd_test_register_callback(SVE_SAVE_REGS, cb_sve_save);
	simd_test_register_callback(SVE_RESTORE_REGS, cb_sve_restore);
	simd_test_register_callback(SVE_CLEAR_P_FFR_REGS, cb_sve_clear_p_ffr);

	/*
	 * Do the NS SVE -> RL SVE switch. Since SVE hint bit is set, expect the
	 * FPU Q registers to be saved, as opposed to the SVE Z registers.
	 */
	(void)simd_context_switch(&simd_ctx_nwd, &simd_ctx_rl);

	CHECK_TRUE(helpers_times_called[FPU_SAVE_REGS] == 1);
	CHECK_TRUE(helpers_times_called[SVE_RESTORE_REGS] == 1);
	CHECK_TRUE(helpers_times_called[SVE_SAVE_REGS] == 0);

	reset_times_called();

	/*
	 * Do the RL SVE -> NS SVE switch. Since SVE hint bit is set, expect the
	 * FPU Q registers to be restored, as opposed to the SVE Z registers. In
	 * addition, expect the sve_clear_p_ffr_registers() helper routine to be
	 * called. The P and FFR registers hold values from previous usage, so
	 * they should be explicitly cleared.
	 */
	(void)simd_context_switch(&simd_ctx_rl, &simd_ctx_nwd);

	CHECK_TRUE(helpers_times_called[SVE_SAVE_REGS] == 1);
	CHECK_TRUE(helpers_times_called[FPU_RESTORE_REGS] == 1);
	CHECK_TRUE(helpers_times_called[SVE_CLEAR_P_FFR_REGS] == 1);
	CHECK_TRUE(helpers_times_called[SVE_RESTORE_REGS] == 0);
}

TEST(simd, simd_update_smc_sve_hint_TC1)
{
	struct simd_context simd_ctx_nwd;
	struct simd_context simd_ctx_rl;
	struct simd_config test_simd_cfg = { 0 };
	union simd_cbs cb_save;
	union simd_cbs cb_restore;
	union simd_cbs cb_sve_clear_p_ffr;
	int ret1, ret2;

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Initialise two FPU contexts, one with NS owner and one with
	 * Realm owner. Try to enable SVE hint bit for NS FPU context.
	 * Verify that the SVE hint bit is not set by checking that context
	 * switching between these two contexts proceeds in the same way as
	 * in simd_context_switch_TC1.
	 ******************************************************************/

	reset_times_called();
	(void)memset(&simd_ctx_nwd, 0, sizeof(struct simd_context));
	(void)memset(&simd_ctx_rl, 0, sizeof(struct simd_context));
	simd_test_helpers_setup_id_regs(false, false);

	simd_init();

	/* Initialise NS and RL FPU contexts */
	ret1 = simd_context_init(SIMD_OWNER_REL1, &simd_ctx_rl, &test_simd_cfg);
	CHECK_TRUE(ret1 == 0);

	/* Initialise NS ctx. */
	ret1 = simd_get_cpu_config(&test_simd_cfg);
	CHECK_TRUE(ret1 == 0);
	ret2 = simd_context_init(SIMD_OWNER_NWD, &simd_ctx_nwd, &test_simd_cfg);
	CHECK_TRUE(ret2 == 0);

	/*
	 * Set SVE hint bit for NS FPU ctx. We expect nothing to happen, since
	 * NS SIMD ctx does not have SVE.
	 */
	simd_update_smc_sve_hint(&simd_ctx_nwd, true);

	/*
	 * Check that the resulting context switches proceed as expected, and
	 * that the sve_clear_p_ffr_registers() helper routine isn't called when
	 * the NS ctx is restored.
	 */
	cb_save.fpu_save_restore_regs = fpu_save_regs_cb;
	cb_restore.fpu_save_restore_regs = fpu_restore_regs_cb;
	cb_sve_clear_p_ffr.sve_clear_regs = sve_clear_p_ffr_regs_cb;

	simd_test_register_callback(FPU_SAVE_REGS, cb_save);
	simd_test_register_callback(FPU_RESTORE_REGS, cb_restore);
	simd_test_register_callback(SVE_CLEAR_P_FFR_REGS, cb_sve_clear_p_ffr);

	/* Do the NS FPU -> RL FPU switch. */
	(void)simd_context_switch(&simd_ctx_nwd, &simd_ctx_rl);

	CHECK_TRUE(helpers_times_called[FPU_SAVE_REGS] == 1);
	CHECK_TRUE(helpers_times_called[FPU_RESTORE_REGS] == 1);

	reset_times_called();

	/* Do the RL FPU -> NS FPU switch. */
	(void)simd_context_switch(&simd_ctx_rl, &simd_ctx_nwd);

	CHECK_TRUE(helpers_times_called[FPU_SAVE_REGS] == 1);
	CHECK_TRUE(helpers_times_called[FPU_RESTORE_REGS] == 1);
	CHECK_TRUE(helpers_times_called[SVE_CLEAR_P_FFR_REGS] == 0);
}
