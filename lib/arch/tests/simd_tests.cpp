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
