/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch.h>
#include <arch_helpers.h>
#include <host_utils.h>
#include <simd_callbacks.h>
#include <simd_private.h>
#include <simd_test_helpers.h>
#include <test_helpers.h>

static void simd_test_helpers_setup_sysregs(void)
{
	int __unused ret;

	(void)host_util_set_default_sysreg_cb("cptr_el2", 0UL);
	(void)host_util_set_default_sysreg_cb("id_aa64pfr0_el1", 0UL);
	(void)host_util_set_default_sysreg_cb("id_aa64pfr1_el1", 0UL);
	(void)host_util_set_default_sysreg_cb("zcr_el2", 0UL);
	ret = host_util_set_default_sysreg_cb("svcr", 0UL);

	assert(ret == 0);
}

void simd_test_helpers_init(void)
{
	test_helpers_init();
	test_helpers_rmm_start(true);
	simd_test_helpers_setup_sysregs();
	host_util_set_cpuid(0U);
	test_helpers_expect_assert_fail(false);
	simd_reset();
}

void simd_test_helpers_teardown(void)
{
	host_util_zero_sysregs_and_cbs();

	for (unsigned int id = 0U; id < SIMD_CB_IDS_MAX; id++) {
		simd_test_unregister_callback(id);
	}
}

void simd_test_helpers_setup_id_regs(bool is_sve_en, bool is_sme_en)
{
	u_register_t id_aa64pfr0_el1 = read_id_aa64pfr0_el1();
	u_register_t id_aa64pfr1_el1 = read_id_aa64pfr1_el1();

	if (is_sve_en) {
		id_aa64pfr0_el1 |= INPLACE(ID_AA64PFR0_EL1_SVE, 1UL);
	} else {
		id_aa64pfr0_el1 |= INPLACE(ID_AA64PFR0_EL1_SVE, 0UL);
	}

	host_write_sysreg("id_aa64pfr0_el1", id_aa64pfr0_el1);

	if (is_sme_en) {
		id_aa64pfr1_el1 |= INPLACE(ID_AA64PFR1_EL1_SME, 1UL);
	} else {
		id_aa64pfr1_el1 |= INPLACE(ID_AA64PFR1_EL1_SME, 0UL);
	}

	host_write_sysreg("id_aa64pfr1_el1", id_aa64pfr1_el1);
}
