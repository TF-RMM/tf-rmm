/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch_features.h>
#include <debug.h>
#include <host_utils.h>
#include <mec.h>
#include <stdlib.h>
#include <test_helpers.h>

static bool is_mecid_a1_el2_modified;
static bool is_mecid_a1_el2_read;
static bool is_vmecid_p_el2_modified;
static bool is_vmecid_p_el2_read;

static struct mec_state_s g_mec_state;

/*
 * Custom callback to access MECID_A1_EL2 for reading.
 */
static u_register_t mecid_a1_el2_rd_cb(u_register_t *reg)
{
	is_mecid_a1_el2_read = true;
	return *reg;
}

/*
 * Custom callback to access MECID_A1_EL2 for writing.
 */
static void mecid_a1_el2_wr_cb(u_register_t val, u_register_t *reg)
{
	is_mecid_a1_el2_modified = true;
	*reg = val;
}

/*
 * Custom callback to access VMECID_P_EL2 for reading.
 */
static u_register_t vmecid_p_el2_rd_cb(u_register_t *reg)
{
	is_vmecid_p_el2_read = true;
	return *reg;
}

/*
 * Custom callback to access VMECID_P_EL2 for writing.
 */
static void vmecid_p_el2_wr_cb(u_register_t val, u_register_t *reg)
{
	is_vmecid_p_el2_modified = true;
	*reg = val;
}

static void no_mec_test_helpers_arch_init(void)
{
	uint64_t _id_aa64mmfr3_el1 = INPLACE(ID_AA64MMFR3_EL1_TCRX, 1UL) |
					INPLACE(ID_AA64MMFR3_EL1_SCTLRX, 1UL);

	WRITE_CACHED_REG(id_aa64mmfr3_el1, _id_aa64mmfr3_el1);
}

static void no_sctlr2_test_helpers_arch_init(void)
{
	uint64_t _id_aa64mmfr3_el1 = INPLACE(ID_AA64MMFR3_EL1_MEC, 1UL);

	WRITE_CACHED_REG(id_aa64mmfr3_el1, _id_aa64mmfr3_el1);
}

static void mec_test_helpers_arch_restore(void)
{
	uint64_t _id_aa64mmfr3_el1 = INPLACE(ID_AA64MMFR3_EL1_MEC, 1UL) |
					INPLACE(ID_AA64MMFR3_EL1_TCRX, 1UL) |
					INPLACE(ID_AA64MMFR3_EL1_SCTLRX, 1UL);

	WRITE_CACHED_REG(id_aa64mmfr3_el1, _id_aa64mmfr3_el1);
}

static void mec_reset_sysregs_and_callbacks(void)
{
	unsigned int retval __unused;

	/* reset the MMU register callbacks */
	retval = host_util_set_default_sysreg_cb("tcr2_el2", 0UL);
	retval |= host_util_set_default_sysreg_cb("sctlr_el2", 0UL);
	retval |= host_util_set_default_sysreg_cb("sctlr2_el2", 0UL);
	retval |= host_util_set_default_sysreg_cb("mecid_p0_el2", 0UL);
	retval |= host_util_set_default_sysreg_cb("mecid_p1_el2", 0UL);
	retval |= host_util_set_default_sysreg_cb("mecid_a0_el2", 0UL);
	retval |= host_util_set_default_sysreg_cb("mecid_a1_el2", 0UL);
	retval |= host_util_set_default_sysreg_cb("vmecid_p_el2", 0UL);
	retval |= host_util_set_default_sysreg_cb("vmecid_a_el2", 0UL);
	retval |= host_util_set_default_sysreg_cb("mecidr_el2",
				INPLACE(MECIDR_MECIDWIDTHM1, 0xFFFF));

	if (retval != 0) {
		ERROR("%s: Failed to reset mec sysreg callbacks\n", __func__);
		exit(1);
	}

	is_mecid_a1_el2_modified = false;
	is_mecid_a1_el2_read = false;
	is_vmecid_p_el2_modified = false;
	is_vmecid_p_el2_read = false;
}

static void release_all_mecids(void)
{
	unsigned int max_mecid = mecid_max();

	for (unsigned int i = MECID_PRIVATE_START; i <= max_mecid; i++) {
		mecid_free(i);
	}
}

void mec_test_setup(void)
{
	test_helpers_init();

	mec_init_state((uintptr_t)&g_mec_state, sizeof(g_mec_state));

	release_all_mecids();

	mec_reset_sysregs_and_callbacks();
}

void mec_test_teardown(void)
{
	mec_test_reset();
}

void no_mec_test_setup(void)
{
	test_helpers_init();

	mec_init_state((uintptr_t)&g_mec_state, sizeof(g_mec_state));

	no_mec_test_helpers_arch_init();

	mec_reset_sysregs_and_callbacks();
}

void no_mec_test_teardown(void)
{
	mec_test_reset();

	mec_test_helpers_arch_restore();
}

void no_sctlr2_mec_test_setup(void)
{
	test_helpers_init();

	mec_init_state((uintptr_t)&g_mec_state, sizeof(g_mec_state));

	no_sctlr2_test_helpers_arch_init();

	mec_reset_sysregs_and_callbacks();
}

void no_sctlr2_mec_test_teardown(void)
{
	mec_test_reset();

	mec_test_helpers_arch_restore();
}

int register_custom_mecid_a1_el2_callbacks(void)
{
	return host_util_set_sysreg_cb("mecid_a1_el2",
			mecid_a1_el2_rd_cb,
			mecid_a1_el2_wr_cb,
			0UL);
}

bool check_mecid_a1_el2_modified_clear(void)
{
	bool result = is_mecid_a1_el2_modified;
	is_mecid_a1_el2_modified = false;
	return result;
}

bool check_mecid_a1_el2_read_clear(void)
{
	bool result = is_mecid_a1_el2_read;
	is_mecid_a1_el2_read = false;
	return result;
}

int register_custom_vmecid_p_el2_callbacks(void)
{
	return host_util_set_sysreg_cb("vmecid_p_el2",
			vmecid_p_el2_rd_cb,
			vmecid_p_el2_wr_cb,
			0UL);
}

bool check_vmecid_p_el2_modified_clear(void)
{
	bool result = is_vmecid_p_el2_modified;
	is_vmecid_p_el2_modified = false;
	return result;
}

bool check_vmecid_p_el2_read_clear(void)
{
	bool result = is_vmecid_p_el2_read;
	is_vmecid_p_el2_read = false;
	return result;
}

void reset_mecidr_el2(unsigned int value)
{
	unsigned int retval __unused;

	if (value > 0xFFFFU) {
		ERROR("%s: Invalid mecid value\n", __func__);
		exit(1);
	}

	retval = host_util_set_default_sysreg_cb("mecidr_el2",
				INPLACE(MECIDR_MECIDWIDTHM1, value));

	if (retval != 0) {
		ERROR("%s: Failed to reset mecidr_el2 callbacks\n", __func__);
		exit(1);
	}
}
