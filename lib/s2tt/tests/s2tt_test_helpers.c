/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch_features.h>
#include <assert.h>
#include <errno.h>
#include <host_utils.h>
#include <limits.h>
#include <ripas.h>
#include <s2tt.h>
#include <s2tt_pvt_defs.h>
#include <s2tt_test_helpers.h>
#include <stdbool.h>
#include <stdlib.h>
#include <string.h>
#include <test_helpers.h>
#include <utils_def.h>
#include <xlat_defs.h>

static bool lpa2_enabled;

/*
 * Helper function to perform any system register initialization
 * needed for the tests.
 */
static void s2tt_test_helpers_arch_init(bool lpa2_en)
{
	unsigned int retval __unused;
	uint64_t id_aa64mmfr0_el0 = INPLACE(ID_AA64MMFR0_EL1_TGRAN4_2,
					    ID_AA64MMFR0_EL1_TGRAN4_2_TGRAN4);

	/*
	 * Enable the platform. We don't need support for several CPUs
	 * on this testsuite, so keep it disabled for simplicity.
	 */
	test_helpers_rmm_start(false);

	/*
	 * Reset the sysreg state so that we can setup
	 * custom values for the tests
	 */
	host_util_zero_sysregs_and_cbs();

	/* Setup id_aa64mmfr0_el1 */
	if (lpa2_en == true) {
		id_aa64mmfr0_el0 |= INPLACE(ID_AA64MMFR0_EL1_PARANGE, 6UL) |
				    INPLACE(ID_AA64MMFR0_EL1_TGRAN4,
					    ID_AA64MMFR0_EL1_TGRAN4_LPA2);
	} else {
		id_aa64mmfr0_el0 |= INPLACE(ID_AA64MMFR0_EL1_PARANGE, 5UL) |
				    INPLACE(ID_AA64MMFR0_EL1_TGRAN4,
					    ID_AA64MMFR0_EL1_TGRAN4_SUPPORTED);
	}
	lpa2_enabled = lpa2_en;

	retval = host_util_set_default_sysreg_cb("id_aa64mmfr0_el1",
						 id_aa64mmfr0_el0);

	assert(retval == 0);

	/* Make sure current cpu id is 0 (primary processor) */
	host_util_set_cpuid(0U);

	test_helpers_expect_assert_fail(false);
}

void s2tt_test_helpers_setup(bool lpa2)
{
	test_helpers_init();
	s2tt_test_helpers_arch_init(lpa2);
}

unsigned long s2tt_test_helpers_lvl_mask(long level)
{
	assert(level <= S2TT_TEST_HELPERS_MAX_LVL);

	unsigned int levels = (unsigned int)(S2TT_TEST_HELPERS_MAX_LVL - level);
	unsigned int lsb = GRANULE_SHIFT + (levels * S2TTE_STRIDE);
	unsigned int msb = arch_feat_get_pa_width() - 1U;

	return BIT_MASK_ULL(msb, lsb);
}

unsigned long s2tt_test_helpers_s2tte_oa_mask(void)
{
	unsigned long mask = s2tt_test_helpers_lvl_mask(
						S2TT_TEST_HELPERS_MAX_LVL);

	if (is_feat_lpa2_4k_2_present() == true) {
		mask |= MASK(S2TT_TEST_MSB);
		mask &= ~MASK(S2TT_TEST_OA_MSB);
	}

	return mask;
}

unsigned long s2tt_test_helpers_s2tte_to_pa(unsigned long s2tte, long level)
{
	unsigned long pa = s2tte & s2tt_test_helpers_lvl_mask(level);

	if (is_feat_lpa2_4k_2_present() == true) {
		pa &= ~MASK(S2TT_TEST_MSB);
		pa |= INPLACE(S2TT_TEST_OA_MSB, EXTRACT(S2TT_TEST_MSB, s2tte));
	}

	return pa;
}

unsigned long s2tt_test_helpers_pa_to_s2tte(unsigned long pa, long level)
{
	unsigned long s2tte;

	pa &= s2tt_test_helpers_lvl_mask(level);

	if (is_feat_lpa2_4k_2_present() == true) {
		s2tte = pa | INPLACE(S2TT_TEST_MSB, EXTRACT(S2TT_TEST_OA_MSB, pa));
		s2tte &= ~MASK(S2TT_TEST_OA_MSB);
	} else {
		s2tte = pa;
	}

	return s2tte;
}

unsigned long s2tt_test_helpers_gen_addr(long level, bool aligned)
{
	unsigned int levels, lsb;
	unsigned long addr;

	/*
	 * We allow to get addresses aligned to one level below the minimum
	 * so we can use that address to create a table @level starting
	 * at such address.
	 */
	assert(level >= s2tt_test_helpers_min_table_lvl() - 1);
	assert(level <= S2TT_TEST_HELPERS_MAX_LVL);

	levels = S2TT_TEST_HELPERS_MAX_LVL - level;
	lsb = GRANULE_SHIFT + (levels * S2TTE_STRIDE);

	do {
		unsigned int shift = (level <= S2TT_TEST_HELPERS_MIN_LVL_LPA2) ?
				LM1_XLAT_ADDRESS_SHIFT : L0_XLAT_ADDRESS_SHIFT;

		addr = test_helpers_get_rand_in_range((1UL << lsb), ULONG_MAX);
		addr &= ((1UL << shift) - 1UL);
	} while (addr == 0UL);

	return aligned ? (addr & s2tt_test_helpers_lvl_mask(level)) : addr;
}

unsigned long s2tt_test_helpers_s2tte_to_attrs(unsigned long tte, bool ns)
{
	unsigned long attrs_mask;

	if (ns) {
		attrs_mask = S2TTE_NS_ATTR_RMM | S2TT_DESC_TYPE_MASK | S2TTE_NS_ATTR_MASK;
		if (!is_feat_lpa2_4k_2_present()) {
			attrs_mask |= S2TTE_SH_MASK;
		}
	} else {
		attrs_mask = ((is_feat_lpa2_4k_2_present() == true) ?
			S2TTE_ATTRS_LPA2_MASK :
			S2TTE_ATTRS_MASK) | S2TT_DESC_TYPE_MASK;
	}

	return tte & attrs_mask;
}

unsigned long s2tt_test_helpers_gen_ns_attrs(bool host, bool reserved)
{
	unsigned long attrs;
	bool done;

	if (host == true) {
		/* Generate a random set of attributes coming from the host */
		do {
			bool inv_attrs;

			attrs = test_helpers_get_rand_in_range(0UL, ULONG_MAX);
			attrs &= S2TTE_NS_ATTR_MASK;

			/* Find out if we are done or not */
			inv_attrs = ((attrs & S2TTE_MEMATTR_MASK) ==
						S2TTE_MEMATTR_FWB_RESERVED);
			done = (reserved == inv_attrs);
		} while (!done);
	} else {
		/* Setup the NS TTE attributes that don't come from the host */
		attrs = S2TTE_NS_ATTR_RMM;
	}

	return attrs;
}

unsigned long s2tt_test_helpers_gen_attrs(bool invalid, long level)
{
	unsigned long attrs = (is_feat_lpa2_4k_2_present() == true) ?
		S2TTE_ATTRS_LPA2 : S2TTE_ATTRS;

	if (invalid == true) {
		return attrs | S2TT_TEST_INVALID_DESC;
	}

	return ((level == S2TT_TEST_HELPERS_MAX_LVL) ?
			S2TT_TEST_PAGE_DESC : S2TT_TEST_BLOCK_DESC) | attrs;
}

long s2tt_test_helpers_min_table_lvl(void)
{
	if (is_feat_lpa2_4k_2_present() == true) {
		return S2TT_TEST_HELPERS_MIN_LVL_LPA2;
	}

	return S2TT_TEST_HELPERS_MIN_LVL;
}

long s2tt_test_helpers_min_block_lvl(void)
{
	return S2TT_MIN_BLOCK_LEVEL;
}

unsigned long s2tt_test_helpers_get_entry_va_space_size(long level)
{
	assert(level >= s2tt_test_helpers_min_table_lvl());
	assert(level <= S2TT_TEST_HELPERS_MAX_LVL);

	unsigned long levels = S2TT_TEST_HELPERS_MAX_LVL - level;

	return 1UL << (GRANULE_SHIFT + (S2TTE_STRIDE * levels));
}

unsigned long s2tt_test_helpers_get_idx_from_addr(unsigned long addr,
						  long level)
{
	assert(level >= s2tt_test_helpers_min_table_lvl());
	assert(level <= S2TT_TEST_HELPERS_MAX_LVL);
	assert((addr & ~((1UL << arch_feat_get_pa_width()) - 1UL)) == 0UL);

	unsigned int levels = (unsigned int)(S2TT_TEST_HELPERS_MAX_LVL - level);
	unsigned int lsb = GRANULE_SHIFT + (levels * S2TTE_STRIDE);

	return (addr >> lsb) & ((1UL << S2TTE_STRIDE) - 1UL);
}

bool s2tt_test_helpers_lpa2_enabled(void)
{
	return lpa2_enabled;
}

unsigned long s2tt_test_create_assigned(const struct s2tt_context *s2tt_ctx,
					unsigned long pa, long level,
					unsigned long ripas)
{
	if (ripas == S2TTE_INVALID_RIPAS_EMPTY) {
		return s2tte_create_assigned_empty(s2tt_ctx, pa, level);
	} else if (ripas == S2TTE_INVALID_RIPAS_DESTROYED) {
		return s2tte_create_assigned_destroyed(s2tt_ctx, pa, level);
	} else if (ripas == S2TTE_INVALID_RIPAS_RAM) {
		return s2tte_create_assigned_ram(s2tt_ctx, pa, level);
	}

	return s2tte_create_assigned_ns(s2tt_ctx, pa, level);
}

unsigned long s2tt_test_create_unassigned(const struct s2tt_context *s2tt_ctx,
					  unsigned long ripas)
{
	if (ripas == S2TTE_INVALID_RIPAS_EMPTY) {
		return s2tte_create_unassigned_empty(s2tt_ctx);
	} else if (ripas == S2TTE_INVALID_RIPAS_DESTROYED) {
		return s2tte_create_unassigned_destroyed(s2tt_ctx);
	} else if (ripas == S2TTE_INVALID_RIPAS_RAM) {
		return s2tte_create_unassigned_ram(s2tt_ctx);
	}

	return s2tte_create_unassigned_ns(s2tt_ctx);
}
