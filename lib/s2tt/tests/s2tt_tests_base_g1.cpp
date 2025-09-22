/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <CppUTest/CommandLineTestRunner.h>
#include <CppUTest/TestHarness.h>

extern "C" {
#include <cpuid.h>
#include <granule_types.h>
#include <host_harness.h>
#include <host_utils.h>
#include <status.h>
#include <stdlib.h>
#include <string.h>
#include <s2tt_pvt_defs.h>
#include <s2tt_test_helpers.h>
#include <ripas.h>
#include <s2tt.h>	/* Interface to exercise */
#include <s2tt_ap.h>
#include <test_helpers.h>
#include <unistd.h>
#include <utils_def.h>
}

void s2tte_create_unassigned_empty_tc1(void)
{
	/***************************************************************
	 * TEST CASE 1:
	 *
	 * Create an unassigned empty S2TTE and verify that the
	 * S2TTE is valid.
	 ***************************************************************/

	unsigned long ap = test_helpers_get_rand_in_range(0UL, ULONG_MAX);
	unsigned long expected_tte = S2TTE_INVALID_RIPAS_EMPTY |
				     S2TTE_INVALID_HIPAS_UNASSIGNED;
	struct s2tt_context s2tt_ctx;

	(void)memset(&s2tt_ctx, 0, sizeof(s2tt_ctx));

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 and s2tt_ctx.indirect_s2ap ar of use
	 * on this API, so the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
	s2tt_ctx.indirect_s2ap = s2tt_test_helpers_s2pie_enabled();

	if (s2tt_ctx.indirect_s2ap) {
		expected_tte = s2tte_set_pi_index(&s2tt_ctx, expected_tte,
						 S2TTE_DEF_BASE_PERM_IDX);
		expected_tte &= ~MASK(S2TTE_PO_INDEX);
		expected_tte |= ap & MASK(S2TTE_PO_INDEX);
		expected_tte |= S2TTE_DIRTY_BIT;
	} else {
		expected_tte |= (ap & S2TTE_PERM_MASK);
	}

	/* s2tt_context argument is ignored */
	unsigned long tte = s2tte_create_unassigned_empty(
			(const struct s2tt_context *)&s2tt_ctx, ap);

	UNSIGNED_LONGS_EQUAL(expected_tte, tte);
}

void s2tte_create_unassigned_ram_tc1(void)
{
	/***************************************************************
	 * TEST CASE 1:
	 *
	 * Create an unassigned ram S2TTE and verify that the
	 * S2TTE is valid.
	 ***************************************************************/

	unsigned long ap = test_helpers_get_rand_in_range(0UL, ULONG_MAX);
	unsigned long expected_tte = S2TTE_INVALID_RIPAS_RAM |
				     S2TTE_INVALID_HIPAS_UNASSIGNED;
	struct s2tt_context s2tt_ctx;

	(void)memset(&s2tt_ctx, 0, sizeof(s2tt_ctx));

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 and s2tt_ctx.indirect_s2ap ar of use
	 * on this API, so the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
	s2tt_ctx.indirect_s2ap = s2tt_test_helpers_s2pie_enabled();

	if (s2tt_ctx.indirect_s2ap) {
		expected_tte = s2tte_set_pi_index(&s2tt_ctx, expected_tte,
						 S2TTE_DEF_BASE_PERM_IDX);
		expected_tte &= ~MASK(S2TTE_PO_INDEX);
		expected_tte |= ap & MASK(S2TTE_PO_INDEX);
		expected_tte |= S2TTE_DIRTY_BIT;
	} else {
		expected_tte |= (ap & S2TTE_PERM_MASK);
	}

	/* s2tt_context argument is ignored */
	unsigned long tte = s2tte_create_unassigned_ram(
			(const struct s2tt_context *)&s2tt_ctx, ap);

	UNSIGNED_LONGS_EQUAL(expected_tte, tte);
}

void s2tte_create_unassigned_destroyed_tc1(void)
{
	/***************************************************************
	 * TEST CASE 1:
	 *
	 * Create an unassigned destroyed S2TTE and verify that the
	 * S2TTE is valid.
	 ***************************************************************/

	unsigned long ap = test_helpers_get_rand_in_range(0UL, ULONG_MAX);
	unsigned long expected_tte = S2TTE_INVALID_RIPAS_DESTROYED |
				     S2TTE_INVALID_HIPAS_UNASSIGNED;
	struct s2tt_context s2tt_ctx;

	(void)memset(&s2tt_ctx, 0, sizeof(s2tt_ctx));

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 and s2tt_ctx.indirect_s2ap ar of use
	 * on this API, so the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
	s2tt_ctx.indirect_s2ap = s2tt_test_helpers_s2pie_enabled();

	if (s2tt_ctx.indirect_s2ap) {
		expected_tte = s2tte_set_pi_index(&s2tt_ctx, expected_tte,
						 S2TTE_DEF_BASE_PERM_IDX);
		expected_tte &= ~MASK(S2TTE_PO_INDEX);
		expected_tte |= ap & MASK(S2TTE_PO_INDEX);
		expected_tte |= S2TTE_DIRTY_BIT;
	} else {
		expected_tte |= (ap & S2TTE_PERM_MASK);
	}

	/* s2tt_context argument is ignored */
	unsigned long tte = s2tte_create_unassigned_destroyed(
			(const struct s2tt_context *)&s2tt_ctx, ap);

	UNSIGNED_LONGS_EQUAL(expected_tte, tte);
}

void s2tte_create_unassigned_ns_tc1(void)
{
	/***************************************************************
	 * TEST CASE 1:
	 *
	 * Create an unassigned ns S2TTE and verify that the
	 * S2TTE is valid.
	 ***************************************************************/

	unsigned long expected_tte = S2TTE_NS | S2TTE_INVALID_HIPAS_UNASSIGNED;

	/* s2tt_context argument is ignored */
	unsigned long tte = s2tte_create_unassigned_ns(NULL, 0UL);

	UNSIGNED_LONGS_EQUAL(expected_tte, tte);
}

void s2tte_create_assigned_destroyed_tc1(void)
{
	/***************************************************************
	 * TEST CASE 1:
	 *
	 * Create an assigned destroyed S2TTE with valid parameters and
	 * verify that the S2TTE is valid.
	 ***************************************************************/

	/* Test for each possible level */
	for (long i = s2tt_test_helpers_min_block_lvl();
	     i <= S2TT_TEST_HELPERS_MAX_LVL; i++) {

		unsigned long pa = s2tt_test_helpers_gen_addr(i, true);
		unsigned long tte;
		unsigned long ap = test_helpers_get_rand_in_range(0UL, ULONG_MAX);
		unsigned long ap_mask = s2tt_test_generate_ap_mask();
		s2tt_context s2tt_ctx;

		(void)memset(&s2tt_ctx, 0, sizeof(s2tt_ctx));

		/*
		 * Generate an s2tt context to be used for the test.
		 * only s2tt_ctx.enable_lpa2 and s2tt_ctx.indirect_s2ap ar of use
		 * on this API, so the rest of them can be uninitialized.
		 */
		s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
		s2tt_ctx.indirect_s2ap = s2tt_test_helpers_s2pie_enabled();

		tte = s2tte_create_assigned_destroyed((const struct s2tt_context *)&s2tt_ctx,
						      pa, i, ap);

		/* Validate the address */
		UNSIGNED_LONGS_EQUAL(
				s2tt_test_helpers_s2tte_to_pa(tte, i), pa);

		/* Validate the RIPAS */
		UNSIGNED_LONGS_EQUAL((tte & S2TTE_INVALID_RIPAS_MASK),
					     S2TTE_INVALID_RIPAS_DESTROYED);

		/* Validate the HIPAS */
		UNSIGNED_LONGS_EQUAL((tte & S2TTE_INVALID_HIPAS_MASK),
						S2TTE_INVALID_HIPAS_ASSIGNED);

		/* Validate the Access Permissions */
		if (s2tt_ctx.indirect_s2ap) {
			UNSIGNED_LONGS_EQUAL(s2tte_get_pi_index(&s2tt_ctx, tte),
					     S2TTE_DEF_BASE_PERM_IDX);
			UNSIGNED_LONGS_EQUAL((ap & MASK(S2TTE_PO_INDEX)),
					     (tte & MASK(S2TTE_PO_INDEX)));
		} else {
			UNSIGNED_LONGS_EQUAL((ap & ap_mask), (tte & ap_mask));
		}

		/* The rest of the fields must be all 0 */
		if (s2tt_ctx.indirect_s2ap) {
			ap_mask |= S2TTE_DIRTY_BIT;
		}
		UNSIGNED_LONGS_EQUAL(
			(tte & ~(s2tt_test_helpers_s2tte_oa_mask() |
			S2TTE_INVALID_RIPAS_MASK |
			S2TTE_INVALID_HIPAS_MASK | ap_mask)), 0UL);
	}
}

void s2tte_create_assigned_destroyed_tc2(void)
{
	/***************************************************************
	 * TEST CASE 2:
	 *
	 * For a valid level, try to create an assigned-destroyed S2TTE
	 * with an unaligned address.
	 ***************************************************************/

	long level = (long)test_helpers_get_rand_in_range(
			(unsigned long)s2tt_test_helpers_min_block_lvl(),
			(unsigned long)S2TT_TEST_HELPERS_MAX_LVL);
	unsigned long pa = s2tt_test_helpers_gen_addr(level, true);
	unsigned long ap = test_helpers_get_rand_in_range(0UL, ULONG_MAX);
	struct s2tt_context s2tt_ctx;

	(void)memset(&s2tt_ctx, 0, sizeof(s2tt_ctx));

	pa += test_helpers_get_rand_in_range(1UL, (unsigned long)GRANULE_SIZE - 1UL);

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 and s2tt_ctx.indirect_s2ap ar of use
	 * on this API, so the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
	s2tt_ctx.indirect_s2ap = s2tt_test_helpers_s2pie_enabled();

	test_helpers_expect_assert_fail(true);
	(void)s2tte_create_assigned_destroyed((const struct s2tt_context *)&s2tt_ctx,
					      pa, level, ap);
	test_helpers_fail_if_no_assert_failed();
}

void s2tte_create_assigned_destroyed_tc3(void)
{
	/***************************************************************
	 * TEST CASE 3:
	 *
	 * For a valid address, try to create an assigned-destroyed
	 * S2TTE with a level below the minimum.
	 ***************************************************************/

	long level = s2tt_test_helpers_min_block_lvl() - 1L;
	unsigned long pa = 0UL; /* Valid for any level */
	unsigned long ap = 0UL; /* Valid on any level */
	struct s2tt_context s2tt_ctx;

	(void)memset(&s2tt_ctx, 0, sizeof(s2tt_ctx));

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 and s2tt_ctx.indirect_s2ap ar of use
	 * on this API, so the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
	s2tt_ctx.indirect_s2ap = s2tt_test_helpers_s2pie_enabled();

	test_helpers_expect_assert_fail(true);
	(void)s2tte_create_assigned_destroyed((const struct s2tt_context *)&s2tt_ctx,
					      pa, level, ap);
	test_helpers_fail_if_no_assert_failed();
}

void s2tte_create_assigned_destroyed_tc4(void)
{
	/***************************************************************
	 * TEST CASE 4:
	 *
	 * For a valid address, try to create an assigned-destroyed
	 * S2TTE with a level above the maximum.
	 ***************************************************************/

	long level = S2TT_TEST_HELPERS_MAX_LVL + 1L;
	unsigned long pa = 0UL; /* Valid for any level */
	unsigned long ap = 0UL; /* Valid on any level */
	struct s2tt_context s2tt_ctx;

	(void)memset(&s2tt_ctx, 0, sizeof(s2tt_ctx));

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 and s2tt_ctx.indirect_s2ap ar of use
	 * on this API, so the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
	s2tt_ctx.indirect_s2ap = s2tt_test_helpers_s2pie_enabled();

	test_helpers_expect_assert_fail(true);
	(void)s2tte_create_assigned_destroyed((const struct s2tt_context *)&s2tt_ctx,
					      pa, level, ap);
	test_helpers_fail_if_no_assert_failed();
}

void s2tte_create_assigned_destroyed_tc5(void)
{
	/***************************************************************
	 * TEST CASE 5:
	 *
	 * For a valid address, try to create an assigned-destroyed
	 * S2TTE with a null s2tt_context structure.
	 ***************************************************************/

	long level = S2TT_TEST_HELPERS_MAX_LVL;
	unsigned long pa = 0UL; /* Valid for any level */
	unsigned long ap = 0UL; /* Valid on any level */

	test_helpers_expect_assert_fail(true);
	(void)s2tte_create_assigned_destroyed((const struct s2tt_context *)NULL,
					      pa, level, ap);
	test_helpers_fail_if_no_assert_failed();
}

void s2tte_create_assigned_empty_tc1(void)
{
	/***************************************************************
	 * TEST CASE 1:
	 *
	 * Create an assigned empty S2TTE with valid parameters and
	 * verify that the S2TTE is valid.
	 ***************************************************************/

	/* Test for each possible level */
	for (long i = s2tt_test_helpers_min_block_lvl();
	     i <= S2TT_TEST_HELPERS_MAX_LVL; i++) {

		unsigned long pa = s2tt_test_helpers_gen_addr(i, true);
		unsigned long tte;
		unsigned long ap = test_helpers_get_rand_in_range(0UL, ULONG_MAX);
		unsigned long ap_mask = s2tt_test_generate_ap_mask();
		s2tt_context s2tt_ctx;

		(void)memset(&s2tt_ctx, 0, sizeof(s2tt_ctx));

		/*
		 * Generate an s2tt context to be used for the test.
		 * only s2tt_ctx.enable_lpa2 and s2tt_ctx.indirect_s2ap ar of use
		 * on this API, so the rest of them can be uninitialized.
		 */
		s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
		s2tt_ctx.indirect_s2ap = s2tt_test_helpers_s2pie_enabled();

		tte = s2tte_create_assigned_empty((const struct s2tt_context *)&s2tt_ctx,
						  pa, i, ap);

		/* Validate the address */
		UNSIGNED_LONGS_EQUAL(
				s2tt_test_helpers_s2tte_to_pa(tte, i), pa);

		/* Validate the RIPAS */
		UNSIGNED_LONGS_EQUAL((tte & S2TTE_INVALID_RIPAS_MASK),
					     S2TTE_INVALID_RIPAS_EMPTY);

		/* Validate the HIPAS */
		UNSIGNED_LONGS_EQUAL((tte & S2TTE_INVALID_HIPAS_MASK),
						S2TTE_INVALID_HIPAS_ASSIGNED);

		/* Validate de Access Permissions */
		if (s2tt_ctx.indirect_s2ap) {
			UNSIGNED_LONGS_EQUAL(s2tte_get_pi_index(&s2tt_ctx, tte),
					     S2TTE_DEF_BASE_PERM_IDX);
			UNSIGNED_LONGS_EQUAL((ap & MASK(S2TTE_PO_INDEX)),
					     (tte & MASK(S2TTE_PO_INDEX)));
		} else {
			UNSIGNED_LONGS_EQUAL((ap & ap_mask), (tte & ap_mask));
		}

		/* The rest of the fields must be all 0 */
		if (s2tt_ctx.indirect_s2ap) {
			ap_mask |= S2TTE_DIRTY_BIT;
		}
		UNSIGNED_LONGS_EQUAL(
			(tte & ~(s2tt_test_helpers_s2tte_oa_mask() |
			S2TTE_INVALID_RIPAS_MASK |
			S2TTE_INVALID_HIPAS_MASK | ap_mask)), 0UL);
	}
}

void s2tte_create_assigned_empty_tc2(void)
{
	/***************************************************************
	 * TEST CASE 2:
	 *
	 * For a valid level, try to create an assigned-empty S2TTE
	 * with an unaligned address.
	 ***************************************************************/

	long level = (long)test_helpers_get_rand_in_range(
			(unsigned long)s2tt_test_helpers_min_block_lvl(),
			(unsigned long)S2TT_TEST_HELPERS_MAX_LVL);
	unsigned long pa = s2tt_test_helpers_gen_addr(level, true);
	unsigned long ap = 0UL; /* Valid on any level */
	struct s2tt_context s2tt_ctx;

	(void)memset(&s2tt_ctx, 0, sizeof(s2tt_ctx));

	pa += test_helpers_get_rand_in_range(1UL, (unsigned long)GRANULE_SIZE - 1UL);

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 and s2tt_ctx.indirect_s2ap ar of use
	 * on this API, so the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
	s2tt_ctx.indirect_s2ap = s2tt_test_helpers_s2pie_enabled();

	test_helpers_expect_assert_fail(true);
	(void)s2tte_create_assigned_empty((const struct s2tt_context *)&s2tt_ctx,
					   pa, level, ap);
	test_helpers_fail_if_no_assert_failed();
}

void s2tte_create_assigned_empty_tc3(void)
{
	/***************************************************************
	 * TEST CASE 3:
	 *
	 * For a valid address, try to create an assigned-empty
	 * S2TTE with a level below the minimum.
	 ***************************************************************/

	long level = s2tt_test_helpers_min_block_lvl() - 1L;
	unsigned long pa = 0UL; /* Valid for any level */
	unsigned long ap = 0UL; /* Valid on any level */
	struct s2tt_context s2tt_ctx;

	(void)memset(&s2tt_ctx, 0, sizeof(s2tt_ctx));

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 and s2tt_ctx.indirect_s2ap ar of use
	 * on this API, so the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
	s2tt_ctx.indirect_s2ap = s2tt_test_helpers_s2pie_enabled();

	test_helpers_expect_assert_fail(true);
	(void)s2tte_create_assigned_empty((const struct s2tt_context *)&s2tt_ctx,
					  pa, level, ap);
	test_helpers_fail_if_no_assert_failed();
}

void s2tte_create_assigned_empty_tc4(void)
{
	/***************************************************************
	 * TEST CASE 4:
	 *
	 * For a valid address, try to create an assigned-empty
	 * S2TTE with a level above the maximum.
	 ***************************************************************/

	long level = S2TT_TEST_HELPERS_MAX_LVL + 1L;
	unsigned long pa = 0UL; /* Valid for any level */
	unsigned long ap = 0UL; /* Valid on any level */
	struct s2tt_context s2tt_ctx;

	(void)memset(&s2tt_ctx, 0, sizeof(s2tt_ctx));

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 and s2tt_ctx.indirect_s2ap ar of use
	 * on this API, so the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
	s2tt_ctx.indirect_s2ap = s2tt_test_helpers_s2pie_enabled();

	test_helpers_expect_assert_fail(true);
	(void)s2tte_create_assigned_empty((const struct s2tt_context *)&s2tt_ctx,
					  pa, level, ap);
	test_helpers_fail_if_no_assert_failed();
}

void s2tte_create_assigned_empty_tc5(void)
{
	/***************************************************************
	 * TEST CASE 5:
	 *
	 * For a valid address, try to create an assigned-empty
	 * S2TTE with a null s2tt_context structure.
	 ***************************************************************/

	long level = S2TT_TEST_HELPERS_MAX_LVL;
	unsigned long pa = 0UL; /* Valid for any level */
	unsigned long ap = 0UL; /* Valid on any level */

	test_helpers_expect_assert_fail(true);
	(void)s2tte_create_assigned_empty((const struct s2tt_context *)NULL,
					  pa, level, ap);
	test_helpers_fail_if_no_assert_failed();
}

void s2tte_create_assigned_ram_tc1(void)
{
	/***************************************************************
	 * TEST CASE 1:
	 *
	 * Create an assigned-ram S2TTE with valid parameters and
	 * verify that it is valid.
	 ***************************************************************/

	struct s2tt_context s2tt_ctx;

	(void)memset(&s2tt_ctx, 0, sizeof(s2tt_ctx));

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 and s2tt_ctx.indirect_s2ap ar of use
	 * on this API, so the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
	s2tt_ctx.indirect_s2ap = s2tt_test_helpers_s2pie_enabled();

	/* Test for each possible level */
	for (long i = s2tt_test_helpers_min_block_lvl();
	     i <= S2TT_TEST_HELPERS_MAX_LVL; i++) {
		unsigned long pa = s2tt_test_helpers_gen_addr(i, true);
		unsigned long ap = test_helpers_get_rand_in_range(0UL, ULONG_MAX);
		unsigned long ap_mask = s2tt_test_generate_ap_mask();
		unsigned long tte =
			s2tte_create_assigned_ram((const struct s2tt_context *)&s2tt_ctx,
						  pa, i, ap);
		unsigned long attrs = (is_feat_lpa2_4k_2_present() == true) ?
				S2TTE_ATTRS_LPA2 : S2TTE_ATTRS;

		attrs |= (i == S2TT_TEST_HELPERS_MAX_LVL) ?
				S2TT_TEST_PAGE_DESC : S2TT_TEST_BLOCK_DESC;

		if (s2tt_ctx.indirect_s2ap) {
			attrs |= S2TTE_DIRTY_BIT;
		}

		/* Validate the address */
		UNSIGNED_LONGS_EQUAL(s2tt_test_helpers_s2tte_to_pa(tte, i), pa);

		/* Validate the attributes, excluding Access Permissions  */
		UNSIGNED_LONGS_EQUAL((s2tt_test_helpers_s2tte_to_attrs(tte, false) &
						~s2tt_test_generate_ap_mask()), attrs);

		/* Validate the Access Permissions */
		if (s2tt_ctx.indirect_s2ap) {
			UNSIGNED_LONGS_EQUAL(s2tte_get_pi_index(&s2tt_ctx, tte),
					     S2TTE_DEF_BASE_PERM_IDX);
			UNSIGNED_LONGS_EQUAL((ap & MASK(S2TTE_PO_INDEX)),
					     (tte & MASK(S2TTE_PO_INDEX)));
		} else {
			UNSIGNED_LONGS_EQUAL((ap & ap_mask), (tte & ap_mask));
		}

		/* The rest of the fields must be all 0 */
		UNSIGNED_LONGS_EQUAL((tte & ~(s2tt_test_helpers_s2tte_oa_mask() |
							attrs | ap_mask)), 0UL);
	}
}

void s2tte_create_assigned_ram_tc2(void)
{
	/***************************************************************
	 * TEST CASE 2:
	 *
	 * For a valid level, try to create an assigned-ram S2TTE with
	 * an unaligned address.
	 ***************************************************************/

	long level = (long)test_helpers_get_rand_in_range(
			(unsigned long)s2tt_test_helpers_min_block_lvl(),
			(unsigned long)S2TT_TEST_HELPERS_MAX_LVL);
	unsigned long pa = s2tt_test_helpers_gen_addr(level, true);
	unsigned long ap = 0UL; /* Valid on any level */

	struct s2tt_context s2tt_ctx;

	(void)memset(&s2tt_ctx, 0, sizeof(s2tt_ctx));

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 and s2tt_ctx.indirect_s2ap ar of use
	 * on this API, so the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
	s2tt_ctx.indirect_s2ap = s2tt_test_helpers_s2pie_enabled();

	pa += test_helpers_get_rand_in_range(1UL, (unsigned long)GRANULE_SIZE - 1UL);

	test_helpers_expect_assert_fail(true);
	(void)s2tte_create_assigned_ram((const struct s2tt_context *)&s2tt_ctx,
					pa, level, ap);
	test_helpers_fail_if_no_assert_failed();
}

void s2tte_create_assigned_ram_tc3(void)
{
	/***************************************************************
	 * TEST CASE 3:
	 *
	 * For a valid address, try to create an assigned-ram S2TTE
	 * with a level below the minimum.
	 ***************************************************************/

	long level = s2tt_test_helpers_min_block_lvl() - 1L;
	unsigned long pa = 0UL; /* Valid for any level */
	unsigned long ap = 0UL; /* Valid on any level */
	struct s2tt_context s2tt_ctx;

	(void)memset(&s2tt_ctx, 0, sizeof(s2tt_ctx));

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 and s2tt_ctx.indirect_s2ap ar of use
	 * on this API, so the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
	s2tt_ctx.indirect_s2ap = s2tt_test_helpers_s2pie_enabled();

	test_helpers_expect_assert_fail(true);
	(void)s2tte_create_assigned_ram((const struct s2tt_context *)&s2tt_ctx,
					pa, level, ap);
	test_helpers_fail_if_no_assert_failed();
}

void s2tte_create_assigned_ram_tc4(void)
{
	/***************************************************************
	 * TEST CASE 4:
	 *
	 * For a valid address, try to create an assigned-ram S2TTE
	 * with a level above the maximum.
	 ***************************************************************/

	long level = S2TT_TEST_HELPERS_MAX_LVL + 1L;
	unsigned long pa = 0UL; /* Valid for any level */
	unsigned long ap = 0UL; /* valid on any level */
	struct s2tt_context s2tt_ctx;

	(void)memset(&s2tt_ctx, 0, sizeof(s2tt_ctx));

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 and s2tt_ctx.indirect_s2ap ar of use
	 * on this API, so the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
	s2tt_ctx.indirect_s2ap = s2tt_test_helpers_s2pie_enabled();

	test_helpers_expect_assert_fail(true);
	(void)s2tte_create_assigned_ram((const struct s2tt_context *)&s2tt_ctx,
					pa, level, ap);
	test_helpers_fail_if_no_assert_failed();
}

void s2tte_create_assigned_ram_tc5(void)
{
	/***************************************************************
	 * TEST CASE 5:
	 *
	 * For a valid address, try to create an assigned-ram S2TTE
	 * with a null s2tt_context structure.
	 ***************************************************************/

	long level = S2TT_TEST_HELPERS_MAX_LVL;
	unsigned long pa = 0UL; /* Valid for any level */
	unsigned long ap = 0UL; /* Valid on any level */

	test_helpers_expect_assert_fail(true);
	(void)s2tte_create_assigned_ram((const struct s2tt_context *)NULL,
					pa, level, ap);
	test_helpers_fail_if_no_assert_failed();
}

void s2tte_create_assigned_ns_tc1(void)
{
	/***************************************************************
	 * TEST CASE 1:
	 *
	 * Create an assigned-NS S2TTE with valid parameters and
	 * verify that it is valid.
	 ***************************************************************/

	/* Test for each possible level */
	for (long i = s2tt_test_helpers_min_block_lvl();
	     i <= S2TT_TEST_HELPERS_MAX_LVL; i++) {
		unsigned long pa = s2tt_test_helpers_gen_addr(i, true);
		unsigned long host_attrs = s2tt_test_helpers_gen_ns_attrs(true,
									  false);
		unsigned long attrs = s2tt_test_helpers_gen_ns_attrs(false,
								     false);
		struct s2tt_context s2tt_ctx;

		(void)memset(&s2tt_ctx, 0, sizeof(s2tt_ctx));

		/*
		 * Generate an s2tt context to be used for the test.
		 * only s2tt_ctx.enable_lpa2 and s2tt_ctx.indirect_s2ap ar of use
		 * on this API, so the rest of them can be uninitialized.
		 */
		s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
		s2tt_ctx.indirect_s2ap = s2tt_test_helpers_s2pie_enabled();

		unsigned long tte = s2tte_create_assigned_ns(
				(const struct s2tt_context *)&s2tt_ctx,
				s2tt_test_helpers_pa_to_s2tte(pa, i) |
							host_attrs, i, 0UL);

		attrs |= (i == S2TT_TEST_HELPERS_MAX_LVL) ?
				S2TT_TEST_PAGE_DESC : S2TT_TEST_BLOCK_DESC;

		if (!s2tt_test_helpers_lpa2_enabled()) {
			attrs |= S2TTE_SH_IS;
		}

		/* Validate the address */
		UNSIGNED_LONGS_EQUAL(s2tt_test_helpers_s2tte_to_pa(tte, i), pa);

		/* Validate the attributes */
		UNSIGNED_LONGS_EQUAL(s2tt_test_helpers_s2tte_to_attrs(tte, true),
							(attrs | host_attrs));

		/* The rest of the fields must be all 0 */
		UNSIGNED_LONGS_EQUAL((tte & ~(s2tt_test_helpers_s2tte_oa_mask() |
			S2TTE_NS_ATTR_RMM | S2TT_DESC_TYPE_MASK |
			S2TTE_NS_ATTR_MASK | s2tt_test_generate_ap_mask() |
			S2TTE_DIRTY_BIT |
			(is_feat_lpa2_4k_2_present() ? 0UL : S2TTE_SH_MASK))), 0UL);
	}
}

void s2tte_create_assigned_ns_tc2(void)
{
	/***************************************************************
	 * TEST CASE 2:
	 *
	 * For a valid address, try to create an assigned-ns S2TTE
	 * with a level below the minimum.
	 ***************************************************************/

	long level = s2tt_test_helpers_min_table_lvl() - 1L;
	unsigned long pa = 0UL; /* Valid for any level */

	test_helpers_expect_assert_fail(true);
	/*
	 * s2tte_create_assigned_ns() does not make use of the
	 * s2tt_context structure even though it receives it, so
	 * it is safe to just pass a NULL pointer.
	 */
	(void)s2tte_create_assigned_ns((const struct s2tt_context *)NULL,
					pa, level, 0UL);
	test_helpers_fail_if_no_assert_failed();
}

void s2tte_create_assigned_ns_tc3(void)
{
	/***************************************************************
	 * TEST CASE 3:
	 *
	 * For a valid address, try to create an assigned-ns S2TTE
	 * with a level above the maximum.
	 ***************************************************************/

	long level = S2TT_TEST_HELPERS_MAX_LVL + 1L;
	unsigned long pa = 0UL; /* Valid for any level */

	test_helpers_expect_assert_fail(true);
	/*
	 * s2tte_create_assigned_ns() does not make use of the
	 * s2tt_context structure even though it receives it, so
	 * it is safe to just pass a NULL pointer.
	 */
	(void)s2tte_create_assigned_ns((const struct s2tt_context *)NULL,
			s2tt_test_helpers_pa_to_s2tte(pa, level), level, 0UL);
	test_helpers_fail_if_no_assert_failed();
}

void s2tte_create_assigned_unchanged_tc1(void)
{
	/***************************************************************
	 * TEST CASE 1:
	 *
	 * For each possible level and each possible RIPAS, invoke
	 * create_assigned_unchanged() and verify that the TTE is
	 * correct.
	 ***************************************************************/

	struct s2tt_context s2tt_ctx;

	(void)memset(&s2tt_ctx, 0, sizeof(s2tt_ctx));

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 and s2tt_ctx.indirect_s2ap ar of use
	 * on this API, so the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
	s2tt_ctx.indirect_s2ap = s2tt_test_helpers_s2pie_enabled();

	for (long level = s2tt_test_helpers_min_block_lvl();
	     level <= S2TT_TEST_HELPERS_MAX_LVL;
	     level++) {
		for (unsigned long ripas = RIPAS_EMPTY;
		     ripas < S2TT_TEST_RIPAS_INVALID;
		     ripas++) {
			unsigned long pa = s2tt_test_helpers_gen_addr(level,
								    true);
			unsigned long ap = s2tt_test_generate_ap(false);
			unsigned long tte = s2tte_create_assigned_unchanged(
				(const struct s2tt_context *)&s2tt_ctx,
				(INPLACE(S2TTE_INVALID_RIPAS, ripas) | ap),
				pa, level);

			/* Validate the address */
			UNSIGNED_LONGS_EQUAL(pa,
				s2tt_test_helpers_s2tte_to_pa(tte, level));

			if (ripas == RIPAS_RAM) {
				/*
				 * Manually generate an assigned-ram entry and
				 * compare it with the generated TTE. The PA,
				 * which has already been validated, is the
				 * same so this check will fail if any
				 * attribute is invalid.
				 */
				unsigned long expected_tte =
					s2tt_test_helpers_pa_to_s2tte(pa, level) |
					s2tt_test_helpers_gen_attrs(false, level) |
					ap;
				UNSIGNED_LONGS_EQUAL(expected_tte, tte);
			} else {
				/* Verify the RIPAS */
				UNSIGNED_LONGS_EQUAL(
					(tte & S2TTE_INVALID_RIPAS_MASK),
						INPLACE(S2TTE_INVALID_RIPAS,
							ripas));

				/* Verify the HIPAS */
				UNSIGNED_LONGS_EQUAL(
					(tte & S2TTE_INVALID_HIPAS_MASK),
						S2TTE_INVALID_HIPAS_ASSIGNED);

				/* Verify the Access Permissions */
				UNSIGNED_LONGS_EQUAL(
					(tte & s2tt_test_generate_ap_mask()), ap);

				/* The Descriptor type must be invalid */
				UNSIGNED_LONGS_EQUAL(
					(tte & S2TT_TEST_DESC_TYPE_MASK),
						S2TT_TEST_INVALID_DESC);
			}
		}
	}
}

void s2tte_create_assigned_unchanged_tc2(void)
{
	/***************************************************************
	 * TEST CASE 2:
	 *
	 * For a valid level and ripas try to create an
	 * assigned-unchanged S2TTE with an unaligned address.
	 ***************************************************************/

	long level = (long)test_helpers_get_rand_in_range(
			(unsigned long)s2tt_test_helpers_min_block_lvl(),
			(unsigned long)S2TT_TEST_HELPERS_MAX_LVL);
	unsigned long ripas = test_helpers_get_rand_in_range(
					RIPAS_EMPTY,
					RIPAS_DESTROYED);
	unsigned long pa = s2tt_test_helpers_gen_addr(level, true);
	unsigned long ap = 0UL; /* Valid on any level or RIPAS value */
	struct s2tt_context s2tt_ctx;

	(void)memset(&s2tt_ctx, 0, sizeof(s2tt_ctx));

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 and s2tt_ctx.indirect_s2ap ar of use
	 * on this API, so the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
	s2tt_ctx.indirect_s2ap = s2tt_test_helpers_s2pie_enabled();

	pa += test_helpers_get_rand_in_range(1UL, (unsigned long)GRANULE_SIZE - 1UL);

	test_helpers_expect_assert_fail(true);
	(void)s2tte_create_assigned_unchanged((const struct s2tt_context *)&s2tt_ctx,
					      (ripas | ap), pa, level);
	test_helpers_fail_if_no_assert_failed();
}

void s2tte_create_assigned_unchanged_tc3(void)
{
	/***************************************************************
	 * TEST CASE 3:
	 *
	 * For a valid address and ripas try to create an
	 * assigned-unchanged S2TTE with a level below the minimum.
	 ***************************************************************/

	long level = s2tt_test_helpers_min_block_lvl() - 1L;
	unsigned long ripas = test_helpers_get_rand_in_range(
					RIPAS_EMPTY,
					RIPAS_DESTROYED);
	unsigned long pa = 0UL; /* Valid for any level */
	unsigned long ap = 0UL; /* Valid on any level or RIPAS value */
	struct s2tt_context s2tt_ctx;

	(void)memset(&s2tt_ctx, 0, sizeof(s2tt_ctx));

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 and s2tt_ctx.indirect_s2ap ar of use
	 * on this API, so the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
	s2tt_ctx.indirect_s2ap = s2tt_test_helpers_s2pie_enabled();

	test_helpers_expect_assert_fail(true);
	(void)s2tte_create_assigned_unchanged((const struct s2tt_context *)&s2tt_ctx,
					      (ripas | ap), pa, level);
	test_helpers_fail_if_no_assert_failed();
}

void s2tte_create_assigned_unchanged_tc4(void)
{
	/***************************************************************
	 * TEST CASE 4:
	 *
	 * For a valid address and ripas, try to create an
	 * assigned-unchanged S2TTE with a level above the maximum.
	 ***************************************************************/

	long level = S2TT_TEST_HELPERS_MAX_LVL + 1L;
	unsigned long ripas = test_helpers_get_rand_in_range(
					RIPAS_EMPTY,
					RIPAS_DESTROYED);
	unsigned long pa = 0UL; /* Valid for any level */
	unsigned long ap = 0UL; /* Valid on any level or RIPAS value */
	struct s2tt_context s2tt_ctx;

	(void)memset(&s2tt_ctx, 0, sizeof(s2tt_ctx));

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 and s2tt_ctx.indirect_s2ap ar of use
	 * on this API, so the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
	s2tt_ctx.indirect_s2ap = s2tt_test_helpers_s2pie_enabled();

	test_helpers_expect_assert_fail(true);
	(void)s2tte_create_assigned_unchanged((const struct s2tt_context *)&s2tt_ctx,
					      (ripas | ap), pa, level);
	test_helpers_fail_if_no_assert_failed();
}

void s2tte_create_assigned_unchanged_tc5(void)
{
	/***************************************************************
	 * TEST CASE 5:
	 *
	 * For a valid level and pa try to create an
	 * assigned-unchanged S2TTE with an invalid RIPAS.
	 ***************************************************************/

	long level = (long)test_helpers_get_rand_in_range(
			(unsigned long)s2tt_test_helpers_min_block_lvl(),
			(unsigned long)S2TT_TEST_HELPERS_MAX_LVL);
	unsigned long ripas = INPLACE(S2TTE_INVALID_RIPAS,
						S2TT_TEST_RIPAS_INVALID);
	unsigned long pa = 0UL; /* Valid for any level */
	unsigned long ap = 0UL; /* Valid on any level or RIPAS value */
	struct s2tt_context s2tt_ctx;

	(void)memset(&s2tt_ctx, 0, sizeof(s2tt_ctx));

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 and s2tt_ctx.indirect_s2ap ar of use
	 * on this API, so the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
	s2tt_ctx.indirect_s2ap = s2tt_test_helpers_s2pie_enabled();

	test_helpers_expect_assert_fail(true);
	(void)s2tte_create_assigned_unchanged((const struct s2tt_context *)&s2tt_ctx,
					      (ripas | ap), pa, level);
	test_helpers_fail_if_no_assert_failed();
}

void s2tte_create_assigned_unchanged_tc6(void)
{
	/***************************************************************
	 * TEST CASE 6:
	 *
	 * For a valid level, pa and RIPAS, try to create an
	 * assigned-unchanged S2TTE with a null s2tt_context structure.
	 ***************************************************************/

	long level = (long)test_helpers_get_rand_in_range(
			(unsigned long)s2tt_test_helpers_min_block_lvl(),
			(unsigned long)S2TT_TEST_HELPERS_MAX_LVL);
	unsigned long ripas = test_helpers_get_rand_in_range(
					RIPAS_EMPTY,
					RIPAS_DESTROYED);
	unsigned long pa = 0UL; /* Valid for any level */
	unsigned long ap = 0UL; /* Valid on any level or RIPAS value */

	test_helpers_expect_assert_fail(true);
	(void)s2tte_create_assigned_unchanged((const struct s2tt_context *)NULL,
					      (ripas | ap), pa, level);
	test_helpers_fail_if_no_assert_failed();
}

void s2tte_create_table_tc1(void)
{
	/***************************************************************
	 * TEST CASE 1:
	 *
	 * For all possible valid levels, try to create and validate
	 * a table tte.
	 ***************************************************************/

	struct s2tt_context s2tt_ctx;

	(void)memset(&s2tt_ctx, 0, sizeof(s2tt_ctx));

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 and s2tt_ctx.indirect_s2ap ar of use
	 * on this API, so the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
	s2tt_ctx.indirect_s2ap = s2tt_test_helpers_s2pie_enabled();

	for (long level = s2tt_test_helpers_min_table_lvl();
	     level < S2TT_TEST_HELPERS_MAX_LVL; level++) {
		unsigned long pa = s2tt_test_helpers_gen_addr(level, true);
		unsigned long tte = s2tte_create_table(
				(const struct s2tt_context *)&s2tt_ctx,
				pa, level);

		/* Validate the address */
		UNSIGNED_LONGS_EQUAL(s2tt_test_helpers_s2tte_to_pa(tte, level),
									 pa);

		/* Validate the descriptor type */
		UNSIGNED_LONGS_EQUAL(EXTRACT(S2TT_TEST_DESC_TYPE, tte),
							S2TT_TEST_TABLE_DESC);

		/* Validate that the rest of the descriptor is all zero */
		UNSIGNED_LONGS_EQUAL((tte & ~(S2TT_TEST_DESC_TYPE_MASK |
				   s2tt_test_helpers_s2tte_oa_mask())), 0UL);

	}
}

void s2tte_create_table_tc2(void)
{
	/***************************************************************
	 * TEST CASE 2:
	 *
	 * For a valid level try to create a table tte with an
	 * unaligned address.
	 ***************************************************************/

	long level = (long)test_helpers_get_rand_in_range(
			(unsigned long)s2tt_test_helpers_min_block_lvl(),
			(unsigned long)S2TT_TEST_HELPERS_MAX_LVL);
	unsigned long pa = s2tt_test_helpers_gen_addr(level, true);
	struct s2tt_context s2tt_ctx;

	(void)memset(&s2tt_ctx, 0, sizeof(s2tt_ctx));

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 and s2tt_ctx.indirect_s2ap ar of use
	 * on this API, so the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
	s2tt_ctx.indirect_s2ap = s2tt_test_helpers_s2pie_enabled();

	pa += test_helpers_get_rand_in_range(1UL, (unsigned long)GRANULE_SIZE - 1UL);

	test_helpers_expect_assert_fail(true);
	(void)s2tte_create_table((const struct s2tt_context *)&s2tt_ctx, pa, level);
	test_helpers_fail_if_no_assert_failed();
}

void s2tte_create_table_tc3(void)
{
	/***************************************************************
	 * TEST CASE 3:
	 *
	 * For a valid address to create a table tte with a level below
	 * the minimum.
	 ***************************************************************/

	long level = s2tt_test_helpers_min_table_lvl() - 1;
	unsigned long pa = 0UL; /* Valid for any level */
	struct s2tt_context s2tt_ctx;

	(void)memset(&s2tt_ctx, 0, sizeof(s2tt_ctx));

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 and s2tt_ctx.indirect_s2ap ar of use
	 * on this API, so the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
	s2tt_ctx.indirect_s2ap = s2tt_test_helpers_s2pie_enabled();

	test_helpers_expect_assert_fail(true);
	(void)s2tte_create_table((const struct s2tt_context *)&s2tt_ctx, pa, level);
	test_helpers_fail_if_no_assert_failed();
}

void s2tte_create_table_tc4(void)
{
	/***************************************************************
	 * TEST CASE 4:
	 *
	 * For a valid address to create a table tte with a level above
	 * the maximum.
	 ***************************************************************/

	long level = S2TT_TEST_HELPERS_MAX_LVL;
	unsigned long pa = 0UL; /* Valid for any level */
	struct s2tt_context s2tt_ctx;

	(void)memset(&s2tt_ctx, 0, sizeof(s2tt_ctx));

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 and s2tt_ctx.indirect_s2ap ar of use
	 * on this API, so the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
	s2tt_ctx.indirect_s2ap = s2tt_test_helpers_s2pie_enabled();

	test_helpers_expect_assert_fail(true);
	(void)s2tte_create_table((const struct s2tt_context *)&s2tt_ctx, pa, level);
	test_helpers_fail_if_no_assert_failed();
}

void s2tte_create_table_tc5(void)
{
	/***************************************************************
	 * TEST CASE 5:
	 *
	 * Test s2tte_create_table() with a set of valid arguments and
	 * a NULL struct s2tt_context pointer.
	 ***************************************************************/

	long level = s2tt_test_helpers_min_table_lvl();
	unsigned long pa = s2tt_test_helpers_gen_addr(level, true);

	test_helpers_expect_assert_fail(true);
	(void)s2tte_create_table((const struct s2tt_context *)NULL,
				 pa, level);
	test_helpers_fail_if_no_assert_failed();
}

void host_ns_s2tte_is_valid_tc1(void)
{
	/***************************************************************
	 * TEST CASE 1:
	 *
	 * For all valid levels, generate a random ns_s2tte and pass it
	 * to host_ns_s2tte_is_valid() to validate its behaviour.
	 ***************************************************************/
	struct s2tt_context s2tt_ctx;

	(void)memset(&s2tt_ctx, 0, sizeof(s2tt_ctx));

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 and s2tt_ctx.indirect_s2ap ar of use
	 * on this API, so the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
	s2tt_ctx.indirect_s2ap = s2tt_test_helpers_s2pie_enabled();

	for (long level = s2tt_test_helpers_min_block_lvl();
	     level <= S2TT_TEST_HELPERS_MAX_LVL; level++) {

		unsigned long pa = s2tt_test_helpers_gen_addr(level, true);
		unsigned long host_attrs =
				s2tt_test_helpers_gen_ns_attrs(true, false);
		unsigned long tte = s2tt_test_helpers_pa_to_s2tte(pa, level) |
								host_attrs;

		CHECK_TRUE(host_ns_s2tte_is_valid(
					(const struct s2tt_context *)&s2tt_ctx,
					tte, level));
	}
}

void host_ns_s2tte_is_valid_tc2(void)
{
	/***************************************************************
	 * TEST CASE 2:
	 *
	 * For all valid levels, generate different invalid NS-S2TTEs
	 * and pass them to host_ns_s2tte_is_valid() to validate its
	 * behaviour.
	 ***************************************************************/
	struct s2tt_context s2tt_ctx;

	(void)memset(&s2tt_ctx, 0, sizeof(s2tt_ctx));

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 and s2tt_ctx.indirect_s2ap ar of use
	 * on this API, so the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
	s2tt_ctx.indirect_s2ap = s2tt_test_helpers_s2pie_enabled();

	for (long level = s2tt_test_helpers_min_block_lvl();
	     level <= S2TT_TEST_HELPERS_MAX_LVL; level++) {

		/* Generate a NS S2TTE with a set of invalid host attrs */
		unsigned long host_attrs =
				s2tt_test_helpers_gen_ns_attrs(true, true);
		unsigned long ap = 0UL; /* Valid on any level */
		unsigned long pa = s2tt_test_helpers_gen_addr(level, true);
		unsigned long tte = s2tt_test_helpers_pa_to_s2tte(pa, level) |
								host_attrs | ap;

		CHECK_FALSE(host_ns_s2tte_is_valid(
					(const struct s2tt_context *)&s2tt_ctx,
					tte, level));

		/*
		 * Generate a NS S2TTE with invalid bits set to '1'.
		 *
		 * This case would also cover unaligned PAs on the S2TTE
		 * as that would be equivalent to have some invalid bits
		 * set to '1' as well.
		 */
		do {
			host_attrs = s2tt_test_helpers_gen_ns_attrs(true, false) |
				test_helpers_get_rand_in_range(1UL, ULONG_MAX);
		} while ((host_attrs & ~(S2TTE_NS_ATTR_MASK |
					 s2tt_test_helpers_s2tte_oa_mask())) == 0UL);

		tte = s2tt_test_helpers_pa_to_s2tte(pa, level) | host_attrs | ap;

		CHECK_FALSE(host_ns_s2tte_is_valid(
					(const struct s2tt_context *)&s2tt_ctx,
					tte, level));
	}
}

void host_ns_s2tte_is_valid_tc3(void)
{
	/***************************************************************
	 * TEST CASE 3:
	 *
	 * Test host_ns_s2tte_is_valid() with a valid NS S2TTE but a
	 * level below the minimum supported. This should cause an
	 * assert fail even if the PA is not aligned to the invalid
	 * level.
	 ***************************************************************/

	struct s2tt_context s2tt_ctx;

	(void)memset(&s2tt_ctx, 0, sizeof(s2tt_ctx));

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 and s2tt_ctx.indirect_s2ap ar of use
	 * on this API, so the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
	s2tt_ctx.indirect_s2ap = s2tt_test_helpers_s2pie_enabled();

	/*
	 * Generate the tte with an assumed PA == 0, which is aligned to
	 * any level.
	 */
	unsigned long tte = s2tt_test_helpers_gen_ns_attrs(true, false);
	long level = s2tt_test_helpers_min_block_lvl() - 1L;

	test_helpers_expect_assert_fail(true);
	(void)host_ns_s2tte_is_valid((const struct s2tt_context *)&s2tt_ctx,
				     tte, level);
	test_helpers_fail_if_no_assert_failed();
}

void host_ns_s2tte_is_valid_tc4(void)
{
	/***************************************************************
	 * TEST CASE 4:
	 *
	 * Test host_ns_s2tte_is_valid() with a valid NS S2TTE but a
	 * level above the maximum supported. This should cause an
	 * assert fail even if the PA is not aligned to the invalid
	 * level.
	 ***************************************************************/

	struct s2tt_context s2tt_ctx;

	(void)memset(&s2tt_ctx, 0, sizeof(s2tt_ctx));

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 and s2tt_ctx.indirect_s2ap ar of use
	 * on this API, so the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
	s2tt_ctx.indirect_s2ap = s2tt_test_helpers_s2pie_enabled();

	/*
	 * Generate the tte with an assumed PA == 0, which is aligned to
	 * any level.
	 */
	unsigned long tte = s2tt_test_helpers_gen_ns_attrs(true, false);
	long level = S2TT_TEST_HELPERS_MAX_LVL + 1L;

	test_helpers_expect_assert_fail(true);
	(void)host_ns_s2tte_is_valid((const struct s2tt_context *)&s2tt_ctx,
				     tte, level);
	test_helpers_fail_if_no_assert_failed();
}

void host_ns_s2tte_is_valid_tc5(void)
{
	/***************************************************************
	 * TEST CASE 5:
	 *
	 * Test host_ns_s2tte_is_valid() with valid parameters but a
	 * NULL s2tt_context struct pointer.
	 ***************************************************************/

	long level = s2tt_test_helpers_min_block_lvl();
	unsigned long pa = s2tt_test_helpers_gen_addr(level, true);
	unsigned long host_attrs = s2tt_test_helpers_gen_ns_attrs(true, false);
	unsigned long tte = s2tt_test_helpers_pa_to_s2tte(pa, level) | host_attrs;

	test_helpers_expect_assert_fail(true);
	(void)host_ns_s2tte_is_valid((const struct s2tt_context *)NULL,
				     tte, level);
	test_helpers_fail_if_no_assert_failed();
}

void host_ns_s2tte_is_valid_tc6(void)
{
	/***************************************************************
	 * TEST CASE 6:
	 *
	 * Test host_ns_s2tte_is_valid() with invalid PA >= 48 bits
	 * when LPA2 is disabled
	 **************************************************************/

	struct s2tt_context s2tt_ctx;

	(void)memset(&s2tt_ctx, 0, sizeof(s2tt_ctx));

	unsigned long host_attrs;
	unsigned long tte;
	long level = s2tt_test_helpers_min_block_lvl();
	unsigned long pa = s2tt_test_helpers_gen_addr(level, true);
	unsigned long ap = 0UL; /* Valid on any level */

	if (is_feat_lpa2_4k_2_present() == false) {
		CHECK_TRUE(true);
		return;
	}

	pa = pa | (1UL << S2TT_MAX_PA_BITS);
	host_attrs =
		s2tt_test_helpers_gen_ns_attrs(true, false);
	tte = s2tt_test_helpers_pa_to_s2tte(pa, level) |
		host_attrs | ap;

	CHECK_TRUE(s2tt_test_helpers_s2tte_to_pa(tte, level) >= (1UL << S2TT_MAX_PA_BITS));
	CHECK_FALSE(host_ns_s2tte_is_valid((const struct s2tt_context *)&s2tt_ctx,
				tte, level));
}

void host_ns_s2tte_tc1(void)
{
	/***************************************************************
	 * TEST CASE 1:
	 *
	 * Create an assigned-NS S2TTE with valid parameters and
	 * verify that host_ns_s2tte() returns the portion of the S2TTE
	 * has been set by the host.
	 ***************************************************************/

	struct s2tt_context s2tt_ctx;

	(void)memset(&s2tt_ctx, 0, sizeof(s2tt_ctx));

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 and s2tt_ctx.indirect_s2ap ar of use
	 * on this API, so the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
	s2tt_ctx.indirect_s2ap = s2tt_test_helpers_s2pie_enabled();

	/* Test for each possible level */
	for (long level = s2tt_test_helpers_min_block_lvl();
	     level <= S2TT_TEST_HELPERS_MAX_LVL; level++) {
		unsigned long pa = s2tt_test_helpers_gen_addr(level, true);
		unsigned long host_attrs = s2tt_test_helpers_gen_ns_attrs(true,
									  false);
		unsigned long val_tte = s2tte_create_assigned_ns(
					(const struct s2tt_context *)&s2tt_ctx,
					s2tt_test_helpers_pa_to_s2tte(pa, level) |
							host_attrs, level, 0UL);
		unsigned long tte = host_ns_s2tte((const struct s2tt_context *)&s2tt_ctx,
						   val_tte, level);

		/* Validate the address */
		UNSIGNED_LONGS_EQUAL(s2tt_test_helpers_s2tte_to_pa(val_tte, level),
			   s2tt_test_helpers_s2tte_to_pa(tte, level));

		/*
		 * Validate that the rest of the S2TTE (excluding the PA)
		 * matches the host_attrs an AP (and therefore any other
		 * bit is '0')
		 */
		UNSIGNED_LONGS_EQUAL(host_attrs,
			(tte & ~s2tt_test_helpers_s2tte_oa_mask()));
	}
}

void host_ns_s2tte_tc2(void)
{
	/***************************************************************
	 * TEST CASE 2:
	 *
	 * Test host_ns_s2tte() with a valid NS S2TTE but a level
	 * below the minimum supported.
	 ***************************************************************/

	struct s2tt_context s2tt_ctx;

	(void)memset(&s2tt_ctx, 0, sizeof(s2tt_ctx));

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 and s2tt_ctx.indirect_s2ap ar of use
	 * on this API, so the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
	s2tt_ctx.indirect_s2ap = s2tt_test_helpers_s2pie_enabled();

	/*
	 * Generate the tte with an assumed PA == 0, which is aligned to
	 * any level.
	 */
	long level = s2tt_test_helpers_min_block_lvl();
	unsigned long host_attrs = s2tt_test_helpers_gen_ns_attrs(true,	false);
	unsigned long ap = 0UL; /* Valid on any level */

	/* s2tte_create_assigned_ns() can receive a NULL s2tt_context pointer */
	unsigned long tte = s2tte_create_assigned_ns(
			(const struct s2tt_context *)&s2tt_ctx,
			0UL | host_attrs, level, ap);

	test_helpers_expect_assert_fail(true);

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 and s2tt_ctx.indirect_s2ap ar of use
	 * on this API, so the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
	s2tt_ctx.indirect_s2ap = s2tt_test_helpers_s2pie_enabled();

	(void)host_ns_s2tte((const struct s2tt_context *)&s2tt_ctx, tte, level - 1L);
	test_helpers_fail_if_no_assert_failed();
}

void host_ns_s2tte_tc3(void)
{
	/***************************************************************
	 * TEST CASE 3:
	 *
	 * Test host_ns_s2tte() with a valid NS S2TTE but a level
	 * above the maximum supported.
	 ***************************************************************/

	struct s2tt_context s2tt_ctx;

	(void)memset(&s2tt_ctx, 0, sizeof(s2tt_ctx));

	/*
	 * Generate the tte with an assumed PA == 0, which is aligned to
	 * any level.
	 */
	long level = S2TT_TEST_HELPERS_MAX_LVL;
	unsigned long host_attrs = s2tt_test_helpers_gen_ns_attrs(true,	false);
	unsigned long ap = 0UL; /* Valid on any level */

	/* s2tte_create_assigned_ns() can receive a NULL s2tt_context pointer */
	unsigned long tte = s2tte_create_assigned_ns(
			(const struct s2tt_context *)&s2tt_ctx,
			0UL | host_attrs, level, ap);

	test_helpers_expect_assert_fail(true);
	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 and s2tt_ctx.indirect_s2ap ar of use
	 * on this API, so the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
	s2tt_ctx.indirect_s2ap = s2tt_test_helpers_s2pie_enabled();

	(void)host_ns_s2tte((const struct s2tt_context *)&s2tt_ctx, tte, level + 1L);
	test_helpers_fail_if_no_assert_failed();
}

void host_ns_s2tte_tc4(void)
{
	/***************************************************************
	 * TEST CASE 4:
	 *
	 * Test host_ns_s2tte() passing a NULL pointer to an
	 * s2tt_context structure.
	 ***************************************************************/

	/* Test for each possible level */
	long level = s2tt_test_helpers_min_block_lvl();
	unsigned long pa = s2tt_test_helpers_gen_addr(level, true);
	unsigned long host_attrs = s2tt_test_helpers_gen_ns_attrs(true, false);
	unsigned long ap = 0UL; /* Valid on any level */

	struct s2tt_context s2tt_ctx;

	(void)memset(&s2tt_ctx, 0, sizeof(s2tt_ctx));

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 and s2tt_ctx.indirect_s2ap ar of use
	 * on this API, so the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
	s2tt_ctx.indirect_s2ap = s2tt_test_helpers_s2pie_enabled();

	unsigned long val_tte = s2tte_create_assigned_ns(
				(const struct s2tt_context *)&s2tt_ctx,
				s2tt_test_helpers_pa_to_s2tte(pa, level) |
							host_attrs, level, ap);
	test_helpers_expect_assert_fail(true);
	(void)host_ns_s2tte((const struct s2tt_context *)NULL, val_tte, level);
	test_helpers_fail_if_no_assert_failed();
}

void s2tte_has_ripas_tc1(void)
{
	/***************************************************************
	 * TEST CASE 1:
	 *
	 * For each valid level at which a TTE can have RIPAS, generate
	 * a set of assigned/unassigned S2TTEs with different RIPAS and
	 * validate the output of s2tte_has_ripas().
	 ***************************************************************/

	unsigned long ripas[] = {S2TTE_INVALID_RIPAS_EMPTY,
				 S2TTE_INVALID_RIPAS_RAM,
				 S2TTE_INVALID_RIPAS_DESTROYED};
	unsigned long ap = 0UL; /* Valid on any level or RIPAS */
	struct s2tt_context s2tt_ctx;

	(void)memset(&s2tt_ctx, 0, sizeof(s2tt_ctx));

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 and s2tt_ctx.indirect_s2ap ar of use
	 * on this API, so the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
	s2tt_ctx.indirect_s2ap = s2tt_test_helpers_s2pie_enabled();

	for (long level = s2tt_test_helpers_min_block_lvl();
	     level <= S2TT_TEST_HELPERS_MAX_LVL; level++) {
		for (unsigned int i = 0U; i < ARRAY_SIZE(ripas); i++) {

			unsigned long tte;
			unsigned long pa = s2tt_test_helpers_gen_addr(level,
								    true);

			/* Validate with an assigned S2TTE */
			tte = s2tt_test_create_assigned(
					(const struct s2tt_context *)&s2tt_ctx,
					pa, level, ripas[i], ap);
			CHECK_TRUE(s2tte_has_ripas((const struct s2tt_context *)&s2tt_ctx,
						   tte, level) == true);

			/* Validate with an unassigned S2TTE */
			tte = s2tt_test_create_unassigned((
					const struct s2tt_context *)&s2tt_ctx,
					ripas[i], ap);
			CHECK_TRUE(s2tte_has_ripas((const struct s2tt_context *)&s2tt_ctx,
						   tte, level) == true);
		}
	}
}

void s2tte_has_ripas_tc2(void)
{
	/***************************************************************
	 * TEST CASE 2:
	 *
	 * For each valid level generate a set of negative tests:
	 *
	 *	- For each valid level at which a TTE can have RIPAS,
	 *	  generate a set of NS-S2TTEs (assigned and unassigned)
	 *	  and validate that  s2tte_has_ripas() returns
	 *	  the expected error.
	 *	- For each valid level at which a table can exist,
	 *	  Generate a table and verify that s2tte_has_ripas()
	 *	  returns the expected value.
	 ***************************************************************/

	unsigned long tte;
	unsigned long ap = 0UL; /* Valid on any level and RIPAS */
	struct s2tt_context s2tt_ctx;

	(void)memset(&s2tt_ctx, 0, sizeof(s2tt_ctx));

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 and s2tt_ctx.indirect_s2ap ar of use
	 * on this API, so the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
	s2tt_ctx.indirect_s2ap = s2tt_test_helpers_s2pie_enabled();

	/* Generate a set of NS S2TTEs per valid level */
	for (long level = s2tt_test_helpers_min_block_lvl();
	     level <= S2TT_TEST_HELPERS_MAX_LVL; level++) {

		unsigned long pa = s2tt_test_helpers_gen_addr(level, true);
		unsigned long host_attr = s2tt_test_helpers_gen_ns_attrs(true,
									false);
		tte = s2tte_create_assigned_ns((const struct s2tt_context *)&s2tt_ctx,
				host_attr | s2tt_test_helpers_pa_to_s2tte(pa, level),
				level, ap);
		/* Validate with assigned-ns S2TTE */
		CHECK_TRUE(s2tte_has_ripas((const struct s2tt_context *)&s2tt_ctx,
					   tte, level) == false);

		/* Validate with unassigned-ns S2TTE */
		tte = s2tte_create_unassigned_ns((const struct s2tt_context *)&s2tt_ctx, 0UL);
		CHECK_TRUE(s2tte_has_ripas((const struct s2tt_context *)NULL,
					   tte, level) == false);
	}

	for (long level = s2tt_test_helpers_min_table_lvl();
	     level < s2tt_test_helpers_min_block_lvl(); level++) {

		/* Use Addr 0UL as it is valid on any level */
		tte = s2tte_create_table((const struct s2tt_context *)&s2tt_ctx,
					 0UL, level);

		CHECK_TRUE(s2tte_has_ripas((const struct s2tt_context *)&s2tt_ctx,
					   tte, level) == false);
	}
}

void s2tte_is_unassigned_tc1(void)
{
	/***************************************************************
	 * TEST CASE 1:
	 *
	 * This test case cover positive tests for s2tt_is_unassigned()
	 * as well as a number of negative tests.
	 ***************************************************************/

	unsigned long ripas[] = {S2TTE_INVALID_RIPAS_EMPTY,
				 S2TTE_INVALID_RIPAS_RAM,
				 S2TTE_INVALID_RIPAS_DESTROYED,
				 S2TTE_NS};

	/* pickup a random type of unassigned S2TTE to test with */
	unsigned int ripas_idx = (unsigned int)test_helpers_get_rand_in_range(
					0UL, ARRAY_SIZE(ripas) - 1UL);
	unsigned long ap = s2tt_test_generate_ap(false);
	unsigned long inv_tte, tte;
	struct s2tt_context s2tt_ctx;

	(void)memset(&s2tt_ctx, 0, sizeof(s2tt_ctx));

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 and s2tt_ctx.indirect_s2ap ar of use
	 * on this API, so the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
	s2tt_ctx.indirect_s2ap = s2tt_test_helpers_s2pie_enabled();

	tte = s2tt_test_create_unassigned(
			(const struct s2tt_context *)&s2tt_ctx, ripas[ripas_idx], ap);

	/* Validate s2tt_is_unassigned with an unassigned TTE. */
	CHECK_TRUE(s2tte_is_unassigned((const struct s2tt_context *)&s2tt_ctx, tte) == true);

	/* Negative test: Set DESC_TYPE to a valid descriptor */
	inv_tte = tte | S2TT_TEST_PAGE_DESC;
	CHECK_TRUE(s2tte_is_unassigned((const struct s2tt_context *)&s2tt_ctx, inv_tte) == false);

	/* Negative test: Change the HIPAS to ASSIGNED */
	inv_tte = tte & ~S2TTE_INVALID_HIPAS_MASK;
	inv_tte |= S2TTE_INVALID_HIPAS_ASSIGNED;
	CHECK_TRUE(s2tte_is_unassigned((const struct s2tt_context *)&s2tt_ctx, inv_tte) == false);
}

void s2tte_is_unassigned_empty_tc1(void)
{
	/***************************************************************
	 * TEST CASE 1:
	 *
	 * This test case cover positive tests for
	 * is_unassigned_empty() as well as a number of negative tests.
	 ***************************************************************/

	unsigned long ripas[] = {S2TTE_INVALID_RIPAS_RAM,
				 S2TTE_INVALID_RIPAS_DESTROYED,
				 S2TTE_NS};

	unsigned int idx;
	unsigned long inv_tte;
	unsigned long ap = s2tt_test_generate_ap(false);
	unsigned long tte;
	struct s2tt_context s2tt_ctx;

	(void)memset(&s2tt_ctx, 0, sizeof(s2tt_ctx));

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 and s2tt_ctx.indirect_s2ap ar of use
	 * on this API, so the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
	s2tt_ctx.indirect_s2ap = s2tt_test_helpers_s2pie_enabled();

	tte = s2tte_create_unassigned_empty(
					(const struct s2tt_context *)&s2tt_ctx, ap);

	/* Validate s2tt_is_unassigned_empty with an unassigned TTE */
	CHECK_TRUE(s2tte_is_unassigned_empty((const struct s2tt_context *)&s2tt_ctx, tte) == true);

	/* Negative test: Set DESC_TYPE to a valid descriptor */
	inv_tte = tte | S2TT_TEST_PAGE_DESC;
	CHECK_TRUE(s2tte_is_unassigned_empty((const struct s2tt_context *)&s2tt_ctx,
					     inv_tte) == false);

	/* Negative test: Change the HIPAS to ASSIGNED */
	inv_tte = tte & ~S2TTE_INVALID_HIPAS_MASK;
	inv_tte |= S2TTE_INVALID_HIPAS_ASSIGNED;
	CHECK_TRUE(s2tte_is_unassigned_empty((const struct s2tt_context *)&s2tt_ctx,
					     inv_tte) == false);

	/* Negative test: Test with a different type of unassigned TTE but having RIPAS */
	idx = (unsigned int)test_helpers_get_rand_in_range(
					0UL, ARRAY_SIZE(ripas) - 1UL);
	inv_tte = s2tt_test_create_unassigned((const struct s2tt_context *)&s2tt_ctx,
					      ripas[idx], ap);
	CHECK_TRUE(s2tte_is_unassigned_empty((const struct s2tt_context *)&s2tt_ctx,
					     inv_tte) == false);
}

void s2tte_is_unassigned_ram_tc1(void)
{
	/***************************************************************
	 * TEST CASE 1:
	 *
	 * This test case cover positive tests for
	 * is_unassigned_ram() as well as a number of negative tests.
	 ***************************************************************/

	unsigned long ripas[] = {S2TTE_INVALID_RIPAS_EMPTY,
				 S2TTE_INVALID_RIPAS_DESTROYED,
				 S2TTE_NS};
	unsigned int idx;
	unsigned long inv_tte;
	unsigned long ap = s2tt_test_generate_ap(false);
	unsigned long tte;
	struct s2tt_context s2tt_ctx;

	(void)memset(&s2tt_ctx, 0, sizeof(s2tt_ctx));

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 and s2tt_ctx.indirect_s2ap ar of use
	 * on this API, so the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
	s2tt_ctx.indirect_s2ap = s2tt_test_helpers_s2pie_enabled();

	tte = s2tte_create_unassigned_ram(
					(const struct s2tt_context *)&s2tt_ctx, ap);

	/* Validate s2tt_is_unassigned_ram with an unassigned ram TTE */
	CHECK_TRUE(s2tte_is_unassigned_ram((const struct s2tt_context *)&s2tt_ctx, tte) == true);

	/* Negative test: Set DESC_TYPE to a valid descriptor */
	inv_tte = tte | S2TT_TEST_PAGE_DESC;
	CHECK_TRUE(s2tte_is_unassigned_ram((const struct s2tt_context *)&s2tt_ctx,
					   inv_tte) == false);

	/* Negative test: Change the HIPAS to ASSIGNED */
	inv_tte = tte & ~S2TTE_INVALID_HIPAS_MASK;
	inv_tte |= S2TTE_INVALID_HIPAS_ASSIGNED;
	CHECK_TRUE(s2tte_is_unassigned_ram((const struct s2tt_context *)&s2tt_ctx,
					    inv_tte) == false);

	/* Negative test: Test with a different type of unassigned TTE */
	idx = (unsigned int)test_helpers_get_rand_in_range(
					0UL, ARRAY_SIZE(ripas) - 1UL);
	inv_tte = s2tt_test_create_unassigned((const struct s2tt_context *)&s2tt_ctx,
					      ripas[idx], ap);
	CHECK_TRUE(s2tte_is_unassigned_ram((const struct s2tt_context *)&s2tt_ctx,
					   inv_tte) == false);
}

void s2tte_is_unassigned_ns_tc1(void)
{
	/***************************************************************
	 * TEST CASE 1:
	 *
	 * This test case cover positive tests for
	 * is_unassigned_ns() as well as a number of negative tests.
	 ***************************************************************/

	unsigned long ripas[] = {S2TTE_INVALID_RIPAS_EMPTY,
				 S2TTE_INVALID_RIPAS_DESTROYED,
				 S2TTE_INVALID_RIPAS_RAM};
	unsigned int idx;
	unsigned long inv_tte;
	unsigned long ap = s2tt_test_generate_ap(false);
	unsigned long tte;
	struct s2tt_context s2tt_ctx;

	(void)memset(&s2tt_ctx, 0, sizeof(s2tt_ctx));

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 and s2tt_ctx.indirect_s2ap ar of use
	 * on this API, so the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
	s2tt_ctx.indirect_s2ap = s2tt_test_helpers_s2pie_enabled();

	tte = s2tte_create_unassigned_ns((
					const struct s2tt_context *)&s2tt_ctx, 0UL);

	/* Validate s2tt_is_unassigned_ns with an unassigned ns TTE */
	CHECK_TRUE(s2tte_is_unassigned_ns((const struct s2tt_context *)&s2tt_ctx, tte) == true);

	/* Negative test: Set DESC_TYPE to a valid descriptor */
	inv_tte = tte | S2TT_TEST_PAGE_DESC;
	CHECK_TRUE(s2tte_is_unassigned_ns((const struct s2tt_context *)&s2tt_ctx,
					  inv_tte) == false);

	/* Negative test: Change the HIPAS to ASSIGNED */
	inv_tte = tte & ~S2TTE_INVALID_HIPAS_MASK;
	inv_tte |= S2TTE_INVALID_HIPAS_ASSIGNED;
	CHECK_TRUE(s2tte_is_unassigned_ns((const struct s2tt_context *)&s2tt_ctx,
					  inv_tte) == false);

	/* Negative test: Test with a different type of unassigned TTE */
	idx = (unsigned int)test_helpers_get_rand_in_range(
					0UL, ARRAY_SIZE(ripas) - 1UL);
	inv_tte = s2tt_test_create_unassigned((const struct s2tt_context *)&s2tt_ctx,
					      ripas[idx], ap);
	CHECK_TRUE(s2tte_is_unassigned_ns((const struct s2tt_context *)&s2tt_ctx,
					  inv_tte) == false);
}

void s2tte_is_unassigned_destroyed_tc1(void)
{
	/***************************************************************
	 * TEST CASE 1:
	 *
	 * This test case cover positive tests for
	 * is_unassigned_destroyed() as well as a number of
	 * negative tests.
	 ***************************************************************/

	unsigned long ripas[] = {S2TTE_INVALID_RIPAS_EMPTY,
				 S2TTE_NS,
				 S2TTE_INVALID_RIPAS_RAM};
	unsigned int idx;
	unsigned long inv_tte;
	unsigned long ap = s2tt_test_generate_ap(false);
	unsigned long tte;
	struct s2tt_context s2tt_ctx;

	(void)memset(&s2tt_ctx, 0, sizeof(s2tt_ctx));

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 and s2tt_ctx.indirect_s2ap ar of use
	 * on this API, so the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
	s2tt_ctx.indirect_s2ap = s2tt_test_helpers_s2pie_enabled();

	tte = s2tte_create_unassigned_destroyed(
					(const struct s2tt_context *)&s2tt_ctx, ap);

	/* Validate s2tt_is_unassigned_destroyed with an unassigned destroyed TTE */
	CHECK_TRUE(s2tte_is_unassigned_destroyed(
				(const struct s2tt_context *)&s2tt_ctx, tte) == true);

	/* Negative test: Set DESC_TYPE to a valid descriptor */
	inv_tte = tte | S2TT_TEST_PAGE_DESC;
	CHECK_TRUE(s2tte_is_unassigned_destroyed(
				(const struct s2tt_context *)&s2tt_ctx, inv_tte) == false);

	/* Negative test: Change the HIPAS to ASSIGNED */
	inv_tte = tte & ~S2TTE_INVALID_HIPAS_MASK;
	inv_tte |= S2TTE_INVALID_HIPAS_ASSIGNED;
	CHECK_TRUE(s2tte_is_unassigned_destroyed(
				(const struct s2tt_context *)&s2tt_ctx, inv_tte) == false);

	/* Negative test: Test with a different type of unassigned TTE */
	idx = (unsigned int)test_helpers_get_rand_in_range(
					0UL, ARRAY_SIZE(ripas) - 1UL);
	inv_tte = s2tt_test_create_unassigned((const struct s2tt_context *)&s2tt_ctx,
					      ripas[idx], ap);
	CHECK_FALSE(s2tte_is_unassigned_destroyed((const struct s2tt_context *)&s2tt_ctx,
						  inv_tte));
}

void s2tte_is_assigned_empty_tc1(void)
{
	/***************************************************************
	 * TEST CASE 1:
	 *
	 * This test case cover positive tests for is_assigned_empty()
	 * as well as a number of negative tests for each valid level.
	 ***************************************************************/

	unsigned long ripas[] = {S2TTE_NS,
				 S2TTE_INVALID_RIPAS_RAM,
				 S2TTE_INVALID_RIPAS_DESTROYED};
	unsigned long ap = s2tt_test_generate_ap(false);
	struct s2tt_context s2tt_ctx;

	(void)memset(&s2tt_ctx, 0, sizeof(s2tt_ctx));

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 and s2tt_ctx.indirect_s2ap ar of use
	 * on this API, so the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
	s2tt_ctx.indirect_s2ap = s2tt_test_helpers_s2pie_enabled();

	for (long level = s2tt_test_helpers_min_block_lvl();
	     level <= S2TT_TEST_HELPERS_MAX_LVL; level++) {
		unsigned int idx;
		unsigned long pa = s2tt_test_helpers_gen_addr(level, true);
		unsigned long inv_tte, tte =
			s2tte_create_assigned_empty(
					(const struct s2tt_context *)&s2tt_ctx,
					pa, level, ap);

		/* Validate s2tt_is_assigned_empty with an assigned empty TTE */
		CHECK_TRUE(s2tte_is_assigned_empty((const struct s2tt_context *)&s2tt_ctx,
						   tte, level) == true);

		/* Negative test: Set DESC_TYPE to a valid descriptor */
		inv_tte = tte | S2TT_TEST_PAGE_DESC;
		CHECK_TRUE(s2tte_is_assigned_empty((const struct s2tt_context *)&s2tt_ctx,
						   inv_tte, level) == false);

		/* Negative test: Change the HIPAS to UNASSIGNED */
		inv_tte = tte & ~S2TTE_INVALID_HIPAS_MASK;
		inv_tte |= S2TTE_INVALID_HIPAS_UNASSIGNED;
		CHECK_TRUE(s2tte_is_assigned_empty((const struct s2tt_context *)&s2tt_ctx,
						   inv_tte, level) == false);

		/* Negative test: Test with a different type of assigned TTE */
		idx = (unsigned int)test_helpers_get_rand_in_range(
					0UL, ARRAY_SIZE(ripas) - 1UL);
		inv_tte = s2tt_test_create_assigned((const struct s2tt_context *)&s2tt_ctx,
						pa, level, ripas[idx], ap);
		CHECK_TRUE(s2tte_is_assigned_empty((const struct s2tt_context *)&s2tt_ctx,
					inv_tte, level) == false);
	}
}

void s2tte_is_assigned_ns_tc1(void)
{
	/***************************************************************
	 * TEST CASE 1:
	 *
	 * This test case cover positive tests for is_assigned_ns()
	 * as well as a number of negative tests for each valid level.
	 ***************************************************************/

	unsigned long ripas[] = {S2TTE_INVALID_RIPAS_EMPTY,
				 S2TTE_INVALID_RIPAS_RAM,
				 S2TTE_INVALID_RIPAS_DESTROYED};
	unsigned long ap = s2tt_test_generate_ap(false);
	struct s2tt_context s2tt_ctx;

	(void)memset(&s2tt_ctx, 0, sizeof(s2tt_ctx));

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 and s2tt_ctx.indirect_s2ap ar of use
	 * on this API, so the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
	s2tt_ctx.indirect_s2ap = s2tt_test_helpers_s2pie_enabled();

	for (long level = s2tt_test_helpers_min_block_lvl();
	     level <= S2TT_TEST_HELPERS_MAX_LVL; level++) {
		unsigned int idx;
		unsigned long pa = s2tt_test_helpers_gen_addr(level, true);
		unsigned long inv_tte, tte =
				s2tt_test_helpers_gen_ns_attrs(true, false);

		tte = s2tte_create_assigned_ns((const struct s2tt_context *)&s2tt_ctx,
				s2tt_test_helpers_pa_to_s2tte(pa, level) | tte,
				level, ap);

		/* Validate s2tt_is_assigned_ns with an assigned ns TTE */
		CHECK_TRUE(s2tte_is_assigned_ns((const struct s2tt_context *)&s2tt_ctx,
						tte, level) == true);

		/*
		 * Negative test: Test using UNASSIGNED_NS TTE
		 */
		inv_tte = s2tte_create_unassigned_ns(
					(const struct s2tt_context *)&s2tt_ctx, 0UL);
		CHECK_TRUE(s2tte_is_assigned_ns((const struct s2tt_context *)&s2tt_ctx,
						inv_tte, level) == false);

		/*
		 * Negative test: Test with a different type of assigned TTE
		 * which has RIPAS.
		 */
		idx = (unsigned int)test_helpers_get_rand_in_range(
					0UL, ARRAY_SIZE(ripas) - 1UL);
		inv_tte = s2tt_test_create_assigned((const struct s2tt_context *)&s2tt_ctx,
						pa, level, ripas[idx], ap);
		CHECK_TRUE(s2tte_is_assigned_ns((const struct s2tt_context *)&s2tt_ctx,
						inv_tte, level) == false);
	}
}

void s2tte_is_assigned_ns_tc2(void)
{
	/***************************************************************
	 * TEST CASE 2:
	 *
	 * Test s2tte_is_assigned_ns() with invalid levels.
	 ***************************************************************/
	unsigned long pa = 0UL;
	unsigned long tte = s2tt_test_helpers_gen_ns_attrs(true, false);
	long level = s2tt_test_helpers_min_block_lvl();
	unsigned long ap = 0UL; /* Valid on any level */
	struct s2tt_context s2tt_ctx;

	(void)memset(&s2tt_ctx, 0, sizeof(s2tt_ctx));

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 and s2tt_ctx.indirect_s2ap ar of use
	 * on this API, so the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
	s2tt_ctx.indirect_s2ap = s2tt_test_helpers_s2pie_enabled();

	tte = s2tte_create_assigned_ns(
			(const struct s2tt_context *)&s2tt_ctx,
			s2tt_test_helpers_pa_to_s2tte(pa, level) | tte,
					level, ap);

	/* Validate s2tt_is_assigned_ns with an assigned ns TTE */
	CHECK_FALSE(s2tte_is_assigned_ns((const struct s2tt_context *)&s2tt_ctx, tte,
					 s2tt_test_helpers_min_table_lvl()));
	CHECK_FALSE(s2tte_is_assigned_ns((const struct s2tt_context *)&s2tt_ctx, tte,
					S2TT_TEST_HELPERS_MAX_LVL));
}

void s2tte_is_assigned_ram_tc1(void)
{
	/***************************************************************
	 * TEST CASE 1:
	 *
	 * This test case cover positive tests for is_assigned_ram()
	 * as well as a number of negative tests for each valid level.
	 ***************************************************************/

	unsigned long ripas[] = {S2TTE_NS,
				 S2TTE_INVALID_RIPAS_EMPTY,
				 S2TTE_INVALID_RIPAS_DESTROYED};
	struct s2tt_context s2tt_ctx;

	(void)memset(&s2tt_ctx, 0, sizeof(s2tt_ctx));

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 and s2tt_ctx.indirect_s2ap ar of use
	 * on this API, so the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
	s2tt_ctx.indirect_s2ap = s2tt_test_helpers_s2pie_enabled();

	for (long level = s2tt_test_helpers_min_block_lvl();
	     level <= S2TT_TEST_HELPERS_MAX_LVL; level++) {
		unsigned int idx;
		unsigned long pa = s2tt_test_helpers_gen_addr(level, true);
		unsigned long ap = s2tt_test_generate_ap(false);
		unsigned long inv_tte, tte =
			s2tte_create_assigned_ram((const struct s2tt_context *)&s2tt_ctx,
						  pa, level, ap);

		/* Validate s2tt_is_assigned_ram with an assigned ram TTE */
		CHECK_TRUE(s2tte_is_assigned_ram((const struct s2tt_context *)&s2tt_ctx,
						 tte, level) == true);

		/*
		 * Negative test: Test with UNASSIGNED-RAM
		 * We test with UNASSIGNED-RAM as in the current RMM implementation,
		 * an ASSIGNED-RAM S2TTE does not have HIPAS field, so we pick
		 * up an S2TTE with a HIPAS other than ASSIGNED.
		 */
		inv_tte = s2tte_create_unassigned_ram(
				(const struct s2tt_context *)&s2tt_ctx, ap);
		CHECK_TRUE(s2tte_is_assigned_ram((const struct s2tt_context *)&s2tt_ctx,
						 inv_tte, level) == false);

		/* Negative test: Test with a different type of RIPAS */
		idx = (unsigned int)test_helpers_get_rand_in_range(
					0UL, ARRAY_SIZE(ripas) - 1UL);
		inv_tte = s2tt_test_create_assigned((const struct s2tt_context *)&s2tt_ctx,
						pa, level, ripas[idx], ap);
		CHECK_TRUE(s2tte_is_assigned_ram((const struct s2tt_context *)&s2tt_ctx,
						 inv_tte, level) == false);
	}
}

void s2tte_is_assigned_ram_tc2(void)
{
	/***************************************************************
	 * TEST CASE 2:
	 *
	 * Test s2tte_is_assigned_ram() with invalid levels.
	 ***************************************************************/
	unsigned long pa = 0UL;
	unsigned long tte;
	unsigned long ap = 0UL; /* Valid on any level */
	struct s2tt_context s2tt_ctx;

	(void)memset(&s2tt_ctx, 0, sizeof(s2tt_ctx));

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 and s2tt_ctx.indirect_s2ap ar of use
	 * on this API, so the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
	s2tt_ctx.indirect_s2ap = s2tt_test_helpers_s2pie_enabled();

	tte = s2tte_create_assigned_ram((const struct s2tt_context *)&s2tt_ctx,
					pa, s2tt_test_helpers_min_block_lvl(), ap);

	/* Validate s2tt_is_assigned_ram with an assigned ram TTE */
	CHECK_FALSE(s2tte_is_assigned_ram((const struct s2tt_context *)&s2tt_ctx,
					  tte, s2tt_test_helpers_min_block_lvl() - 1L));
	CHECK_FALSE(s2tte_is_assigned_ram((const struct s2tt_context *)&s2tt_ctx,
					  tte, S2TT_TEST_HELPERS_MAX_LVL));
}

void s2tte_is_assigned_destroyed_tc1(void)
{
	/***************************************************************
	 * TEST CASE 1:
	 *
	 * This test case cover positive tests for
	 * is_assigned_destroyed() as well as a number of negative
	 * tests for each valid level.
	 ***************************************************************/

	unsigned long ripas[] = {S2TTE_NS,
				 S2TTE_INVALID_RIPAS_RAM,
				 S2TTE_INVALID_RIPAS_EMPTY};
	struct s2tt_context s2tt_ctx;

	(void)memset(&s2tt_ctx, 0, sizeof(s2tt_ctx));

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 and s2tt_ctx.indirect_s2ap ar of use
	 * on this API, so the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
	s2tt_ctx.indirect_s2ap = s2tt_test_helpers_s2pie_enabled();

	for (long level = s2tt_test_helpers_min_block_lvl();
	     level <= S2TT_TEST_HELPERS_MAX_LVL; level++) {
		unsigned int idx;
		unsigned long pa = s2tt_test_helpers_gen_addr(level, true);
		unsigned long ap = s2tt_test_generate_ap(false);
		unsigned long inv_tte, tte =
			s2tte_create_assigned_destroyed(
					(const struct s2tt_context *)&s2tt_ctx,
					pa, level, ap);

		/* Validate s2tt_is_assigned_destroyed with an assigned destroyed TTE */
		CHECK_TRUE(s2tte_is_assigned_destroyed((const struct s2tt_context *)&s2tt_ctx,
							tte, level) == true);

		/* Negative test: Set DESC_TYPE to a valid descriptor */
		inv_tte = tte | S2TT_TEST_PAGE_DESC;
		CHECK_TRUE(s2tte_is_assigned_destroyed((const struct s2tt_context *)&s2tt_ctx,
						inv_tte, level) == false);

		/* Negative test: Change the HIPAS to UNASSIGNED */
		inv_tte = tte & ~S2TTE_INVALID_HIPAS_MASK;
		inv_tte |= S2TTE_INVALID_HIPAS_UNASSIGNED;
		CHECK_TRUE(s2tte_is_assigned_destroyed((const struct s2tt_context *)&s2tt_ctx,
						inv_tte, level) == false);

		/* Negative test: Test with a different RIPAS */
		idx = (unsigned int)test_helpers_get_rand_in_range(
					0UL, ARRAY_SIZE(ripas) - 1UL);
		inv_tte = s2tt_test_create_assigned((const struct s2tt_context *)&s2tt_ctx,
						pa, level, ripas[idx], ap);
		CHECK_TRUE(s2tte_is_assigned_destroyed((const struct s2tt_context *)&s2tt_ctx,
						inv_tte, level) == false);
	}
}

void s2tte_is_table_tc1(void)
{
	/***************************************************************
	 * TEST CASE 1:
	 *
	 * This test case cover positive tests for is_table() as well
	 * as a number of negative tests for each valid level.
	 ***************************************************************/

	struct s2tt_context s2tt_ctx;

	(void)memset(&s2tt_ctx, 0, sizeof(s2tt_ctx));

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 and s2tt_ctx.indirect_s2ap ar of use
	 * on this API, so the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
	s2tt_ctx.indirect_s2ap = s2tt_test_helpers_s2pie_enabled();

	for (long level = s2tt_test_helpers_min_table_lvl();
	     level <= S2TT_TEST_HELPERS_MAX_LVL; level++) {
		unsigned long pa, inv_tte, tte = 0UL;

		if (level <= S2TT_TEST_HELPERS_MAX_TABLE_LVL) {
			/* Validate s2tt_is_table with a valid table TTE */
			pa = s2tt_test_helpers_gen_addr(level, true);
			tte = s2tte_create_table(
					(const struct s2tt_context *)&s2tt_ctx,
					pa, level);
			CHECK_TRUE(s2tte_is_table((const struct s2tt_context *)&s2tt_ctx,
						  tte, level) == true);
		} else {
			/*
			 * Per aarch64 VMSA, PAGE and TABLE S2TTEs share the
			 * same descriptor type ID, but the PAGE will only be
			 * allowed into the last supported level. So reuse the
			 * previous tte and test again with the PAGE level.
			 */
			CHECK_TRUE(s2tte_is_table((const struct s2tt_context *)&s2tt_ctx,
						  tte, level) == false);
		}

		/* Negative test: Set DESC_TYPE to INVALID */
		inv_tte = tte & ~S2TT_TEST_DESC_TYPE_MASK;
		inv_tte = inv_tte | S2TT_TEST_INVALID_DESC;
		CHECK_TRUE(s2tte_is_table((const struct s2tt_context *)&s2tt_ctx,
					  inv_tte, level) == false);

		/* Negative test: Set DESC_TYPE to BLOCK */
		inv_tte = tte & ~S2TT_TEST_DESC_TYPE_MASK;
		inv_tte = inv_tte | S2TT_TEST_BLOCK_DESC;
		CHECK_TRUE(s2tte_is_table((const struct s2tt_context *)&s2tt_ctx,
					  inv_tte, level) == false);
	}
}

void s2tte_get_ripas_tc1(void)
{
	/***************************************************************
	 * TEST CASE 1:
	 *
	 * For all possible RIPAS types, generate a HIPAS ASSIGNED and
	 * a HIPAS UNASSIGNED S2TTE and verify that s2tt_get_ripas()
	 * returns the right RIPAS
	 ***************************************************************/

	unsigned long tte, pa;
	unsigned long ripas[] = {S2TTE_INVALID_RIPAS_EMPTY,
				 S2TTE_INVALID_RIPAS_RAM,
				 S2TTE_INVALID_RIPAS_DESTROYED};
	struct s2tt_context s2tt_ctx;

	(void)memset(&s2tt_ctx, 0, sizeof(s2tt_ctx));

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 and s2tt_ctx.indirect_s2ap ar of use
	 * on this API, so the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
	s2tt_ctx.indirect_s2ap = s2tt_test_helpers_s2pie_enabled();

	for (unsigned int i = 0U; i < ARRAY_SIZE(ripas); i++) {
		unsigned long ap = s2tt_test_generate_ap(false);

		/* HIPAS = UNASSIGNED */
		tte = s2tt_test_create_unassigned(
				(const struct s2tt_context *)&s2tt_ctx, ripas[i], ap);
		UNSIGNED_LONGS_EQUAL((unsigned int)s2tte_get_ripas(
					(const struct s2tt_context *)&s2tt_ctx, tte),
				     EXTRACT(S2TTE_INVALID_RIPAS, ripas[i]));

		/* HIPAS = ASSIGNED */
		for (long level = s2tt_test_helpers_min_block_lvl();
		     level <= S2TT_TEST_HELPERS_MAX_LVL; level++) {
			pa = s2tt_test_helpers_gen_addr(level, true);
			tte = s2tt_test_create_assigned(
				(const struct s2tt_context *)&s2tt_ctx,
					pa, level, ripas[i], ap);
			UNSIGNED_LONGS_EQUAL(
				(unsigned int)s2tte_get_ripas(
					(const struct s2tt_context *)&s2tt_ctx, tte),
					EXTRACT(S2TTE_INVALID_RIPAS, ripas[i]));
		}
	}
}

void s2tte_get_ripas_tc2(void)
{
	/***************************************************************
	 * TEST CASE 2:
	 *
	 * Test s2tte_get_ripas() with an invalid S2TTE and an invalid
	 * HIPAS.
	 ***************************************************************/

	unsigned long ap = 0UL; /* Valid on any level */
	unsigned long tte;
	struct s2tt_context s2tt_ctx;

	(void)memset(&s2tt_ctx, 0, sizeof(s2tt_ctx));

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 and s2tt_ctx.indirect_s2ap ar of use
	 * on this API, so the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
	s2tt_ctx.indirect_s2ap = s2tt_test_helpers_s2pie_enabled();

	tte = s2tte_create_unassigned_destroyed(
				(const struct s2tt_context *)&s2tt_ctx, ap);
	tte &= ~S2TTE_INVALID_HIPAS_MASK;

	/*
	 * As per s2tt_pvt_defs.h, HIPAS field is 3 bits wide with only the
	 * first 2 bits used. Get random invalid HIPAS to test with.
	 */
	unsigned long inv_hipas = test_helpers_get_rand_in_range(
					RMI_ASSIGNED_DEV + 1UL, 7UL);

	tte &= ~S2TTE_INVALID_HIPAS_MASK;
	tte |= INPLACE(S2TTE_INVALID_HIPAS, inv_hipas);

	test_helpers_expect_assert_fail(true);
	(void)s2tte_get_ripas((const struct s2tt_context *)NULL, tte);
	test_helpers_fail_if_no_assert_failed();
}

void s2tte_get_ripas_tc3(void)
{
	/***************************************************************
	 * TEST CASE 3:
	 *
	 * Test s2tte_get_ripas() with an invalid S2TTE and an invalid
	 * HIPAS=RMI_TABLE.
	 ***************************************************************/

	struct s2tt_context s2tt_ctx;
	unsigned long tte;

	(void)memset(&s2tt_ctx, 0, sizeof(s2tt_ctx));

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 and s2tt_ctx.indirect_s2ap ar of use
	 * on this API, so the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
	s2tt_ctx.indirect_s2ap = s2tt_test_helpers_s2pie_enabled();

	tte = s2tte_create_unassigned_destroyed(
					(const struct s2tt_context *)&s2tt_ctx, 0UL);
	tte &= ~S2TTE_INVALID_HIPAS_MASK;
	tte |= INPLACE(S2TTE_INVALID_HIPAS, RMI_TABLE);

	test_helpers_expect_assert_fail(true);
	(void)s2tte_get_ripas((const struct s2tt_context *)&s2tt_ctx, tte);
	test_helpers_fail_if_no_assert_failed();
}

void s2tt_init_unassigned_empty_tc1(void)
{
	/***************************************************************
	 * TEST CASE 1:
	 *
	 * Initialize a table with unassigned empty S2TTEs and validate
	 * its content.
	 ***************************************************************/

	unsigned long s2tt[S2TTES_PER_S2TT] = { 0UL };
	unsigned long val_s2tt[S2TTES_PER_S2TT];
	unsigned long ap = s2tt_test_generate_ap(false);
	struct s2tt_context s2tt_ctx;

	(void)memset(&s2tt_ctx, 0, sizeof(s2tt_ctx));

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 and s2tt_ctx.indirect_s2ap ar of use
	 * on this API, so the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
	s2tt_ctx.indirect_s2ap = s2tt_test_helpers_s2pie_enabled();

	/* Generate the validation table */
	for (unsigned int i = 0U; i < S2TTES_PER_S2TT; i++) {
		val_s2tt[i] =
			s2tte_create_unassigned_empty(
				(const struct s2tt_context *)&s2tt_ctx, ap);
	}

	/*
	 * Generate the test table. Note that s2tt_init_unassigned_empty()
	 * can take a NULL s2tt_context pointer.
	 */
	s2tt_init_unassigned_empty((const struct s2tt_context *)&s2tt_ctx, &s2tt[0], ap);

	/* Validate */
	MEMCMP_EQUAL(val_s2tt, s2tt, sizeof(s2tt));
}

void s2tt_init_unassigned_empty_tc2(void)
{
	/***************************************************************
	 * TEST CASE 2:
	 *
	 * Invoke s2tt_init_unassigned_empty() passing a NULL
	 * s2tt pointer.
	 *
	 * Note that s2tt_init_unassigned_empty() can take a NULL
	 * s2tt_context pointer.
	 ***************************************************************/

	test_helpers_expect_assert_fail(true);
	s2tt_init_unassigned_empty((const struct s2tt_context *)NULL, NULL, 0UL);
	test_helpers_fail_if_no_assert_failed();
}

void s2tt_init_unassigned_ram_tc1(void)
{
	/***************************************************************
	 * TEST CASE 1:
	 *
	 * Initialize a table with unassigned ram S2TTEs and validate its
	 * content.
	 ***************************************************************/

	unsigned long s2tt[S2TTES_PER_S2TT] = { 0UL };
	unsigned long val_s2tt[S2TTES_PER_S2TT];
	unsigned long ap = s2tt_test_generate_ap(false);
	struct s2tt_context s2tt_ctx;

	(void)memset(&s2tt_ctx, 0, sizeof(s2tt_ctx));

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 and s2tt_ctx.indirect_s2ap ar of use
	 * on this API, so the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
	s2tt_ctx.indirect_s2ap = s2tt_test_helpers_s2pie_enabled();

	/* Generate the validation table */
	for (unsigned int i = 0U; i < S2TTES_PER_S2TT; i++) {
		val_s2tt[i] = s2tte_create_unassigned_ram(
				(const struct s2tt_context *)&s2tt_ctx, ap);
	}

	/*
	 * Generate the test table. Note that s2tt_init_unassigned_ram()
	 * can take a NULL pointer to struct s2tt_context.
	 */
	s2tt_init_unassigned_ram((const struct s2tt_context *)&s2tt_ctx, &s2tt[0], ap);

	/* Validate */
	MEMCMP_EQUAL(val_s2tt, s2tt, sizeof(s2tt));
}

void s2tt_init_unassigned_ram_tc2(void)
{
	/***************************************************************
	 * TEST CASE 2:
	 *
	 * Invoke init_unassigned_ram() passing a NULL pointer.
	 *
	 * Note that s2tt_init_unassigned_ram() can take a NULL pointer
	 * to struct s2tt_context.
	 ***************************************************************/

	test_helpers_expect_assert_fail(true);
	s2tt_init_unassigned_ram((const struct s2tt_context *)NULL, NULL, 0UL);
	test_helpers_fail_if_no_assert_failed();
}

void s2tt_init_unassigned_ns_tc1(void)
{
	/***************************************************************
	 * TEST CASE 1:
	 *
	 * Initialize a table with unassigned ns S2TTEs and validate
	 * its content.
	 ***************************************************************/

	unsigned long s2tt[S2TTES_PER_S2TT] = { 0UL };
	unsigned long val_s2tt[S2TTES_PER_S2TT];

	/* Generate the validation table */
	for (unsigned int i = 0U; i < S2TTES_PER_S2TT; i++) {
		val_s2tt[i] = s2tte_create_unassigned_ns(
				(const struct s2tt_context *)NULL, 0UL);
	}

	/*
	 * Generate the test table. Note that s2tt_init_unassigned_ns()
	 * can take a NULL s2tt_context pointer.
	 */
	s2tt_init_unassigned_ns((const struct s2tt_context *)NULL, &s2tt[0], 0UL);

	/* Validate */
	MEMCMP_EQUAL(val_s2tt, s2tt, sizeof(s2tt));
}

void s2tt_init_unassigned_ns_tc2(void)
{
	/***************************************************************
	 * TEST CASE 2:
	 *
	 * Invoke init_unassigned_ns() passing a NULL pointer.
	 *
	 * Note that s2tt_init_unassigned_ns() can take a NULL
	 * struct s2tt_context pointer.
	 ***************************************************************/

	test_helpers_expect_assert_fail(true);
	s2tt_init_unassigned_ns((const struct s2tt_context *)NULL, NULL, 0UL);
	test_helpers_fail_if_no_assert_failed();
}

void s2tt_init_unassigned_destroyed_tc1(void)
{
	/***************************************************************
	 * TEST CASE 1:
	 *
	 * Initialize a table with unassigned destroyed S2TTEs
	 * and validate its content.
	 ***************************************************************/

	unsigned long s2tt[S2TTES_PER_S2TT] = { 0UL };
	unsigned long val_s2tt[S2TTES_PER_S2TT];
	unsigned long ap = s2tt_test_generate_ap(false);
	struct s2tt_context s2tt_ctx;

	(void)memset(&s2tt_ctx, 0, sizeof(s2tt_ctx));

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 and s2tt_ctx.indirect_s2ap ar of use
	 * on this API, so the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
	s2tt_ctx.indirect_s2ap = s2tt_test_helpers_s2pie_enabled();

	/* Generate the validation table */
	for (unsigned int i = 0U; i < S2TTES_PER_S2TT; i++) {
		val_s2tt[i] =
			s2tte_create_unassigned_destroyed(
				(const struct s2tt_context *)&s2tt_ctx, ap);
	}

	/*
	 * Generate the test table. Note that s2tt_init_unassigned_destroyed()
	 * can take a NULL s2tt_context pointer.
	 */
	s2tt_init_unassigned_destroyed((const struct s2tt_context *)&s2tt_ctx,
					&s2tt[0], ap);

	/* Validate */
	MEMCMP_EQUAL(val_s2tt, s2tt, sizeof(s2tt));
}

void s2tt_init_unassigned_destroyed_tc2(void)
{
	/***************************************************************
	 * TEST CASE 2:
	 *
	 * Invoke s2tt_init_unassigned_destroyed() passing a NULL pointer.
	 *
	 * Note that s2tt_init_unassigned_destroyed() can take a NULL
	 * pointer to struct s2tt_context.
	 ***************************************************************/

	test_helpers_expect_assert_fail(true);
	s2tt_init_unassigned_destroyed((const struct s2tt_context *)NULL, NULL, 0UL);
	test_helpers_fail_if_no_assert_failed();
}

void s2tt_init_assigned_empty_tc1(void)
{
	/***************************************************************
	 * TEST CASE 1:
	 *
	 * For each valid level, initialize a table with assigned-empty
	 * S2TTEs and validate its contents.
	 ***************************************************************/

	struct s2tt_context s2tt_ctx;

	(void)memset(&s2tt_ctx, 0, sizeof(s2tt_ctx));

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 and s2tt_ctx.indirect_s2ap ar of use
	 * on this API, so the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
	s2tt_ctx.indirect_s2ap = s2tt_test_helpers_s2pie_enabled();

	for (long level = s2tt_test_helpers_min_block_lvl();
	     level <= S2TT_TEST_HELPERS_MAX_LVL; level++) {

		unsigned long s2tt[S2TTES_PER_S2TT] = {0};
		unsigned long pa = s2tt_test_helpers_gen_addr(level - 1L, true);
		unsigned long ap = s2tt_test_generate_ap(false);

		/* Generate the table */
		s2tt_init_assigned_empty((const struct s2tt_context *)&s2tt_ctx,
					 &s2tt[0], pa, level, ap);

		/* Validate the content of the table */
		for (unsigned int i = 0U; i < S2TTES_PER_S2TT; i++) {
			unsigned long s2tte;

			s2tte =	s2tte_create_assigned_empty(
					(const struct s2tt_context *)&s2tt_ctx,
					pa, level, ap);
			pa += s2tte_map_size(level);

			UNSIGNED_LONGS_EQUAL(s2tte, s2tt[i]);
		}
	}
}

void s2tt_init_assigned_empty_tc2(void)
{
	/***************************************************************
	 * TEST CASE 2:
	 *
	 * For a valid address, try to create an assigned-empty S2TT
	 * with a level above the maximum.
	 ***************************************************************/

	unsigned long s2tt[S2TTES_PER_S2TT] = {0};
	long level = S2TT_TEST_HELPERS_MAX_LVL + 1L;
	unsigned long pa = 0UL; /* Valid for any level */
	unsigned long ap = 0UL; /* Valid on any level */
	struct s2tt_context s2tt_ctx;

	(void)memset(&s2tt_ctx, 0, sizeof(s2tt_ctx));

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 and s2tt_ctx.indirect_s2ap ar of use
	 * on this API, so the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
	s2tt_ctx.indirect_s2ap = s2tt_test_helpers_s2pie_enabled();

	test_helpers_expect_assert_fail(true);
	s2tt_init_assigned_empty((const struct s2tt_context *)&s2tt_ctx,
				 &s2tt[0U], pa, level, ap);
	test_helpers_fail_if_no_assert_failed();
}

void s2tt_init_assigned_empty_tc3(void)
{
	/***************************************************************
	 * TEST CASE 3:
	 *
	 * For a valid address, try to create an assigned-empty S2TT
	 * with a level below the minimum.
	 ***************************************************************/

	unsigned long s2tt[S2TTES_PER_S2TT] = {0};
	long level = s2tt_test_helpers_min_block_lvl() - 1L;
	unsigned long pa = 0UL; /* Valid for any level */
	unsigned long ap = 0UL; /* Valid on any level */
	struct s2tt_context s2tt_ctx;

	(void)memset(&s2tt_ctx, 0, sizeof(s2tt_ctx));

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 and s2tt_ctx.indirect_s2ap ar of use
	 * on this API, so the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
	s2tt_ctx.indirect_s2ap = s2tt_test_helpers_s2pie_enabled();

	test_helpers_expect_assert_fail(true);
	s2tt_init_assigned_empty((const struct s2tt_context *)&s2tt_ctx,
				 &s2tt[0U], pa, level, ap);
	test_helpers_fail_if_no_assert_failed();
}

void s2tt_init_assigned_empty_tc4(void)
{
	/***************************************************************
	 * TEST CASE 4:
	 *
	 * Invoke s2tt_init_assigned_empty() with a NULL table pointer.
	 ***************************************************************/

	long level = s2tt_test_helpers_min_block_lvl();
	unsigned long pa = 0UL; /* Valid for any level */
	unsigned long ap = 0UL; /* Valid on any level */
	struct s2tt_context s2tt_ctx;

	(void)memset(&s2tt_ctx, 0, sizeof(s2tt_ctx));

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 and s2tt_ctx.indirect_s2ap ar of use
	 * on this API, so the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
	s2tt_ctx.indirect_s2ap = s2tt_test_helpers_s2pie_enabled();

	test_helpers_expect_assert_fail(true);
	s2tt_init_assigned_empty((const struct s2tt_context *)&s2tt_ctx,
				 NULL, pa, level, ap);
	test_helpers_fail_if_no_assert_failed();
}

void s2tt_init_assigned_empty_tc5(void)
{
	/***************************************************************
	 * TEST CASE 5:
	 *
	 * Invoke s2tt_init_assigned_empty() with an unaligned address.
	 ***************************************************************/

	unsigned long s2tt[S2TTES_PER_S2TT] = {0};
	long level =
		test_helpers_get_rand_in_range(s2tt_test_helpers_min_block_lvl(),
					       S2TT_TEST_HELPERS_MAX_LVL);
	unsigned long pa = s2tt_test_helpers_gen_addr(level, true) +
		test_helpers_get_rand_in_range(1UL, (unsigned long)GRANULE_SIZE - 1UL);
	unsigned long ap = 0UL; /* Valid on any level */
	struct s2tt_context s2tt_ctx;

	(void)memset(&s2tt_ctx, 0, sizeof(s2tt_ctx));

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 and s2tt_ctx.indirect_s2ap ar of use
	 * on this API, so the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
	s2tt_ctx.indirect_s2ap = s2tt_test_helpers_s2pie_enabled();

	test_helpers_expect_assert_fail(true);
	s2tt_init_assigned_empty((const struct s2tt_context *)&s2tt_ctx,
				 &s2tt[0U], pa, level, ap);
	test_helpers_fail_if_no_assert_failed();
}

void s2tt_init_assigned_empty_tc6(void)
{
	/***************************************************************
	 * TEST CASE 6:
	 *
	 * Invoke s2tt_init_assigned_empty() with a NULL s2tt_context
	 * structure.
	 ***************************************************************/
	unsigned long s2tt[S2TTES_PER_S2TT] = {0};
	long level = s2tt_test_helpers_min_block_lvl();
	unsigned long ap = 0UL; /* Valid on any level */
	unsigned long pa = 0UL; /* Valid for any level */

	test_helpers_expect_assert_fail(true);
	s2tt_init_assigned_empty((const struct s2tt_context *)NULL,
				 &s2tt[0U], pa, level, ap);
	test_helpers_fail_if_no_assert_failed();
}

void s2tt_init_assigned_ram_tc1(void)
{
	/***************************************************************
	 * TEST CASE 1:
	 *
	 * For each valid level, initialize a table with assigned-ram
	 * S2TTEs and validate its contents.
	 ***************************************************************/

	struct s2tt_context s2tt_ctx;

	(void)memset(&s2tt_ctx, 0, sizeof(s2tt_ctx));

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 and s2tt_ctx.indirect_s2ap ar of use
	 * on this API, so the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
	s2tt_ctx.indirect_s2ap = s2tt_test_helpers_s2pie_enabled();

	for (long level = s2tt_test_helpers_min_block_lvl();
	     level <= S2TT_TEST_HELPERS_MAX_LVL; level++) {

		unsigned long s2tt[S2TTES_PER_S2TT] = {0};
		unsigned long pa = s2tt_test_helpers_gen_addr(level - 1L, true);
		unsigned long ap = s2tt_test_generate_ap(false);

		/* Generate the table */
		s2tt_init_assigned_ram((const struct s2tt_context *)&s2tt_ctx,
					&s2tt[0], pa, level, ap);

		/* Validate the content of the table */
		for (unsigned int i = 0U; i < S2TTES_PER_S2TT; i++) {
			unsigned long s2tte;

			s2tte =	s2tte_create_assigned_ram(
					(const struct s2tt_context *)&s2tt_ctx,
					pa, level, ap);
			pa += s2tte_map_size(level);

			UNSIGNED_LONGS_EQUAL(s2tte, s2tt[i]);
		}
	}
}

void s2tt_init_assigned_ram_tc2(void)
{
	/***************************************************************
	 * TEST CASE 2:
	 *
	 * For a valid address, try to create an assigned-ram S2TT
	 * with a level above the maximum.
	 ***************************************************************/

	unsigned long s2tt[S2TTES_PER_S2TT] = {0};
	long level = S2TT_TEST_HELPERS_MAX_LVL + 1L;
	unsigned long pa = 0UL; /* Valid for any level */
	unsigned long ap = 0UL; /* Valid on any level */
	struct s2tt_context s2tt_ctx;

	(void)memset(&s2tt_ctx, 0, sizeof(s2tt_ctx));

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 and s2tt_ctx.indirect_s2ap ar of use
	 * on this API, so the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
	s2tt_ctx.indirect_s2ap = s2tt_test_helpers_s2pie_enabled();

	test_helpers_expect_assert_fail(true);
	s2tt_init_assigned_ram((const struct s2tt_context *)&s2tt_ctx,
				&s2tt[0U], pa, level, ap);
	test_helpers_fail_if_no_assert_failed();
}

void s2tt_init_assigned_ram_tc3(void)
{
	/***************************************************************
	 * TEST CASE 3:
	 *
	 * For a valid address, try to create an assigned-ram S2TT
	 * with a level below the minimum.
	 ***************************************************************/

	unsigned long s2tt[S2TTES_PER_S2TT] = {0};
	long level = s2tt_test_helpers_min_block_lvl() - 1L;
	unsigned long pa = 0UL; /* Valid for any level */
	unsigned long ap = 0UL; /* Valid on any level */
	struct s2tt_context s2tt_ctx;

	(void)memset(&s2tt_ctx, 0, sizeof(s2tt_ctx));

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 and s2tt_ctx.indirect_s2ap ar of use
	 * on this API, so the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
	s2tt_ctx.indirect_s2ap = s2tt_test_helpers_s2pie_enabled();

	test_helpers_expect_assert_fail(true);
	s2tt_init_assigned_ram((const struct s2tt_context *)&s2tt_ctx,
				&s2tt[0U], pa, level, ap);
	test_helpers_fail_if_no_assert_failed();
}

void s2tt_init_assigned_ram_tc4(void)
{
	/***************************************************************
	 * TEST CASE 4:
	 *
	 * Invoke s2tt_init_assigned_ram() with a NULL table pointer.
	 ***************************************************************/

	long level = s2tt_test_helpers_min_block_lvl();
	unsigned long pa = 0UL; /* Valid for any level */
	unsigned long ap = 0UL; /* Valid on any level */
	struct s2tt_context s2tt_ctx;

	(void)memset(&s2tt_ctx, 0, sizeof(s2tt_ctx));

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 and s2tt_ctx.indirect_s2ap ar of use
	 * on this API, so the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
	s2tt_ctx.indirect_s2ap = s2tt_test_helpers_s2pie_enabled();

	test_helpers_expect_assert_fail(true);
	s2tt_init_assigned_ram((const struct s2tt_context *)&s2tt_ctx,
				NULL, pa, level, ap);
	test_helpers_fail_if_no_assert_failed();
}

void s2tt_init_assigned_ram_tc5(void)
{
	/***************************************************************
	 * TEST CASE 5:
	 *
	 * Invoke s2tt_init_assigned_ram() with an unaligned address.
	 ***************************************************************/

	unsigned long s2tt[S2TTES_PER_S2TT] = {0};
	long level =
		test_helpers_get_rand_in_range(s2tt_test_helpers_min_block_lvl(),
					       S2TT_TEST_HELPERS_MAX_LVL);
	unsigned long pa = s2tt_test_helpers_gen_addr(level, true) +
		test_helpers_get_rand_in_range(1UL, (unsigned long)GRANULE_SIZE - 1UL);
	unsigned long ap = 0UL; /* Valid on any level */
	struct s2tt_context s2tt_ctx;

	(void)memset(&s2tt_ctx, 0, sizeof(s2tt_ctx));

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 and s2tt_ctx.indirect_s2ap ar of use
	 * on this API, so the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
	s2tt_ctx.indirect_s2ap = s2tt_test_helpers_s2pie_enabled();

	test_helpers_expect_assert_fail(true);
	s2tt_init_assigned_ram((const struct s2tt_context *)&s2tt_ctx,
				&s2tt[0U], pa, level, ap);
	test_helpers_fail_if_no_assert_failed();
}

void s2tt_init_assigned_ram_tc6(void)
{
	/***************************************************************
	 * TEST CASE 6:
	 *
	 * Call s2tt_init_assigned_ram() with a NULL s2tt_context
	 * pointer.
	 ***************************************************************/

	unsigned long s2tt[S2TTES_PER_S2TT] = {0};
	long level = s2tt_test_helpers_min_block_lvl();
	unsigned long pa = 0UL; /* Valid for any level */
	unsigned long ap = 0UL; /* Valid on any level */

	test_helpers_expect_assert_fail(true);
	s2tt_init_assigned_ram((const struct s2tt_context *)NULL,
				&s2tt[0U], pa, level, ap);
	test_helpers_fail_if_no_assert_failed();
}

void s2tt_init_assigned_ns_tc1(void)
{
	/***************************************************************
	 * TEST CASE 1:
	 *
	 * For each valid level, initialize a table with assigned-ns
	 * S2TTEs and validate its contents.
	 ***************************************************************/

	struct s2tt_context s2tt_ctx;

	(void)memset(&s2tt_ctx, 0, sizeof(s2tt_ctx));

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 and s2tt_ctx.indirect_s2ap ar of use
	 * on this API, so the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
	s2tt_ctx.indirect_s2ap = s2tt_test_helpers_s2pie_enabled();

	for (long level = s2tt_test_helpers_min_block_lvl();
	     level <= S2TT_TEST_HELPERS_MAX_LVL; level++) {

		unsigned long s2tt[S2TTES_PER_S2TT] = { 0UL };
		unsigned long pa = s2tt_test_helpers_gen_addr(level - 1L, true);

		/*
		 * s2tt_init_assigned_ns() does not verify that the
		 * host-side attributes are architecturally valid.
		 * Nevertheless, pass a valid set of them.
		 */
		unsigned long attrs =
				s2tt_test_helpers_gen_ns_attrs(true, false);

		/*
		 * s2tt_init_assigned_ns() should mask out everything other
		 * than the host-side attributes, so generate a whole parent
		 * s2tte to pass to the former to verify it does what it is
		 * expected.
		 */
		unsigned long parent_s2tte = attrs |
			s2tt_test_helpers_gen_ns_attrs(false, false) |
			s2tt_test_helpers_pa_to_s2tte(
					s2tt_test_helpers_gen_addr(level, true),
					level);

		/*
		 * Generate the table. Note that s2tt_init_assigned_ns() can
		 * take a NULL struct s2tt_context pointer.
		 */
		s2tt_init_assigned_ns((const struct s2tt_context *)&s2tt_ctx,
				      &s2tt[0], parent_s2tte, pa, level, 0UL);

		/* Validate the content of the table */
		for (unsigned int i = 0U; i < S2TTES_PER_S2TT; i++) {
			unsigned long s2tte =
				s2tt_test_helpers_pa_to_s2tte(pa, level);

			s2tte =	s2tte_create_assigned_ns(
					(const struct s2tt_context *)&s2tt_ctx,
					s2tte | attrs, level, 0UL);
			pa += s2tte_map_size(level);

			UNSIGNED_LONGS_EQUAL(s2tte, s2tt[i]);
		}
	}
}

void s2tt_init_assigned_ns_tc2(void)
{
	/***************************************************************
	 * TEST CASE 2:
	 *
	 * For a valid address, try to create an assigned-ns S2TT
	 * with a level above the maximum.
	 *
	 * Note that s2tt_init_assigned_ns() can take a NULL
	 * struct s2tt_context pointer.
	 ***************************************************************/

	unsigned long s2tt[S2TTES_PER_S2TT] = {0};
	long level = S2TT_TEST_HELPERS_MAX_LVL + 1L;
	unsigned long pa = 0UL; /* Valid for any level */
	unsigned long ap = 0UL; /* Valid on any level */
	unsigned long attrs = s2tt_test_helpers_gen_ns_attrs(true, false);

	test_helpers_expect_assert_fail(true);
	s2tt_init_assigned_ns((const struct s2tt_context *)NULL,
			      &s2tt[0U], attrs, pa, level, ap);
	test_helpers_fail_if_no_assert_failed();
}

void s2tt_init_assigned_ns_tc3(void)
{
	/***************************************************************
	 * TEST CASE 3:
	 *
	 * For a valid address, try to create an assigned-ns S2TT
	 * with a level below the minimum.
	 *
	 * Note that s2tt_init_assigned_ns() can take a NULL
	 * struct s2tt_context pointer.
	 ***************************************************************/

	unsigned long s2tt[S2TTES_PER_S2TT] = {0};
	long level = s2tt_test_helpers_min_block_lvl() - 1L;
	unsigned long pa = 0UL; /* Valid for any level */
	unsigned long ap = 0UL; /* Valid on any level */
	unsigned long attrs = s2tt_test_helpers_gen_ns_attrs(true, false);

	test_helpers_expect_assert_fail(true);
	s2tt_init_assigned_ns((const struct s2tt_context *)NULL,
			      &s2tt[0U], attrs, pa, level, ap);
	test_helpers_fail_if_no_assert_failed();
}

void s2tt_init_assigned_ns_tc4(void)
{
	/***************************************************************
	 * TEST CASE 4:
	 *
	 * Invoke s2tt_init_assigned_ns() with a NULL table pointer.
	 *
	 * Note that s2tt_init_assigned_ns() can take a NULL
	 * struct s2tt_context_pointer.
	 ***************************************************************/

	long level = s2tt_test_helpers_min_block_lvl();
	unsigned long pa = 0UL; /* Valid for any level */
	unsigned long ap = 0UL; /* Valid on any level */
	unsigned long attrs = s2tt_test_helpers_gen_ns_attrs(true, false);

	test_helpers_expect_assert_fail(true);
	s2tt_init_assigned_ns((const struct s2tt_context *)NULL,
			      NULL, attrs, pa, level, ap);
	test_helpers_fail_if_no_assert_failed();
}

void s2tt_init_assigned_ns_tc5(void)
{
	/***************************************************************
	 * TEST CASE 5:
	 *
	 * Invoke s2tt_init_assigned_ns() with an unaligned address.
	 *
	 * Note that s2tt_init_assigned_ns() can take a NULL
	 * struct s2tt_context pointer.
	 ***************************************************************/

	unsigned long s2tt[S2TTES_PER_S2TT] = {0};
	unsigned long attrs = s2tt_test_helpers_gen_ns_attrs(true, false);
	long level =
		test_helpers_get_rand_in_range(s2tt_test_helpers_min_block_lvl(),
					       S2TT_TEST_HELPERS_MAX_LVL);
	unsigned long pa = s2tt_test_helpers_gen_addr(level, true) +
		test_helpers_get_rand_in_range(1UL, (unsigned long)GRANULE_SIZE - 1UL);
	unsigned long ap = 0UL; /* Valid on any level */

	test_helpers_expect_assert_fail(true);
	s2tt_init_assigned_ns((const struct s2tt_context *)NULL,
			      &s2tt[0U], attrs, pa, level, ap);
	test_helpers_fail_if_no_assert_failed();
}

void s2tt_init_assigned_destroyed_tc1(void)
{
	/***************************************************************
	 * TEST CASE 1:
	 *
	 * For each valid level, initialize a table with
	 * assigned-destroyed S2TTEs and validate its contents.
	 ***************************************************************/
	struct s2tt_context s2tt_ctx;

	(void)memset(&s2tt_ctx, 0, sizeof(s2tt_ctx));

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 and s2tt_ctx.indirect_s2ap ar of use
	 * on this API, so the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
	s2tt_ctx.indirect_s2ap = s2tt_test_helpers_s2pie_enabled();

	for (long level = s2tt_test_helpers_min_block_lvl();
	     level <= S2TT_TEST_HELPERS_MAX_LVL; level++) {

		unsigned long s2tt[S2TTES_PER_S2TT] = {0};
		unsigned long pa = s2tt_test_helpers_gen_addr(level - 1L, true);
		unsigned long ap = s2tt_test_generate_ap(false);

		/* Generate the table */
		s2tt_init_assigned_destroyed(
				(const struct s2tt_context *)&s2tt_ctx,
				&s2tt[0], pa, level, ap);

		/* Validate the content of the table */
		for (unsigned int i = 0U; i < S2TTES_PER_S2TT; i++) {
			unsigned long s2tte;

			s2tte =	s2tte_create_assigned_destroyed(
					(const struct s2tt_context *)&s2tt_ctx,
					pa, level, ap);
			pa += s2tte_map_size(level);

			UNSIGNED_LONGS_EQUAL(s2tte, s2tt[i]);
		}
	}
}

void s2tt_init_assigned_destroyed_tc2(void)
{
	/***************************************************************
	 * TEST CASE 2:
	 *
	 * For a valid address, try to create an assigned-destroyed
	 * S2TT with a level above the maximum.
	 ***************************************************************/

	unsigned long s2tt[S2TTES_PER_S2TT] = {0};
	long level = S2TT_TEST_HELPERS_MAX_LVL + 1L;
	unsigned long pa = 0UL; /* Valid for any level */
	unsigned long ap = 0UL; /* Valid on any level */
	struct s2tt_context s2tt_ctx;

	(void)memset(&s2tt_ctx, 0, sizeof(s2tt_ctx));

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 and s2tt_ctx.indirect_s2ap ar of use
	 * on this API, so the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
	s2tt_ctx.indirect_s2ap = s2tt_test_helpers_s2pie_enabled();

	test_helpers_expect_assert_fail(true);
	s2tt_init_assigned_destroyed((const struct s2tt_context *)&s2tt_ctx,
				     &s2tt[0U], pa, level, ap);
	test_helpers_fail_if_no_assert_failed();
}

void s2tt_init_assigned_destroyed_tc3(void)
{
	/***************************************************************
	 * TEST CASE 3:
	 *
	 * For a valid address, try to create an assigned-destroyed
	 * S2TT with a level below the minimum.
	 ***************************************************************/

	unsigned long s2tt[S2TTES_PER_S2TT] = {0};
	long level = s2tt_test_helpers_min_block_lvl() - 1L;
	unsigned long pa = 0UL; /* Valid for any level */
	unsigned long ap = 0UL; /* Valid on any level */
	struct s2tt_context s2tt_ctx;

	(void)memset(&s2tt_ctx, 0, sizeof(s2tt_ctx));

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 and s2tt_ctx.indirect_s2ap ar of use
	 * on this API, so the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
	s2tt_ctx.indirect_s2ap = s2tt_test_helpers_s2pie_enabled();

	test_helpers_expect_assert_fail(true);
	s2tt_init_assigned_destroyed((const struct s2tt_context *)&s2tt_ctx,
				     &s2tt[0U], pa, level, ap);
	test_helpers_fail_if_no_assert_failed();
}

void s2tt_init_assigned_destroyed_tc4(void)
{
	/***************************************************************
	 * TEST CASE 4:
	 *
	 * Invoke s2tt_init_assigned_destroyed() with a NULL table
	 * pointer.
	 ***************************************************************/

	long level = s2tt_test_helpers_min_block_lvl();
	unsigned long pa = 0UL; /* Valid for any level */
	unsigned long ap = 0UL; /* Valid on any level */
	struct s2tt_context s2tt_ctx;

	(void)memset(&s2tt_ctx, 0, sizeof(s2tt_ctx));

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 and s2tt_ctx.indirect_s2ap ar of use
	 * on this API, so the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
	s2tt_ctx.indirect_s2ap = s2tt_test_helpers_s2pie_enabled();

	test_helpers_expect_assert_fail(true);
	s2tt_init_assigned_destroyed((const struct s2tt_context *)&s2tt_ctx,
				     NULL, pa, level, ap);
	test_helpers_fail_if_no_assert_failed();
}

void s2tt_init_assigned_destroyed_tc5(void)
{
	/***************************************************************
	 * TEST CASE 5:
	 *
	 * Invoke s2tt_init_assigned_destroyed() with an unaligned
	 * address.
	 ***************************************************************/

	unsigned long s2tt[S2TTES_PER_S2TT] = {0};
	long level =
		test_helpers_get_rand_in_range(s2tt_test_helpers_min_block_lvl(),
					       S2TT_TEST_HELPERS_MAX_LVL);
	unsigned long pa = s2tt_test_helpers_gen_addr(level, true) +
		test_helpers_get_rand_in_range(1UL, (unsigned long)GRANULE_SIZE - 1UL);
	unsigned long ap = 0UL; /* Valid on any level */
	struct s2tt_context s2tt_ctx;

	(void)memset(&s2tt_ctx, 0, sizeof(s2tt_ctx));

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 and s2tt_ctx.indirect_s2ap ar of use
	 * on this API, so the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
	s2tt_ctx.indirect_s2ap = s2tt_test_helpers_s2pie_enabled();

	test_helpers_expect_assert_fail(true);
	s2tt_init_assigned_destroyed((const struct s2tt_context *)&s2tt_ctx,
				     &s2tt[0U], pa, level, ap);
	test_helpers_fail_if_no_assert_failed();
}

void s2tt_init_assigned_destroyed_tc6(void)
{
	/***************************************************************
	 * TEST CASE 6:
	 *
	 * Call s2tt_init_assigned_destroyed() with a NULL
	 * struct s2tt_context pointer.
	 ***************************************************************/

	unsigned long s2tt[S2TTES_PER_S2TT] = {0};
	long level = s2tt_test_helpers_min_block_lvl();
	unsigned long pa = 0UL; /* Valid for any level */
	unsigned long ap = 0UL; /* Valid on any level */

	test_helpers_expect_assert_fail(true);
	s2tt_init_assigned_destroyed((const struct s2tt_context *)NULL,
				     &s2tt[0U], pa, level, ap);
	test_helpers_fail_if_no_assert_failed();
}

void s2tte_pa_tc1(void)
{
	/***************************************************************
	 * TEST CASE 1:
	 *
	 * For each valid level, generate an assigned s2tte or table
	 * and verify that s2tte_pa() returns the right address
	 ***************************************************************/

	unsigned long ripas[] = {S2TTE_INVALID_RIPAS_EMPTY,
				 S2TTE_INVALID_RIPAS_RAM,
				 S2TTE_INVALID_RIPAS_DESTROYED};
	struct s2tt_context s2tt_ctx;

	(void)memset(&s2tt_ctx, 0, sizeof(s2tt_ctx));

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 and s2tt_ctx.indirect_s2ap ar of use
	 * on this API, so the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
	s2tt_ctx.indirect_s2ap = s2tt_test_helpers_s2pie_enabled();

	for (long level = s2tt_test_helpers_min_table_lvl();
	     level <= S2TT_TEST_HELPERS_MAX_LVL; level++) {
		unsigned long tte;
		unsigned long pa = s2tt_test_helpers_gen_addr(level, true);
		unsigned long ap = s2tt_test_generate_ap(false);

		if (level < s2tt_test_helpers_min_block_lvl()) {
			tte = s2tte_create_table(
					(const struct s2tt_context *)&s2tt_ctx,
					pa, level);
		} else {
			/*
			 * pickup a random type of assigned S2TTE
			 * to test with
			 */
			unsigned int idx =
				(unsigned int)test_helpers_get_rand_in_range(
					0UL, ARRAY_SIZE(ripas) - 1UL);

			tte = s2tt_test_create_assigned(
					(const struct s2tt_context *)&s2tt_ctx,
					pa, level, ripas[idx], ap);
		}

		/* Verify the address returned by s2tte_pa() */
		UNSIGNED_LONGS_EQUAL(pa, s2tte_pa(
					(const struct s2tt_context *)&s2tt_ctx,
					tte, level));
	}
}

void s2tte_pa_tc2(void)
{
	/***************************************************************
	 * TEST CASE 2:
	 *
	 * For a given level and unassigned s2tte (which doesn't have
	 * a PA), verify that s2tte_pa() behaves as expected.
	 ***************************************************************/

	unsigned long ripas[] = {S2TTE_INVALID_RIPAS_EMPTY,
				 S2TTE_INVALID_RIPAS_RAM,
				 S2TTE_INVALID_RIPAS_DESTROYED};
	long level = test_helpers_get_rand_in_range(
			s2tt_test_helpers_min_block_lvl(),
			S2TT_TEST_HELPERS_MAX_LVL);
	unsigned long ap = 0UL; /* Valid on any level */
	struct s2tt_context s2tt_ctx;

	(void)memset(&s2tt_ctx, 0, sizeof(s2tt_ctx));

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 and s2tt_ctx.indirect_s2ap ar of use
	 * on this API, so the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
	s2tt_ctx.indirect_s2ap = s2tt_test_helpers_s2pie_enabled();

	/* pickup a random type of unassigned S2TTE to test with */
	unsigned int idx = (unsigned int)test_helpers_get_rand_in_range(
					0UL, ARRAY_SIZE(ripas) - 1UL);
	unsigned long tte = s2tt_test_create_unassigned(
			(const struct s2tt_context *)&s2tt_ctx, ripas[idx], ap);

	test_helpers_expect_assert_fail(true);
	(void)s2tte_pa((const struct s2tt_context *)&s2tt_ctx, tte, level);
	test_helpers_fail_if_no_assert_failed();
}

void s2tte_pa_tc3(void)
{
	/***************************************************************
	 * TEST CASE 3:
	 *
	 * With a valid assigned S2TTE, call s2tte_pa() with a level
	 * above the maximum supported one.
	 **************************************************************/

	unsigned long ripas[] = {S2TTE_INVALID_RIPAS_EMPTY,
				 S2TTE_INVALID_RIPAS_RAM,
				 S2TTE_INVALID_RIPAS_DESTROYED};

	long level = S2TT_TEST_HELPERS_MAX_LVL;
	unsigned long pa = 0UL; /* Valid for any level */
	unsigned long ap = 0UL; /* Valid on any level */
	struct s2tt_context s2tt_ctx;

	(void)memset(&s2tt_ctx, 0, sizeof(s2tt_ctx));

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 and s2tt_ctx.indirect_s2ap ar of use
	 * on this API, so the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
	s2tt_ctx.indirect_s2ap = s2tt_test_helpers_s2pie_enabled();

	/* pickup a random type of assigned S2TTE to test with */
	unsigned int idx = (unsigned int)test_helpers_get_rand_in_range(
					0UL, ARRAY_SIZE(ripas) - 1UL);
	unsigned long tte = s2tt_test_create_assigned(
			(const struct s2tt_context *)&s2tt_ctx,
			pa, level, ripas[idx], ap);

	test_helpers_expect_assert_fail(true);
	(void)s2tte_pa((const struct s2tt_context *)&s2tt_ctx, tte, level + 1U);
	test_helpers_fail_if_no_assert_failed();
}

void s2tte_pa_tc4(void)
{
	/***************************************************************
	 * TEST CASE 4:
	 *
	 * With a valid assigned S2TTE, call s2tte_pa() with a level
	 * below the minimum supported one.
	 **************************************************************/

	unsigned long ripas[] = {S2TTE_INVALID_RIPAS_EMPTY,
				 S2TTE_INVALID_RIPAS_RAM,
				 S2TTE_INVALID_RIPAS_DESTROYED};

	long level = S2TT_TEST_HELPERS_MAX_LVL;
	unsigned long pa = 0UL; /* Valid for any level */
	unsigned long ap = 0UL; /* Valid on any level */
	struct s2tt_context s2tt_ctx;

	(void)memset(&s2tt_ctx, 0, sizeof(s2tt_ctx));

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 and s2tt_ctx.indirect_s2ap ar of use
	 * on this API, so the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
	s2tt_ctx.indirect_s2ap = s2tt_test_helpers_s2pie_enabled();

	/* pickup a random type of assigned S2TTE to test with */
	unsigned int idx = (unsigned int)test_helpers_get_rand_in_range(
					0UL, ARRAY_SIZE(ripas) - 1UL);
	unsigned long tte = s2tt_test_create_assigned(
			(const struct s2tt_context *)&s2tt_ctx,
			pa, level, ripas[idx], ap);

	test_helpers_expect_assert_fail(true);
	(void)s2tte_pa((const struct s2tt_context *)&s2tt_ctx,
			tte, s2tt_test_helpers_min_table_lvl() - 1L);
	test_helpers_fail_if_no_assert_failed();
}

void s2tte_pa_tc5(void)
{
	/***************************************************************
	 * TEST CASE 5:
	 *
	 * Call s2tte_pa() with a NULL s2tt_context pointer.
	 **************************************************************/

	unsigned long ripas[] = {S2TTE_INVALID_RIPAS_EMPTY,
				 S2TTE_INVALID_RIPAS_RAM,
				 S2TTE_INVALID_RIPAS_DESTROYED};

	long level = s2tt_test_helpers_min_block_lvl();
	unsigned long pa = 0UL; /* Valid for any level */
	unsigned long ap = 0UL; /* Valid on any level */
	struct s2tt_context s2tt_ctx;

	(void)memset(&s2tt_ctx, 0, sizeof(s2tt_ctx));

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 and s2tt_ctx.indirect_s2ap ar of use
	 * on this API, so the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
	s2tt_ctx.indirect_s2ap = s2tt_test_helpers_s2pie_enabled();

	/* pickup a random type of assigned S2TTE to test with */
	unsigned int idx = (unsigned int)test_helpers_get_rand_in_range(
					0UL, ARRAY_SIZE(ripas) - 1UL);
	unsigned long tte = s2tt_test_create_assigned(
			(const struct s2tt_context *)&s2tt_ctx,
			pa, level, ripas[idx], ap);

	test_helpers_expect_assert_fail(true);
	(void)s2tte_pa((const struct s2tt_context *)NULL,
			tte, s2tt_test_helpers_min_table_lvl() - 1L);
	test_helpers_fail_if_no_assert_failed();
}
