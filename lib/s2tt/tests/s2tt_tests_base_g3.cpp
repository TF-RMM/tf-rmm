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
#include <test_helpers.h>
#include <unistd.h>
#include <utils_def.h>
}

void s2tte_create_assigned_dev_destroyed_tc1(void)
{
	/*******************************************************************
	 * TEST CASE 1:
	 *
	 * Create an assigned_dev destroyed S2TTE with valid parameters and
	 * verify that the S2TTE is valid.
	 ******************************************************************/

	/* Test for each possible level */
	for (long i = s2tt_test_helpers_min_dev_block_lvl();
	     i <= S2TT_TEST_HELPERS_MAX_LVL; i++) {

		unsigned long pa = s2tt_test_helpers_gen_addr(i, true);
		unsigned long ap = test_helpers_get_rand_in_range(0UL, ULONG_MAX);
		unsigned long tte, tte_mask;
		s2tt_context s2tt_ctx;

		(void)memset(&s2tt_ctx, 0, sizeof(s2tt_ctx));

		/*
		 * Generate an s2tt context to be used for the test.
		 * only s2tt_ctx.enable_lpa2 and s2tt_ctx.indirect_s2ap ar of use
		 * on this API, so the rest of them can be uninitialized.
		 */
		s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
		s2tt_ctx.indirect_s2ap = s2tt_test_helpers_s2pie_enabled();

		tte = s2tte_create_assigned_dev_destroyed((const struct s2tt_context *)&s2tt_ctx,
							  pa, i, ap);

		/* Validate the address */
		UNSIGNED_LONGS_EQUAL(
				s2tt_test_helpers_s2tte_to_pa(tte, i), pa);

		/* Validate the RIPAS */
		UNSIGNED_LONGS_EQUAL((tte & S2TTE_INVALID_RIPAS_MASK),
					     S2TTE_INVALID_RIPAS_DESTROYED);

		/* Validate the HIPAS */
		UNSIGNED_LONGS_EQUAL((tte & S2TTE_INVALID_HIPAS_MASK),
						S2TTE_INVALID_HIPAS_ASSIGNED_DEV);

		/* Validate the Access Permissions */
		if (s2tt_ctx.indirect_s2ap) {
			UNSIGNED_LONGS_EQUAL(s2tte_get_pi_index(&s2tt_ctx, tte),
					     S2TTE_DEV_DEF_BASE_PERM_IDX);
			UNSIGNED_LONGS_EQUAL((ap & MASK(S2TTE_PO_INDEX)),
					     (tte & MASK(S2TTE_PO_INDEX)));
		} else {
			UNSIGNED_LONGS_EQUAL((ap & S2TTE_RW_AP_MASK), (tte & S2TTE_RW_AP_MASK));
			UNSIGNED_LONGS_EQUAL(S2TTE_PERM_XNU_XNP, (tte & MASK(S2TTE_PERM_XN)));
		}

		/* The rest of the fields must be all 0 */
		tte_mask = s2tt_test_helpers_s2tte_oa_mask() |
				S2TTE_INVALID_RIPAS_MASK |
				S2TTE_INVALID_HIPAS_MASK;
		tte_mask |= s2tt_ctx.indirect_s2ap ?
		       (S2TTE_PI_INDEX_MASK | MASK(S2TTE_PO_INDEX) | S2TTE_DIRTY_BIT) :
		       s2tt_test_generate_ap_mask();

		UNSIGNED_LONGS_EQUAL((tte & ~tte_mask), 0UL);
	}
}

void s2tte_create_assigned_dev_destroyed_tc2(void)
{
	/*******************************************************************
	 * TEST CASE 2:
	 *
	 * For a valid level, try to create an assigned_dev destroyed S2TTE
	 * with an unaligned address.
	 ******************************************************************/

	long level = (long)test_helpers_get_rand_in_range(
			(unsigned long)s2tt_test_helpers_min_dev_block_lvl(),
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
	(void)s2tte_create_assigned_dev_destroyed((const struct s2tt_context *)&s2tt_ctx,
						  pa, level, ap);
	test_helpers_fail_if_no_assert_failed();
}

void s2tte_create_assigned_dev_destroyed_tc3(void)
{
	/***************************************************************
	 * TEST CASE 3:
	 *
	 * For a valid address, try to create an assigned_dev destroyed
	 * S2TTE with a level below the minimum.
	 ***************************************************************/

	long level = s2tt_test_helpers_min_dev_block_lvl() - 1L;
	unsigned long pa = 0UL; /* Valid for any level */
	unsigned long ap = test_helpers_get_rand_in_range(0UL, ULONG_MAX);
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
	(void)s2tte_create_assigned_dev_destroyed((const struct s2tt_context *)&s2tt_ctx,
						  pa, level, ap);
	test_helpers_fail_if_no_assert_failed();
}

void s2tte_create_assigned_dev_destroyed_tc4(void)
{
	/***************************************************************
	 * TEST CASE 4:
	 *
	 * For a valid address, try to create an assigned-destroyed
	 * S2TTE with a level above the maximum.
	 ***************************************************************/

	long level = S2TT_TEST_HELPERS_MAX_LVL + 1;
	unsigned long pa = 0UL; /* Valid for any level */
	unsigned long ap = test_helpers_get_rand_in_range(0UL, ULONG_MAX);
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
	(void)s2tte_create_assigned_dev_destroyed((const struct s2tt_context *)&s2tt_ctx,
						  pa, level, ap);
	test_helpers_fail_if_no_assert_failed();
}

void s2tte_create_assigned_dev_destroyed_tc5(void)
{
	/***************************************************************
	 * TEST CASE 5:
	 *
	 * For a valid address, try to create an assigned_dev destroyed
	 * S2TTE with a null s2tt_context structure.
	 ***************************************************************/

	long level = S2TT_TEST_HELPERS_MAX_LVL;
	unsigned long pa = 0UL; /* Valid for any level */
	unsigned long ap = test_helpers_get_rand_in_range(0UL, ULONG_MAX);

	test_helpers_expect_assert_fail(true);
	(void)s2tte_create_assigned_dev_destroyed((const struct s2tt_context *)NULL,
						  pa, level, ap);
	test_helpers_fail_if_no_assert_failed();
}

void s2tte_create_assigned_dev_empty_tc1(void)
{
	/***************************************************************
	 * TEST CASE 1:
	 *
	 * Create an assigned_dev empty S2TTE with valid parameters and
	 * verify that the S2TTE is valid.
	 ***************************************************************/

	/* Test for each possible level */
	for (long i = s2tt_test_helpers_min_dev_block_lvl();
	     i <= S2TT_TEST_HELPERS_MAX_LVL; i++) {

		unsigned long pa = s2tt_test_helpers_gen_addr(i, true);
		unsigned long ap = test_helpers_get_rand_in_range(0UL, ULONG_MAX);
		unsigned long tte, tte_mask;
		s2tt_context s2tt_ctx;

		(void)memset(&s2tt_ctx, 0, sizeof(s2tt_ctx));

		/*
		 * Generate an s2tt context to be used for the test.
		 * only s2tt_ctx.enable_lpa2 and s2tt_ctx.indirect_s2ap are of use
		 * on this API, so the rest of them can be uninitialized.
		 */
		s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
		s2tt_ctx.indirect_s2ap = s2tt_test_helpers_s2pie_enabled();

		tte = s2tte_create_assigned_dev_empty((const struct s2tt_context *)&s2tt_ctx,
							pa, i, ap);

		/* Validate the address */
		UNSIGNED_LONGS_EQUAL(
				s2tt_test_helpers_s2tte_to_pa(tte, i), pa);

		/* Validate the RIPAS */
		UNSIGNED_LONGS_EQUAL((tte & S2TTE_INVALID_RIPAS_MASK),
					     S2TTE_INVALID_RIPAS_EMPTY);

		/* Validate the HIPAS */
		UNSIGNED_LONGS_EQUAL((tte & S2TTE_INVALID_HIPAS_MASK),
						S2TTE_INVALID_HIPAS_ASSIGNED_DEV);

		/* Validate the Access Permissions */
		if (s2tt_ctx.indirect_s2ap) {
			UNSIGNED_LONGS_EQUAL(s2tte_get_pi_index(&s2tt_ctx, tte),
					     S2TTE_DEV_DEF_BASE_PERM_IDX);
			UNSIGNED_LONGS_EQUAL((ap & MASK(S2TTE_PO_INDEX)),
					     (tte & MASK(S2TTE_PO_INDEX)));
		} else {
			UNSIGNED_LONGS_EQUAL((ap & S2TTE_RW_AP_MASK), (tte & S2TTE_RW_AP_MASK));
			UNSIGNED_LONGS_EQUAL(S2TTE_PERM_XNU_XNP, (tte & MASK(S2TTE_PERM_XN)));
		}

		/* The rest of the fields must be all 0 */
		tte_mask = s2tt_test_helpers_s2tte_oa_mask() |
				S2TTE_INVALID_RIPAS_MASK |
				S2TTE_INVALID_HIPAS_MASK;
		tte_mask |= s2tt_ctx.indirect_s2ap ?
		       (S2TTE_PI_INDEX_MASK | MASK(S2TTE_PO_INDEX) | S2TTE_DIRTY_BIT) :
			s2tt_test_generate_ap_mask();

		UNSIGNED_LONGS_EQUAL(0UL, (tte & ~tte_mask));
	}
}

void s2tte_create_assigned_dev_empty_tc2(void)
{
	/***************************************************************
	 * TEST CASE 2:
	 *
	 * For a valid level, try to create an assigned_dev empty S2TTE
	 * with an unaligned address.
	 ***************************************************************/

	long level = (long)test_helpers_get_rand_in_range(
			(unsigned long)s2tt_test_helpers_min_dev_block_lvl(),
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
	(void)s2tte_create_assigned_dev_empty((const struct s2tt_context *)&s2tt_ctx,
						pa, level, ap);
	test_helpers_fail_if_no_assert_failed();
}

void s2tte_create_assigned_dev_empty_tc3(void)
{
	/***************************************************************
	 * TEST CASE 3:
	 *
	 * For a valid address, try to create an assigned_dev empty
	 * S2TTE with a level below the minimum.
	 ***************************************************************/

	long level = s2tt_test_helpers_min_dev_block_lvl() - 1L;
	unsigned long pa = 0UL; /* Valid for any level */
	unsigned long ap = test_helpers_get_rand_in_range(0UL, ULONG_MAX);
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
	(void)s2tte_create_assigned_dev_empty((const struct s2tt_context *)&s2tt_ctx,
						pa, level, ap);
	test_helpers_fail_if_no_assert_failed();
}

void s2tte_create_assigned_dev_empty_tc4(void)
{
	/***************************************************************
	 * TEST CASE 4:
	 *
	 * For a valid address, try to create an assigned_dev empty
	 * S2TTE with a level above the maximum.
	 ***************************************************************/

	long level = S2TT_TEST_HELPERS_MAX_LVL + 1;
	unsigned long pa = 0UL; /* Valid for any level */
	unsigned long ap = test_helpers_get_rand_in_range(0UL, ULONG_MAX);
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
	(void)s2tte_create_assigned_dev_empty((const struct s2tt_context *)&s2tt_ctx,
						pa, level, ap);
	test_helpers_fail_if_no_assert_failed();
}

void s2tte_create_assigned_dev_empty_tc5(void)
{
	/***************************************************************
	 * TEST CASE 5:
	 *
	 * For a valid address, try to create an assigned_dev empty
	 * S2TTE with a null s2tt_context structure.
	 ***************************************************************/

	long level = S2TT_TEST_HELPERS_MAX_LVL;
	unsigned long pa = 0UL; /* Valid for any level */
	unsigned long ap = test_helpers_get_rand_in_range(0UL, ULONG_MAX);

	test_helpers_expect_assert_fail(true);
	(void)s2tte_create_assigned_dev_empty((const struct s2tt_context *)NULL,
						pa, level, ap);
	test_helpers_fail_if_no_assert_failed();
}

void s2tte_create_assigned_dev_unchanged_tc1(void)
{
	/***************************************************************
	 * TEST CASE 1:
	 *
	 * For each possible level and RIPAS_EMPTY and RIPAS_DESTROYED,
	 * invoke create_assigned_dev_unchanged() and verify that the TTE is
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

	for (long level = s2tt_test_helpers_min_dev_block_lvl();
	     level <= S2TT_TEST_HELPERS_MAX_LVL;
	     level++) {
		for (unsigned long ripas = RIPAS_EMPTY;
		     ripas < S2TT_TEST_RIPAS_INVALID;
		     ripas++) {
			unsigned long pa = s2tt_test_helpers_gen_addr(level, true);
			unsigned long ap = s2tt_test_generate_ap(true);
			unsigned long tte;

			/* Skip RIPAS_RAM */
			if (ripas != RIPAS_RAM) {
				tte = s2tte_create_assigned_dev_unchanged(
						(const struct s2tt_context *)&s2tt_ctx,
						INPLACE(S2TTE_INVALID_RIPAS, ripas) | ap,
						pa, level);

				/* Validate the address */
				UNSIGNED_LONGS_EQUAL(pa,
					s2tt_test_helpers_s2tte_to_pa(tte, level));

				/* Verify the RIPAS */
				UNSIGNED_LONGS_EQUAL(
					(tte & S2TTE_INVALID_RIPAS_MASK),
						INPLACE(S2TTE_INVALID_RIPAS,
							ripas));

				/* Verify the HIPAS */
				UNSIGNED_LONGS_EQUAL(
					(tte & S2TTE_INVALID_HIPAS_MASK),
						S2TTE_INVALID_HIPAS_ASSIGNED_DEV);

				/* Validate the Access Permissions */
				UNSIGNED_LONGS_EQUAL(
					ap, (tte & s2tt_test_generate_ap_mask()));

				/* The Descriptor type must be invalid */
				UNSIGNED_LONGS_EQUAL(
					(tte & S2TT_TEST_DESC_TYPE_MASK),
						S2TT_TEST_INVALID_DESC);
			}
		}
	}
}

void s2tte_create_assigned_dev_unchanged_tc2(void)
{
	/***************************************************************
	 * TEST CASE 2:
	 *
	 * For a valid level and ripas try to create an
	 * assigned_dev unchanged S2TTE with an unaligned address.
	 ***************************************************************/

	long level = (long)test_helpers_get_rand_in_range(
			(unsigned long)s2tt_test_helpers_min_dev_block_lvl(),
			(unsigned long)S2TT_TEST_HELPERS_MAX_LVL);
	unsigned long ripas = test_helpers_get_rand_in_range(
					RIPAS_EMPTY,
					RIPAS_DESTROYED);
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
	(void)s2tte_create_assigned_dev_unchanged((const struct s2tt_context *)&s2tt_ctx,
							ripas, pa, level);
	test_helpers_fail_if_no_assert_failed();
}

void s2tte_create_assigned_dev_unchanged_tc3(void)
{
	/***************************************************************
	 * TEST CASE 3:
	 *
	 * For a valid address and ripas try to create an
	 * assigned_dev unchanged S2TTE with a level below the minimum.
	 ***************************************************************/

	long level = s2tt_test_helpers_min_dev_block_lvl() - 1L;
	unsigned long ripas = test_helpers_get_rand_in_range(
					RIPAS_EMPTY,
					RIPAS_DESTROYED);
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
	(void)s2tte_create_assigned_dev_unchanged((const struct s2tt_context *)&s2tt_ctx,
							ripas, pa, level);
	test_helpers_fail_if_no_assert_failed();
}

void s2tte_create_assigned_dev_unchanged_tc4(void)
{
	/***************************************************************
	 * TEST CASE 4:
	 *
	 * For a valid address and ripas, try to create an
	 * assigned_dev unchanged S2TTE with a level above the maximum.
	 ***************************************************************/

	long level = S2TT_TEST_HELPERS_MAX_LVL + 1L;
	unsigned long ripas = test_helpers_get_rand_in_range(
					RIPAS_EMPTY,
					RIPAS_DESTROYED);
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
	(void)s2tte_create_assigned_dev_unchanged((const struct s2tt_context *)&s2tt_ctx,
							ripas, pa, level);
	test_helpers_fail_if_no_assert_failed();
}

void s2tte_create_assigned_dev_unchanged_tc5(void)
{
	/***************************************************************
	 * TEST CASE 5:
	 *
	 * For a valid level and pa try to create an
	 * assigned_dev unchanged S2TTE with an invalid RIPAS.
	 ***************************************************************/

	long level = (long)test_helpers_get_rand_in_range(
			(unsigned long)s2tt_test_helpers_min_dev_block_lvl(),
			(unsigned long)S2TT_TEST_HELPERS_MAX_LVL);
	unsigned long ripas = INPLACE(S2TTE_INVALID_RIPAS,
						S2TT_TEST_RIPAS_INVALID);
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
	(void)s2tte_create_assigned_dev_unchanged((const struct s2tt_context *)&s2tt_ctx,
							ripas, pa, level);
	test_helpers_fail_if_no_assert_failed();
}

void s2tte_create_assigned_dev_unchanged_tc6(void)
{
	/***************************************************************
	 * TEST CASE 6:
	 *
	 * For a valid level, pa and RIPAS, try to create an
	 * assigned_dev unchanged S2TTE with a null s2tt_context structure.
	 ***************************************************************/

	long level = (long)test_helpers_get_rand_in_range(
			(unsigned long)s2tt_test_helpers_min_dev_block_lvl(),
			(unsigned long)S2TT_TEST_HELPERS_MAX_LVL);
	unsigned long ripas = test_helpers_get_rand_in_range(
					RIPAS_EMPTY,
					RIPAS_DESTROYED);
	unsigned long pa = 0UL; /* Valid for any level */

	test_helpers_expect_assert_fail(true);
	(void)s2tte_create_assigned_dev_unchanged((const struct s2tt_context *)NULL,
							ripas, pa, level);
	test_helpers_fail_if_no_assert_failed();
}

void s2tte_create_assigned_dev_unchanged_tc7(void)
{
	/***************************************************************
	 * TEST CASE 7:
	 *
	 * For maximum possible level and RIPAS_RAM, invoke
	 * create_assigned_dev_unchanged() and verify that the assertion
	 * fails.
	 ***************************************************************/

	struct s2tt_context s2tt_ctx;
	long level = S2TT_TEST_HELPERS_MAX_LVL;
	unsigned long pa = s2tt_test_helpers_gen_addr(level, true);

	(void)memset(&s2tt_ctx, 0, sizeof(s2tt_ctx));

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 and s2tt_ctx.indirect_s2ap ar of use
	 * on this API, so the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
	s2tt_ctx.indirect_s2ap = s2tt_test_helpers_s2pie_enabled();

	test_helpers_expect_assert_fail(true);
	(void)s2tte_create_assigned_dev_unchanged(
					(const struct s2tt_context *)&s2tt_ctx,
					INPLACE(S2TTE_INVALID_RIPAS, RIPAS_RAM),
					pa, level);
	test_helpers_fail_if_no_assert_failed();
}

void s2tte_create_assigned_dev_unchanged_tc8(void)
{
	/***************************************************************
	 * TEST CASE 8:
	 *
	 * For minimum possible level and RIPAS_RAM, invoke
	 * create_assigned_dev_unchanged() and verify that the assertion
	 * fails.
	 ***************************************************************/

	struct s2tt_context s2tt_ctx;
	long level = s2tt_test_helpers_min_dev_block_lvl();
	unsigned long pa = s2tt_test_helpers_gen_addr(level, true);

	(void)memset(&s2tt_ctx, 0, sizeof(s2tt_ctx));

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 and s2tt_ctx.indirect_s2ap ar of use
	 * on this API, so the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
	s2tt_ctx.indirect_s2ap = s2tt_test_helpers_s2pie_enabled();

	test_helpers_expect_assert_fail(true);
	(void)s2tte_create_assigned_dev_unchanged(
					(const struct s2tt_context *)&s2tt_ctx,
					INPLACE(S2TTE_INVALID_RIPAS, RIPAS_RAM),
					pa, level);
	test_helpers_fail_if_no_assert_failed();
}

void s2tte_has_ripas_dev_tc1(void)
{
	/***************************************************************
	 * TEST CASE 1:
	 *
	 * For each valid level at which a TTE can have RIPAS,
	 * generate a set of assigned_dev S2TTEs with RIPAS and
	 * validate the output of s2tte_has_ripas().
	 ***************************************************************/

	unsigned long ripas[] = {S2TTE_INVALID_RIPAS_EMPTY,
				 S2TTE_INVALID_RIPAS_DESTROYED,
				 S2TTE_INVALID_RIPAS_DEV};
	struct s2tt_context s2tt_ctx;

	(void)memset(&s2tt_ctx, 0, sizeof(s2tt_ctx));

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 and s2tt_ctx.indirect_s2ap ar of use
	 * on this API, so the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
	s2tt_ctx.indirect_s2ap = s2tt_test_helpers_s2pie_enabled();

	for (long level = s2tt_test_helpers_min_dev_block_lvl();
	     level <= S2TT_TEST_HELPERS_MAX_LVL; level++) {
		for (unsigned long i = 0UL; i < ARRAY_SIZE(ripas); i++) {
			unsigned long tte;
			unsigned long pa = s2tt_test_helpers_gen_addr(level, true);
			unsigned long ap = test_helpers_get_rand_in_range(0UL, ULONG_MAX);

			/* Validate with an assigned_dev_dev S2TTE */
			tte = s2tt_test_create_assigned_dev(
					(const struct s2tt_context *)&s2tt_ctx,
					pa, level, ripas[i], ap);
			CHECK_TRUE(s2tte_has_ripas((const struct s2tt_context *)&s2tt_ctx,
						   tte, level) == true);
		}
	}
}

void s2tte_has_ripas_dev_tc2(void)
{
	/***************************************************************
	 * TEST CASE 2:
	 *
	 * For each valid level and all RmmDevMemCoherent types generate
	 * a set of assigned_dev_dev S2TTEs and validate the output of
	 * s2tte_has_ripas().
	 ***************************************************************/

	enum dev_coh_type type[] = {DEV_MEM_COHERENT,
				    DEV_MEM_NON_COHERENT};
	struct s2tt_context s2tt_ctx;

	(void)memset(&s2tt_ctx, 0, sizeof(s2tt_ctx));

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 and s2tt_ctx.indirect_s2ap ar of use
	 * on this API, so the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
	s2tt_ctx.indirect_s2ap = s2tt_test_helpers_s2pie_enabled();

	for (long level = s2tt_test_helpers_min_dev_block_lvl();
	     level <= S2TT_TEST_HELPERS_MAX_LVL; level++) {
		for (unsigned long i = 0UL; i < ARRAY_SIZE(type); i++) {
			unsigned long tte;
			unsigned long pa = s2tt_test_helpers_gen_addr(level, true);
			unsigned long ap = test_helpers_get_rand_in_range(0UL, ULONG_MAX);

			/* Validate with an assigned_dev_dev S2TTE */
			tte = s2tte_create_assigned_dev_dev_coh_type(
					(const struct s2tt_context *)&s2tt_ctx,
					pa, level, type[i], ap);
			CHECK_TRUE(s2tte_has_ripas((const struct s2tt_context *)&s2tt_ctx,
						   tte, level) == true);
		}
	}
}

void s2tte_is_assigned_dev_empty_tc1(void)
{
	/*****************************************************************
	 * TEST CASE 1:
	 *
	 * This test case cover positive tests for is_assigned_dev_empty()
	 * as well as a number of negative tests for each valid level.
	 *****************************************************************/

	unsigned long ripas[] = {S2TTE_INVALID_RIPAS_DESTROYED,
				 S2TTE_INVALID_RIPAS_DEV};
	struct s2tt_context s2tt_ctx;

	(void)memset(&s2tt_ctx, 0, sizeof(s2tt_ctx));

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 and s2tt_ctx.indirect_s2ap ar of use
	 * on this API, so the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
	s2tt_ctx.indirect_s2ap = s2tt_test_helpers_s2pie_enabled();

	for (long level = s2tt_test_helpers_min_dev_block_lvl();
	     level <= S2TT_TEST_HELPERS_MAX_LVL; level++) {
		unsigned int idx;
		unsigned long pa = s2tt_test_helpers_gen_addr(level, true);
		unsigned long ap = test_helpers_get_rand_in_range(0UL, ULONG_MAX);
		unsigned long inv_tte, tte =
			s2tte_create_assigned_dev_empty(
					(const struct s2tt_context *)&s2tt_ctx,
					pa, level, ap);

		/* Validate s2tt_is_assigned_dev_empty with an assigned_dev empty TTE */
		CHECK_TRUE(s2tte_is_assigned_dev_empty((const struct s2tt_context *)&s2tt_ctx,
							tte, level) == true);

		/* Negative test: Set DESC_TYPE to a valid descriptor */
		inv_tte = tte | S2TT_TEST_PAGE_DESC;

		CHECK_TRUE(s2tte_is_assigned_dev_empty((const struct s2tt_context *)&s2tt_ctx,
							inv_tte, level) == false);

		/* Negative test: Change the HIPAS to UNASSIGNED */
		inv_tte = tte & ~S2TTE_INVALID_HIPAS_MASK;
		inv_tte |= S2TTE_INVALID_HIPAS_UNASSIGNED;
		CHECK_TRUE(s2tte_is_assigned_dev_empty((const struct s2tt_context *)&s2tt_ctx,
							inv_tte, level) == false);

		/* Negative test: Test with a different type of assigned TTE */
		idx = (unsigned int)test_helpers_get_rand_in_range(
					0UL, ARRAY_SIZE(ripas) - 1UL);
		inv_tte = s2tt_test_create_assigned_dev((const struct s2tt_context *)&s2tt_ctx,
							pa, level, ripas[idx], ap);
		CHECK_TRUE(s2tte_is_assigned_dev_empty((const struct s2tt_context *)&s2tt_ctx,
							inv_tte, level) == false);
	}
}

void s2tte_is_assigned_dev_destroyed_tc1(void)
{
	/***************************************************************
	 * TEST CASE 1:
	 *
	 * This test case cover positive tests for
	 * is_assigned_dev_destroyed() as well as a number of negative
	 * tests for each valid level.
	 ***************************************************************/

	unsigned long ripas[] = {S2TTE_INVALID_RIPAS_EMPTY,
				 S2TTE_INVALID_RIPAS_DEV};
	struct s2tt_context s2tt_ctx;

	(void)memset(&s2tt_ctx, 0, sizeof(s2tt_ctx));

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 and s2tt_ctx.indirect_s2ap ar of use
	 * on this API, so the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
	s2tt_ctx.indirect_s2ap = s2tt_test_helpers_s2pie_enabled();

	for (long level = s2tt_test_helpers_min_dev_block_lvl();
	     level <= S2TT_TEST_HELPERS_MAX_LVL; level++) {
		unsigned int idx;
		unsigned long pa = s2tt_test_helpers_gen_addr(level, true);
		unsigned long ap = test_helpers_get_rand_in_range(0UL, ULONG_MAX);
		unsigned long inv_tte, tte;

		tte = s2tte_create_assigned_dev_destroyed(
						(const struct s2tt_context *)&s2tt_ctx,
						pa, level, ap);

		/*
		 * Validate s2tt_is_assigned_dev_destroyed with an assigned_dev
		 * destroyed TTE
		 */
		CHECK_TRUE(s2tte_is_assigned_dev_destroyed(
						(const struct s2tt_context *)&s2tt_ctx,
						tte, level) == true);

		/* Negative test: Set DESC_TYPE to a valid descriptor */
		inv_tte = tte | S2TT_TEST_PAGE_DESC;
		CHECK_TRUE(s2tte_is_assigned_dev_destroyed(
						(const struct s2tt_context *)&s2tt_ctx,
						inv_tte, level) == false);

		/* Negative test: Change the HIPAS to UNASSIGNED */
		inv_tte = tte & ~S2TTE_INVALID_HIPAS_MASK;
		inv_tte |= S2TTE_INVALID_HIPAS_UNASSIGNED;
		CHECK_TRUE(s2tte_is_assigned_dev_destroyed(
						(const struct s2tt_context *)&s2tt_ctx,
						inv_tte, level) == false);

		/* Negative test: Test with a different RIPAS */
		idx = (unsigned int)test_helpers_get_rand_in_range(
					0UL, ARRAY_SIZE(ripas) - 1UL);
		inv_tte = s2tt_test_create_assigned_dev(
						(const struct s2tt_context *)&s2tt_ctx,
						pa, level, ripas[idx], ap);
		CHECK_TRUE(s2tte_is_assigned_dev_destroyed(
						(const struct s2tt_context *)&s2tt_ctx,
						inv_tte, level) == false);
	}
}

void s2tte_is_assigned_dev_dev_tc1(void)
{
	/***************************************************************
	 * TEST CASE 1:
	 *
	 * Calling s2tt_create_assigned_dev_dev() this test case covers
	 * positive tests for is_assigned_dev_dev() as well as a number
	 * of negative tests for each valid level.
	 ***************************************************************/

	unsigned long ripas[] = {S2TTE_INVALID_RIPAS_EMPTY,
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

	for (long level = s2tt_test_helpers_min_dev_block_lvl();
	     level <= S2TT_TEST_HELPERS_MAX_LVL; level++) {
		unsigned int idx;
		unsigned long pa = s2tt_test_helpers_gen_addr(level, true);
		unsigned long ap = test_helpers_get_rand_in_range(0UL, ULONG_MAX);
		unsigned long inv_tte, tte;

		tte = s2tt_test_create_assigned_dev_dev((const struct s2tt_context *)&s2tt_ctx,
							pa, level, ap);

		/* Validate s2tt_is_assigned_dev_dev with an assigned_dev TTE */
		CHECK_TRUE(s2tte_is_assigned_dev_dev((const struct s2tt_context *)&s2tt_ctx,
							tte, level) == true);
		/*
		 * Negative test: Test with UNASSIGNED-RAM
		 * We test with UNASSIGNED-RAM as in the current RMM implementation,
		 * an ASSIGNED-RAM S2TTE does not have HIPAS field, so we pick
		 * up an S2TTE with a HIPAS other than ASSIGNED.
		 */
		inv_tte = s2tte_create_unassigned_ram(
				(const struct s2tt_context *)&s2tt_ctx, ap);
		CHECK_TRUE(s2tte_is_assigned_dev_dev((const struct s2tt_context *)&s2tt_ctx,
							inv_tte, level) == false);

		/* Negative test: Test with a different type of RIPAS */
		idx = (unsigned int)test_helpers_get_rand_in_range(
					0UL, ARRAY_SIZE(ripas) - 1UL);
		inv_tte = s2tt_test_create_assigned((const struct s2tt_context *)&s2tt_ctx,
						pa, level, ripas[idx], ap);
		CHECK_TRUE(s2tte_is_assigned_dev_dev((const struct s2tt_context *)&s2tt_ctx,
							inv_tte, level) == false);
	}
}

void s2tte_is_assigned_dev_dev_tc2(void)
{
	/***************************************************************
	 * TEST CASE 2:
	 *
	 * Calling s2tte_create_assigned_dev_dev_coh_type() for all
	 * RmmDevMemCoherent types this test case covers positive tests
	 * for is_assigned_dev_dev() as well as a number of negative
	 * tests for each valid level.
	 ***************************************************************/

	unsigned long ripas[] = {S2TTE_INVALID_RIPAS_EMPTY,
				 S2TTE_INVALID_RIPAS_DESTROYED};
	enum dev_coh_type type[] = {DEV_MEM_COHERENT,
				    DEV_MEM_NON_COHERENT};
	struct s2tt_context s2tt_ctx;

	(void)memset(&s2tt_ctx, 0, sizeof(s2tt_ctx));

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 and s2tt_ctx.indirect_s2ap ar of use
	 * on this API, so the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
	s2tt_ctx.indirect_s2ap = s2tt_test_helpers_s2pie_enabled();

	for (long level = s2tt_test_helpers_min_dev_block_lvl();
	     level <= S2TT_TEST_HELPERS_MAX_LVL; level++) {
		for (unsigned long i = 0UL; i < ARRAY_SIZE(type); i++) {
			unsigned int idx;
			unsigned long pa = s2tt_test_helpers_gen_addr(level, true);
			unsigned long ap = test_helpers_get_rand_in_range(0UL, ULONG_MAX);
			unsigned long inv_tte, tte;

			tte = s2tte_create_assigned_dev_dev_coh_type(
						(const struct s2tt_context *)&s2tt_ctx,
						pa, level, type[i], ap);

			/* Validate s2tt_is_assigned_dev_dev with an assigned_dev TTE */
			CHECK_TRUE(s2tte_is_assigned_dev_dev(
						(const struct s2tt_context *)&s2tt_ctx,
						tte, level) == true);
			/*
			 * Negative test: Test with UNASSIGNED-RAM
			 * We test with UNASSIGNED-RAM as in the current RMM implementation,
			 * an ASSIGNED-RAM S2TTE does not have HIPAS field, so we pick
			 * up an S2TTE with a HIPAS other than ASSIGNED.
			 */
			inv_tte = s2tte_create_unassigned_ram(
						(const struct s2tt_context *)&s2tt_ctx, ap);
			CHECK_TRUE(s2tte_is_assigned_dev_dev(
						(const struct s2tt_context *)&s2tt_ctx,
						inv_tte, level) == false);

			/* Negative test: Test with a different type of RIPAS */
			idx = (unsigned int)test_helpers_get_rand_in_range(
						0UL, ARRAY_SIZE(ripas) - 1UL);
			inv_tte = s2tt_test_create_assigned(
							(const struct s2tt_context *)&s2tt_ctx,
							pa, level, ripas[idx], ap);
			CHECK_TRUE(s2tte_is_assigned_dev_dev(
							(const struct s2tt_context *)&s2tt_ctx,
							inv_tte, level) == false);
		}
	}
}

void s2tte_is_assigned_dev_dev_tc3(void)
{
	/***************************************************************
	 * TEST CASE 3:
	 *
	 * Calling s2tte_create_assigned_dev_dev() test
	 * s2tte_is_assigned_dev_dev() with invalid levels.
	 ***************************************************************/

	unsigned long pa = 0UL;
	unsigned long tte;
	long level = s2tt_test_helpers_min_dev_block_lvl();
	unsigned long ap = test_helpers_get_rand_in_range(0UL, ULONG_MAX);
	struct s2tt_context s2tt_ctx;

	(void)memset(&s2tt_ctx, 0, sizeof(s2tt_ctx));

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 and s2tt_ctx.indirect_s2ap ar of use
	 * on this API, so the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
	s2tt_ctx.indirect_s2ap = s2tt_test_helpers_s2pie_enabled();

	tte = s2tt_test_create_assigned_dev_dev((const struct s2tt_context *)&s2tt_ctx,
						pa, level, ap);

	/* Validate s2tt_is_assigned_dev_dev with an assigned_dev TTE */
	CHECK_FALSE(s2tte_is_assigned_dev_dev((const struct s2tt_context *)&s2tt_ctx,
						tte, level - 1L));
	CHECK_FALSE(s2tte_is_assigned_dev_dev((const struct s2tt_context *)&s2tt_ctx,
						tte, S2TT_TEST_HELPERS_MAX_LVL));
}

void s2tte_is_assigned_dev_dev_tc4(void)
{
	/***************************************************************
	 * TEST CASE 4:
	 *
	 * Calling s2tte_create_assigned_dev_dev_coh_type() for all
	 * RmmDevMemCoherent types test s2tte_is_assigned_dev_dev() with
	 * invalid levels.
	 ***************************************************************/

	enum dev_coh_type type[] = {DEV_MEM_COHERENT,
				    DEV_MEM_NON_COHERENT};
	unsigned long pa = 0UL;
	unsigned long ap = test_helpers_get_rand_in_range(0UL, ULONG_MAX);
	long level = s2tt_test_helpers_min_dev_block_lvl();
	struct s2tt_context s2tt_ctx;

	(void)memset(&s2tt_ctx, 0, sizeof(s2tt_ctx));

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 and s2tt_ctx.indirect_s2ap ar of use
	 * on this API, so the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
	s2tt_ctx.indirect_s2ap = s2tt_test_helpers_s2pie_enabled();

	for (unsigned long i = 0UL; i < ARRAY_SIZE(type); i++) {
		unsigned long tte = s2tte_create_assigned_dev_dev_coh_type(
					(const struct s2tt_context *)&s2tt_ctx,
					pa, level, type[i], ap);

		/* Validate s2tt_is_assigned_dev_dev with an assigned_dev TTE */
		CHECK_FALSE(s2tte_is_assigned_dev_dev(
					(const struct s2tt_context *)&s2tt_ctx,
					tte, level - 1L));
		CHECK_FALSE(s2tte_is_assigned_dev_dev(
					(const struct s2tt_context *)&s2tt_ctx,
					tte, S2TT_TEST_HELPERS_MAX_LVL));
	}
}

void s2tte_get_ripas_dev_tc1(void)
{
	/***************************************************************
	 * TEST CASE 1:
	 *
	 * For all possible RIPAS types, generate a HIPAS ASSIGNED and
	 * verify that s2tt_get_ripas() returns the right RIPAS
	 ***************************************************************/

	unsigned long tte, pa;
	unsigned long ripas[] = {S2TTE_INVALID_RIPAS_EMPTY,
				 S2TTE_INVALID_RIPAS_DESTROYED,
				 S2TTE_INVALID_RIPAS_DEV};
	struct s2tt_context s2tt_ctx;

	(void)memset(&s2tt_ctx, 0, sizeof(s2tt_ctx));

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 and s2tt_ctx.indirect_s2ap ar of use
	 * on this API, so the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
	s2tt_ctx.indirect_s2ap = s2tt_test_helpers_s2pie_enabled();

	for (unsigned long i = 0UL; i < ARRAY_SIZE(ripas); i++) {
		/* HIPAS = ASSIGNED */
		for (long level = s2tt_test_helpers_min_dev_block_lvl();
		     level <= S2TT_TEST_HELPERS_MAX_LVL; level++) {
			unsigned long ap = test_helpers_get_rand_in_range(0UL, ULONG_MAX);

			pa = s2tt_test_helpers_gen_addr(level, true);
			tte = s2tt_test_create_assigned_dev(
					(const struct s2tt_context *)&s2tt_ctx,
					pa, level, ripas[i], ap);
			UNSIGNED_LONGS_EQUAL(
				(unsigned int)s2tte_get_ripas(
					(const struct s2tt_context *)&s2tt_ctx, tte),
					EXTRACT(S2TTE_INVALID_RIPAS, ripas[i]));
		}
	}
}

void s2tte_get_ripas_dev_tc2(void)
{
	/***************************************************************
	 * TEST CASE 2:
	 *
	 * For each valid level and all RmmDevMemCoherent types generate
	 * assigned_dev_dev and verify that s2tt_get_ripas() returns the
	 * right RIPAS
	 ***************************************************************/

	enum dev_coh_type type[] = {DEV_MEM_COHERENT,
				    DEV_MEM_NON_COHERENT};
	unsigned long tte, pa;
	struct s2tt_context s2tt_ctx;

	(void)memset(&s2tt_ctx, 0, sizeof(s2tt_ctx));

	/*
	 * Generate an s2tt context to be used for the test.
	 * only s2tt_ctx.enable_lpa2 and s2tt_ctx.indirect_s2ap ar of use
	 * on this API, so the rest of them can be uninitialized.
	 */
	s2tt_ctx.enable_lpa2 = s2tt_test_helpers_lpa2_enabled();
	s2tt_ctx.indirect_s2ap = s2tt_test_helpers_s2pie_enabled();

	for (long level = s2tt_test_helpers_min_dev_block_lvl();
	     level <= S2TT_TEST_HELPERS_MAX_LVL; level++) {
		for (unsigned long i = 0U; i < ARRAY_SIZE(type); i++) {
			unsigned long ap = test_helpers_get_rand_in_range(0UL, ULONG_MAX);

			pa = s2tt_test_helpers_gen_addr(level, true);
			tte = s2tte_create_assigned_dev_dev_coh_type(
					(const struct s2tt_context *)&s2tt_ctx,
					pa, level, type[i], ap);
			UNSIGNED_LONGS_EQUAL(
				(unsigned int)s2tte_get_ripas(
					(const struct s2tt_context *)&s2tt_ctx, tte),
					EXTRACT(S2TTE_INVALID_RIPAS, S2TTE_INVALID_RIPAS_DEV));
		}
	}
}

void s2tt_init_assigned_dev_empty_tc1(void)
{
	/***************************************************************
	 * TEST CASE 1:
	 *
	 * For each valid level, initialize a table with assigned_dev
	 * empty S2TTEs and validate its contents.
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

	for (long level = s2tt_test_helpers_min_dev_block_lvl();
	     level <= S2TT_TEST_HELPERS_MAX_LVL; level++) {

		unsigned long s2tt[S2TTES_PER_S2TT] = {0};
		unsigned long pa = s2tt_test_helpers_gen_addr(level - 1L, true);
		unsigned long ap = test_helpers_get_rand_in_range(0UL, ULONG_MAX);

		/* Generate the table */
		s2tt_init_assigned_dev_empty(
					(const struct s2tt_context *)&s2tt_ctx,
					&s2tt[0], pa, level, ap);

		/* Validate the content of the table */
		for (unsigned int i = 0U; i < S2TTES_PER_S2TT; i++) {
			unsigned long s2tte;

			s2tte =	s2tte_create_assigned_dev_empty(
					(const struct s2tt_context *)&s2tt_ctx,
					pa, level, ap);
			pa += s2tte_map_size(level);

			UNSIGNED_LONGS_EQUAL(s2tte, s2tt[i]);
		}
	}
}

void s2tt_init_assigned_dev_empty_tc2(void)
{
	/***************************************************************
	 * TEST CASE 2:
	 *
	 * For a valid address, try to create an assigned_dev empty S2TT
	 * with a level above the maximum.
	 ***************************************************************/

	unsigned long s2tt[S2TTES_PER_S2TT] = {0};
	long level = S2TT_TEST_HELPERS_MAX_LVL + 1L;
	unsigned long pa = 0UL; /* Valid for any level */
	unsigned long ap = test_helpers_get_rand_in_range(0UL, ULONG_MAX);
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
	s2tt_init_assigned_dev_empty((const struct s2tt_context *)&s2tt_ctx,
					&s2tt[0U], pa, level, ap);
	test_helpers_fail_if_no_assert_failed();
}

void s2tt_init_assigned_dev_empty_tc3(void)
{
	/***************************************************************
	 * TEST CASE 3:
	 *
	 * For a valid address, try to create an assigned_dev empty S2TT
	 * with a level below the minimum.
	 ***************************************************************/

	unsigned long s2tt[S2TTES_PER_S2TT] = {0};
	long level = s2tt_test_helpers_min_dev_block_lvl() - 1L;
	unsigned long pa = 0UL; /* Valid for any level */
	unsigned long ap = test_helpers_get_rand_in_range(0UL, ULONG_MAX);
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
	s2tt_init_assigned_dev_empty((const struct s2tt_context *)&s2tt_ctx,
					&s2tt[0U], pa, level, ap);
	test_helpers_fail_if_no_assert_failed();
}

void s2tt_init_assigned_dev_empty_tc4(void)
{
	/******************************************************************
	 * TEST CASE 4:
	 *
	 * Invoke s2tt_init_assigned_dev_empty() with a NULL table pointer.
	 ******************************************************************/

	long level = s2tt_test_helpers_min_dev_block_lvl();
	unsigned long pa = 0UL; /* Valid for any level */
	unsigned long ap = test_helpers_get_rand_in_range(0UL, ULONG_MAX);
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
	s2tt_init_assigned_dev_empty((const struct s2tt_context *)&s2tt_ctx,
					NULL, pa, level, ap);
	test_helpers_fail_if_no_assert_failed();
}

void s2tt_init_assigned_dev_empty_tc5(void)
{
	/******************************************************************
	 * TEST CASE 5:
	 *
	 * Invoke s2tt_init_assigned_dev_empty() with an unaligned address.
	 ******************************************************************/

	unsigned long s2tt[S2TTES_PER_S2TT] = {0};
	long level =
		test_helpers_get_rand_in_range(s2tt_test_helpers_min_dev_block_lvl(),
					       S2TT_TEST_HELPERS_MAX_LVL);
	unsigned long pa = s2tt_test_helpers_gen_addr(level, true) +
		test_helpers_get_rand_in_range(1UL, (unsigned long)GRANULE_SIZE - 1UL);
	unsigned long ap = test_helpers_get_rand_in_range(0UL, ULONG_MAX);
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
	s2tt_init_assigned_dev_empty((const struct s2tt_context *)&s2tt_ctx,
					&s2tt[0U], pa, level, ap);
	test_helpers_fail_if_no_assert_failed();
}

void s2tt_init_assigned_dev_empty_tc6(void)
{
	/***************************************************************
	 * TEST CASE 6:
	 *
	 * Invoke s2tt_init_assigned_dev_empty() with a NULL s2tt_context
	 * structure.
	 ***************************************************************/
	unsigned long s2tt[S2TTES_PER_S2TT] = {0};
	long level = s2tt_test_helpers_min_dev_block_lvl();
	unsigned long pa = 0UL; /* Valid for any level */
	unsigned long ap = test_helpers_get_rand_in_range(0UL, ULONG_MAX);

	test_helpers_expect_assert_fail(true);
	s2tt_init_assigned_dev_empty((const struct s2tt_context *)NULL,
					&s2tt[0U], pa, level, ap);
	test_helpers_fail_if_no_assert_failed();
}

void s2tt_init_assigned_dev_destroyed_tc1(void)
{
	/***************************************************************
	 * TEST CASE 1:
	 *
	 * For each valid level, initialize a table with
	 * assigned_dev destroyed S2TTEs and validate its contents.
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

	for (long level = s2tt_test_helpers_min_dev_block_lvl();
	     level <= S2TT_TEST_HELPERS_MAX_LVL; level++) {

		unsigned long s2tt[S2TTES_PER_S2TT] = {0};
		unsigned long pa = s2tt_test_helpers_gen_addr(level - 1L, true);
		unsigned long ap = test_helpers_get_rand_in_range(0UL, ULONG_MAX);

		/* Generate the table */
		s2tt_init_assigned_dev_destroyed(
				(const struct s2tt_context *)&s2tt_ctx,
				&s2tt[0], pa, level, ap);

		/* Validate the content of the table */
		for (unsigned int i = 0U; i < S2TTES_PER_S2TT; i++) {
			unsigned long s2tte;

			s2tte =	s2tte_create_assigned_dev_destroyed(
					(const struct s2tt_context *)&s2tt_ctx,
					pa, level, ap);
			pa += s2tte_map_size(level);

			UNSIGNED_LONGS_EQUAL(s2tte, s2tt[i]);
		}
	}
}

void s2tt_init_assigned_dev_destroyed_tc2(void)
{
	/***************************************************************
	 * TEST CASE 2:
	 *
	 * For a valid address, try to create an assigned_dev destroyed
	 * S2TT with a level above the maximum.
	 ***************************************************************/

	unsigned long s2tt[S2TTES_PER_S2TT] = {0};
	long level = S2TT_TEST_HELPERS_MAX_LVL + 1L;
	unsigned long pa = 0UL; /* Valid for any level */
	unsigned long ap = test_helpers_get_rand_in_range(0UL, ULONG_MAX);
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
	s2tt_init_assigned_dev_destroyed((const struct s2tt_context *)&s2tt_ctx,
					 &s2tt[0], pa, level, ap);
	test_helpers_fail_if_no_assert_failed();
}

void s2tt_init_assigned_dev_destroyed_tc3(void)
{
	/***************************************************************
	 * TEST CASE 3:
	 *
	 * For a valid address, try to create an assigned_dev destroyed
	 * S2TT with a level below the minimum.
	 ***************************************************************/

	unsigned long s2tt[S2TTES_PER_S2TT] = {0};
	long level = s2tt_test_helpers_min_dev_block_lvl() - 1L;
	unsigned long pa = 0UL; /* Valid for any level */
	unsigned long ap = test_helpers_get_rand_in_range(0UL, ULONG_MAX);
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
	s2tt_init_assigned_dev_destroyed((const struct s2tt_context *)&s2tt_ctx,
					 &s2tt[0], pa, level, ap);
	test_helpers_fail_if_no_assert_failed();
}

void s2tt_init_assigned_dev_destroyed_tc4(void)
{
	/***************************************************************
	 * TEST CASE 4:
	 *
	 * Invoke s2tt_init_assigned_dev_destroyed() with a NULL table
	 * pointer.
	 ***************************************************************/

	long level = s2tt_test_helpers_min_dev_block_lvl();
	unsigned long pa = 0UL; /* Valid for any level */
	unsigned long ap = test_helpers_get_rand_in_range(0UL, ULONG_MAX);
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
	s2tt_init_assigned_dev_destroyed((const struct s2tt_context *)&s2tt_ctx,
					 NULL, pa, level, ap);
	test_helpers_fail_if_no_assert_failed();
}

void s2tt_init_assigned_dev_destroyed_tc5(void)
{
	/***************************************************************
	 * TEST CASE 5:
	 *
	 * Invoke s2tt_init_assigned_dev_destroyed() with an unaligned
	 * address.
	 ***************************************************************/

	unsigned long s2tt[S2TTES_PER_S2TT] = {0};
	long level =
		test_helpers_get_rand_in_range(s2tt_test_helpers_min_dev_block_lvl(),
					       S2TT_TEST_HELPERS_MAX_LVL);
	unsigned long pa = s2tt_test_helpers_gen_addr(level, true) +
		test_helpers_get_rand_in_range(1UL, (unsigned long)GRANULE_SIZE - 1UL);
	unsigned long ap = test_helpers_get_rand_in_range(0UL, ULONG_MAX);
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
	s2tt_init_assigned_dev_destroyed((const struct s2tt_context *)&s2tt_ctx,
					 &s2tt[0], pa, level, ap);
	test_helpers_fail_if_no_assert_failed();
}

void s2tt_init_assigned_dev_destroyed_tc6(void)
{
	/***************************************************************
	 * TEST CASE 6:
	 *
	 * Call s2tt_init_assigned_dev_destroyed() with a NULL struct
	 * s2tt_context pointer.
	 ***************************************************************/

	unsigned long s2tt[S2TTES_PER_S2TT] = {0};
	long level = s2tt_test_helpers_min_dev_block_lvl();
	unsigned long pa = 0UL; /* Valid for any level */
	unsigned long ap = test_helpers_get_rand_in_range(0UL, ULONG_MAX);

	test_helpers_expect_assert_fail(true);
	s2tt_init_assigned_dev_destroyed((const struct s2tt_context *)NULL,
					 &s2tt[0], pa, level, ap);
	test_helpers_fail_if_no_assert_failed();
}

void s2tt_init_assigned_dev_dev_tc1(void)
{
	/***************************************************************
	 * TEST CASE 1:
	 *
	 * For each valid level, initialize a table with
	 * assigned_dev dev S2TTEs and validate its contents.
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

	for (long level = s2tt_test_helpers_min_dev_block_lvl();
	     level <= S2TT_TEST_HELPERS_MAX_LVL; level++) {

		unsigned long s2tt[S2TTES_PER_S2TT] = {0};
		unsigned long pa = s2tt_test_helpers_gen_addr(level - 1L, true);
		unsigned long ap = test_helpers_get_rand_in_range(0UL, ULONG_MAX);

		/* Generate the table */
		s2tt_test_init_assigned_dev_dev(
				(const struct s2tt_context *)&s2tt_ctx,
				&s2tt[0], pa, level, ap);

		/* Validate the content of the table */
		for (unsigned int i = 0U; i < S2TTES_PER_S2TT; i++) {
			unsigned long s2tte;

			s2tte =	s2tt_test_create_assigned_dev_dev(
					(const struct s2tt_context *)&s2tt_ctx,
					pa, level, ap);
			pa += s2tte_map_size(level);

			UNSIGNED_LONGS_EQUAL(s2tte, s2tt[i]);
		}
	}
}

void s2tt_init_assigned_dev_dev_tc2(void)
{
	/***************************************************************
	 * TEST CASE 2:
	 *
	 * For a valid address, try to create an assigned_dev dev S2TT
	 * with a level above the maximum.
	 ***************************************************************/

	unsigned long s2tt[S2TTES_PER_S2TT] = {0};
	long level = S2TT_TEST_HELPERS_MAX_LVL + 1L;
	unsigned long pa = 0UL; /* Valid for any level */
	unsigned long ap = test_helpers_get_rand_in_range(0UL, ULONG_MAX);
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
	s2tt_test_init_assigned_dev_dev((const struct s2tt_context *)&s2tt_ctx,
					&s2tt[0], pa, level, ap);
	test_helpers_fail_if_no_assert_failed();
}

void s2tt_init_assigned_dev_dev_tc3(void)
{
	/***************************************************************
	 * TEST CASE 3:
	 *
	 * For a valid address, try to create an assigned_dev dev S2TT
	 * with a level below the minimum.
	 ***************************************************************/

	unsigned long s2tt[S2TTES_PER_S2TT] = {0};
	long level = s2tt_test_helpers_min_dev_block_lvl() - 1L;
	unsigned long pa = 0UL; /* Valid for any level */
	unsigned long ap = test_helpers_get_rand_in_range(0UL, ULONG_MAX);
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
	s2tt_test_init_assigned_dev_dev((const struct s2tt_context *)&s2tt_ctx,
					&s2tt[0], pa, level, ap);
	test_helpers_fail_if_no_assert_failed();
}

void s2tt_init_assigned_dev_dev_tc4(void)
{
	/***************************************************************
	 * TEST CASE 4:
	 *
	 * Invoke s2tt_init_assigned_dev_dev() with a NULL table
	 * pointer.
	 ***************************************************************/

	long level = s2tt_test_helpers_min_dev_block_lvl();
	unsigned long pa = 0UL; /* Valid for any level */
	unsigned long ap = test_helpers_get_rand_in_range(0UL, ULONG_MAX);
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
	s2tt_test_init_assigned_dev_dev((const struct s2tt_context *)&s2tt_ctx,
					NULL, pa, level, ap);
	test_helpers_fail_if_no_assert_failed();
}

void s2tt_init_assigned_dev_dev_tc5(void)
{
	/***************************************************************
	 * TEST CASE 5:
	 *
	 * Invoke s2tt_init_assigned_dev_dev() with an unaligned
	 * address.
	 ***************************************************************/

	unsigned long s2tt[S2TTES_PER_S2TT] = {0};
	long level =
		test_helpers_get_rand_in_range(s2tt_test_helpers_min_dev_block_lvl(),
					       S2TT_TEST_HELPERS_MAX_LVL);
	unsigned long pa = s2tt_test_helpers_gen_addr(level, true) +
		test_helpers_get_rand_in_range(1UL, (unsigned long)GRANULE_SIZE - 1UL);
	unsigned long ap = test_helpers_get_rand_in_range(0UL, ULONG_MAX);
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
	s2tt_test_init_assigned_dev_dev((const struct s2tt_context *)&s2tt_ctx,
					&s2tt[0], pa, level, ap);
	test_helpers_fail_if_no_assert_failed();
}

void s2tt_init_assigned_dev_dev_tc6(void)
{
	/***************************************************************
	 * TEST CASE 6:
	 *
	 * Call s2tt_init_assigned_dev_dev() with a NULL struct
	 * s2tt_context pointer.
	 ***************************************************************/

	unsigned long s2tt[S2TTES_PER_S2TT] = {0};
	long level = s2tt_test_helpers_min_dev_block_lvl();
	unsigned long pa = 0UL; /* Valid for any level */
	unsigned long ap = test_helpers_get_rand_in_range(0UL, ULONG_MAX);
	unsigned long attr = S2TTE_TEST_DEV_ATTRS;

	/* Add Shareability bits if FEAT_LPA2 is not enabled */
	if (!s2tt_test_helpers_lpa2_enabled()) {
		attr |= S2TTE_TEST_DEV_SH;
	}

	test_helpers_expect_assert_fail(true);
	s2tt_init_assigned_dev_dev((const struct s2tt_context *)NULL,
				   &s2tt[0], (attr | pa), pa, level, ap);
	test_helpers_fail_if_no_assert_failed();
}
