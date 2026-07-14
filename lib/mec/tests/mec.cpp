/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <CppUTest/CommandLineTestRunner.h>
#include <CppUTest/TestHarness.h>

extern "C"
{
#include <arch_features.h>
#include <arch_helpers.h>
#include <host_utils.h>
#include <mec.h> /* Interface to exercise */
#include <mec_test_helpers.h>
#include <test_helpers.h>
}

TEST_GROUP(mec)
{
	TEST_SETUP()
	{
		mec_test_setup();
	}

	TEST_TEARDOWN()
	{
		mec_test_teardown();
	}
};

TEST(mec, mec_realm_mecid_s1_init_TC1)
{
	unsigned int mecid;
	unsigned long mecid_a1_el2_init, mecid_a1_el2_reset;

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Allocate a private MECID, initialize the Realm MECID for Stage 1,
	 * and verify the value written to MECID_A1_EL2 matches the allocated
	 * MECID. After reset, verify MECID_A1_EL2 returns to RESERVED_MECID_SYSTEM.
	 ******************************************************************/

	CHECK_TRUE(mecid_alloc(&mecid, false));

	mec_realm_mecid_s1_init(mecid);
	mecid_a1_el2_init = read_mecid_a1_el2();

	mec_realm_mecid_s1_reset();
	mecid_a1_el2_reset = read_mecid_a1_el2();

	mecid_free(mecid);

	CHECK_EQUAL(mecid, (unsigned int)mecid_a1_el2_init);
	CHECK_EQUAL(RESERVED_MECID_SYSTEM, (unsigned int)mecid_a1_el2_reset);
}

TEST(mec, mec_realm_mecid_s1_init_TC2)
{
	unsigned int mecid;
	unsigned long mecid_a1_el2_init;
	unsigned long mecid_a1_el2_reset;

	/******************************************************************
	 * TEST CASE 2:
	 *
	 * Allocate a shared MECID, initialize the Realm MECID for Stage 1,
	 * and verify the value written to MECID_A1_EL2 matches the allocated
	 * shared MECID.
	 ******************************************************************/

	CHECK_TRUE(mecid_alloc(&mecid, true));

	mec_realm_mecid_s1_init(mecid);
	mecid_a1_el2_init = read_mecid_a1_el2();

	mec_realm_mecid_s1_reset();
	mecid_a1_el2_reset = read_mecid_a1_el2();

	mecid_free(mecid);

	CHECK_EQUAL(mecid, (unsigned int)mecid_a1_el2_init);
	CHECK_EQUAL(RESERVED_MECID_SYSTEM, (unsigned int)mecid_a1_el2_reset);
}

TEST(mec, mec_realm_mecid_s1_init_TC3)
{
	unsigned int mecid;
	unsigned long mecid_a1_el2;
	bool is_mecid_changed_s1_init = false;
	bool is_mecid_changed_s1_init2 = false;
	bool is_mecid_changed_s1_reset = false;
	bool is_mecid_changed_s1_reset2 = false;

	/******************************************************************
	 * TEST CASE 3:
	 *
	 * Allocate a private MECID and initialize it for Stage 1. Call
	 * mec_realm_mecid_s1_init() again with the same MECID. Verify it
	 * does not trigger an assert and MECID_A1_EL2 is only modified on
	 * the first call due to reference counting.
	 ******************************************************************/

	register_custom_mecid_a1_el2_callbacks();

	CHECK_TRUE(mecid_alloc(&mecid, false));

	mec_realm_mecid_s1_init(mecid);
	is_mecid_changed_s1_init = check_mecid_a1_el2_modified_clear();

	mec_realm_mecid_s1_init(mecid);
	is_mecid_changed_s1_init2 = check_mecid_a1_el2_modified_clear();

	mecid_a1_el2 = read_mecid_a1_el2();

	mec_realm_mecid_s1_reset();
	is_mecid_changed_s1_reset = check_mecid_a1_el2_modified_clear();
	mec_realm_mecid_s1_reset();
	is_mecid_changed_s1_reset2 = check_mecid_a1_el2_modified_clear();

	mecid_free(mecid);

	CHECK_EQUAL(mecid, (unsigned int)mecid_a1_el2);
	CHECK_TRUE(is_mecid_changed_s1_init);
	CHECK_FALSE(is_mecid_changed_s1_init2);
	CHECK_FALSE(is_mecid_changed_s1_reset);
	CHECK_TRUE(is_mecid_changed_s1_reset2);
}

TEST(mec, mec_is_realm_mecid_s1_init_TC1)
{
	unsigned int mecid;
	bool is_init = false;

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Allocate a private MECID, initialize it for Stage 1, and verify
	 * that mec_is_realm_mecid_s1_init() returns true.
	 ******************************************************************/

	CHECK_TRUE(mecid_alloc(&mecid, false));

	mec_realm_mecid_s1_init(mecid);

	is_init = mec_is_realm_mecid_s1_init();

	mec_realm_mecid_s1_reset();

	mecid_free(mecid);

	CHECK_TRUE(is_init);
}

TEST(mec, mec_is_realm_mecid_s1_init_TC2)
{
	bool is_init = false;

	/******************************************************************
	 * TEST CASE 2:
	 *
	 * Do not set the MECID and verify that
	 * mec_is_realm_mecid_s1_init() returns false.
	 ******************************************************************/

	is_init = mec_is_realm_mecid_s1_init();

	CHECK_FALSE(is_init);
}

TEST(mec, mec_realm_mecid_s2_init_TC1)
{
	unsigned int mecid;
	unsigned long vmecid_p_el2;

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Allocate a private MECID, initialize the Realm MECID for Stage 2,
	 * and verify the value written to VMECID_P_EL2 matches the allocated
	 * MECID.
	 ******************************************************************/

	CHECK_TRUE(mecid_alloc(&mecid, false));

	mec_realm_mecid_s2_init(mecid);
	vmecid_p_el2 = read_vmecid_p_el2();

	mec_realm_mecid_s2_reset();

	mecid_free(mecid);

	CHECK_EQUAL(mecid, (unsigned int)vmecid_p_el2);
}

TEST(mec, mec_realm_mecid_s2_init_TC2)
{
	unsigned int mecid;
	unsigned long vmecid_p_el2;

	/******************************************************************
	 * TEST CASE 2:
	 *
	 * Allocate a shared MECID, initialize the Realm MECID for Stage 2,
	 * and verify the value written to VMECID_P_EL2 matches the allocated
	 * shared MECID.
	 ******************************************************************/

	CHECK_TRUE(mecid_alloc(&mecid, true));

	mec_realm_mecid_s2_init(mecid);
	vmecid_p_el2 = read_vmecid_p_el2();

	mec_realm_mecid_s2_reset();

	mecid_free(mecid);

	CHECK_EQUAL(mecid, (unsigned int)vmecid_p_el2);
}

TEST(mec, mec_realm_mecid_s2_reset_TC1)
{
	unsigned int mecid;
	unsigned long vmecid_p_el2;

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Allocate a private MECID, initialize it for Stage 2, then reset
	 * it and verify VMECID_P_EL2 returns to RESERVED_MECID_SYSTEM.
	 ******************************************************************/

	CHECK_TRUE(mecid_alloc(&mecid, false));

	mec_realm_mecid_s2_init(mecid);
	mec_realm_mecid_s2_reset();

	vmecid_p_el2 = read_vmecid_p_el2();

	mecid_free(mecid);

	CHECK_EQUAL(RESERVED_MECID_SYSTEM, (unsigned int)vmecid_p_el2);
}

TEST(mec, is_mec_reset_realm_mecid_TC1)
{
	unsigned int mecid;
	bool is_reset = false;

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Allocate a private MECID, initialize it for Stage 2, and verify
	 * that is_mec_reset_realm_mecid() returns false (not reset).
	 ******************************************************************/

	CHECK_TRUE(mecid_alloc(&mecid, false));

	mec_realm_mecid_s2_init(mecid);

	is_reset = is_mec_reset_realm_mecid();

	mec_realm_mecid_s2_reset();

	mecid_free(mecid);

	CHECK_FALSE(is_reset);
}

ASSERT_TEST(mec, mec_realm_mecid_s2_reset_TC3)
{
	/******************************************************************
	 * TEST CASE 3:
	 *
	 * Attempt to reset the MECID for stage 2 translation without
	 * setting it first to trigger an assert failure.
	 ******************************************************************/

	test_helpers_expect_assert_fail(true);
	mec_realm_mecid_s2_reset();
	test_helpers_fail_if_no_assert_failed();
}

TEST(mec, is_mec_reset_realm_mecid_TC2)
{
	unsigned int mecid;
	bool is_reset = false;

	/******************************************************************
	 * TEST CASE 2:
	 *
	 * Allocate a private MECID, initialize it for Stage 1, and verify
	 * that is_mec_reset_realm_mecid() returns false (not reset).
	 ******************************************************************/

	CHECK_TRUE(mecid_alloc(&mecid, false));

	mec_realm_mecid_s1_init(mecid);

	is_reset = is_mec_reset_realm_mecid();

	mec_realm_mecid_s1_reset();

	mecid_free(mecid);

	CHECK_FALSE(is_reset);
}

TEST(mec, is_mec_reset_realm_mecid_TC3)
{
	bool is_reset = false;

	/******************************************************************
	 * TEST CASE 3:
	 *
	 * Do not set the MECID and verify that
	 * is_mec_reset_realm_mecid() returns true.
	 ******************************************************************/

	is_reset = is_mec_reset_realm_mecid();

	CHECK_TRUE(is_reset);
}

TEST(mec, mecid_max_TC1)
{
	unsigned int max_mecid;

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Call mecid_max() and verify that the returned value is
	 * a valid value.
	 ******************************************************************/

	max_mecid = mecid_max();

	CHECK_TRUE((max_mecid > 0U) && (max_mecid <= 0xFFFFU));
}

TEST(mec, mecid_max_TC2)
{
	unsigned int max_mecid, max_valid_mecid;
	unsigned int mecid_width = 0xbU;

	/******************************************************************
	 * TEST CASE 2:
	 *
	 * Set MECIDR_EL2.MECIDWidthm1. Then call mecid_max() and verify
	 * that the returned value corresponds to the maximum possible
	 * value for a MECID.
	 ******************************************************************/

	reset_mecidr_el2(INPLACE(MECIDR_MECIDWIDTHM1, mecid_width - 1U));

	max_valid_mecid = (1U << mecid_width) - 1U;

	max_mecid = mecid_max();

	CHECK_EQUAL(max_valid_mecid, max_mecid);
}

TEST(mec, mecid_private_count_TC1)
{
	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Limit MECIDR_EL2 so there is no private MECID range available and
	 * verify that no private MECIDs are reported.
	 ******************************************************************/

	reset_mecidr_el2(0U);

	CHECK_EQUAL(0U, mecid_private_count());
}

TEST(mec, mecid_private_count_TC2)
{
	unsigned int mecid_width = 4U;
	unsigned int max_mecid;
	unsigned int private_count;

	/******************************************************************
	 * TEST CASE 2:
	 *
	 * Set MECIDR_EL2.MECIDWidthm1 and verify that the private MECID
	 * count excludes reserved and shared MECIDs.
	 ******************************************************************/

	reset_mecidr_el2(mecid_width - 1U);

	max_mecid = (1U << mecid_width) - 1U;
	private_count = max_mecid - MECID_PRIVATE_START + 1U;

	CHECK_EQUAL(private_count, mecid_private_count());
}

TEST(mec, mecid_alloc_TC1)
{
	unsigned int mecid = MECID_INVALID;

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Limit MECIDR_EL2 so there is no private MECID range available and
	 * verify private allocation fails.
	 ******************************************************************/

	reset_mecidr_el2(0U);

	CHECK_FALSE(mecid_alloc(&mecid, false));
	CHECK_EQUAL(MECID_INVALID, mecid);
}

TEST(mec, mecid_alloc_TC2)
{
	unsigned int mecid1, mecid2, mecid3 = MECID_INVALID;

	/******************************************************************
	 * TEST CASE 2:
	 *
	 * Limit MECIDR_EL2 to two private MECIDs, allocate both, and verify
	 * a third private allocation fails after the circular search wraps.
	 ******************************************************************/

	reset_mecidr_el2(1U);

	CHECK_TRUE(mecid_alloc(&mecid1, false));
	CHECK_TRUE(mecid_alloc(&mecid2, false));
	CHECK_FALSE(mecid_alloc(&mecid3, false));

	mecid_free(mecid1);
	mecid_free(mecid2);

	CHECK_EQUAL(MECID_PRIVATE_START, mecid1);
	CHECK_EQUAL(MECID_PRIVATE_START + 1U, mecid2);
	CHECK_EQUAL(MECID_INVALID, mecid3);
}

TEST(mec, mecid_alloc_TC3)
{
	unsigned int mecid1;
	unsigned int mecid2;

	/******************************************************************
	 * TEST CASE 3:
	 *
	 * Allocate and free a private MECID, then verify that the released
	 * MECID can be allocated again.
	 ******************************************************************/

	CHECK_TRUE(mecid_alloc(&mecid1, false));
	mecid_free(mecid1);

	CHECK_TRUE(mecid_alloc(&mecid2, false));
	mecid_free(mecid2);

	CHECK_EQUAL(mecid1, mecid2);
}

TEST(mec, mec_is_realm_mecid_s2_pvt_TC1)
{
	unsigned int mecid;
	bool is_pvt = false;

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Allocate a shared MECID, initialize it for Stage 2, and verify
	 * that mec_is_realm_mecid_s2_pvt() returns false (not private).
	 ******************************************************************/

	CHECK_TRUE(mecid_alloc(&mecid, true));

	mec_realm_mecid_s2_init(mecid);

	is_pvt = mec_is_realm_mecid_s2_pvt();

	mec_realm_mecid_s2_reset();

	mecid_free(mecid);

	CHECK_FALSE(is_pvt);
}

TEST(mec, mec_is_realm_mecid_s2_pvt_TC2)
{
	unsigned int mecid;
	bool is_pvt = false;

	/******************************************************************
	 * TEST CASE 2:
	 *
	 * Allocate a private MECID, initialize it for Stage 2, and verify
	 * that mec_is_realm_mecid_s2_pvt() returns true (is private).
	 ******************************************************************/

	CHECK_TRUE(mecid_alloc(&mecid, false));

	mec_realm_mecid_s2_init(mecid);

	is_pvt = mec_is_realm_mecid_s2_pvt();

	mec_realm_mecid_s2_reset();

	mecid_free(mecid);

	CHECK_TRUE(is_pvt);
}

TEST(mec, mecid_shared_alloc_TC1)
{
	unsigned int mecid1, mecid2;

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Allocate the shared MECID twice and release it twice to exercise
	 * the non-zero shared-member paths.
	 ******************************************************************/

	CHECK_TRUE(mecid_alloc(&mecid1, true));
	CHECK_TRUE(mecid_alloc(&mecid2, true));

	mecid_free(mecid1);
	mecid_free(mecid2);

	CHECK_EQUAL(MECID_SHARED, mecid1);
	CHECK_EQUAL(MECID_SHARED, mecid2);
}

TEST(mec, TEST_mec_mec_init_mmu_TC1)
{
	bool ret = true;

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Call mec_mec_init_mmu() and check the values read from MECID
	 * registers.
	 ******************************************************************/

	mec_init_mmu();

	ret &= (read_mecid_p0_el2() == RESERVED_MECID_SYSTEM);
	ret &= (read_mecid_p1_el2() == RESERVED_MECID_SYSTEM);
	ret &= (read_mecid_a0_el2() == RESERVED_MECID_SYSTEM);
	ret &= (read_mecid_a1_el2() == RESERVED_MECID_SYSTEM);
	ret &= (read_vmecid_p_el2() == RESERVED_MECID_SYSTEM);
	ret &= (read_vmecid_a_el2() == RESERVED_MECID_SYSTEM);
	ret &= ((read_sctlr2_el2() & SCTLR2_ELx_EMEC_BIT) != 0UL);

	CHECK_TRUE(ret);
}

ASSERT_TEST(mec, TEST_mec_mec_init_mmu_TC2)
{
	/******************************************************************
	 * TEST CASE 2:
	 *
	 * Call mec_mec_init_mmu() when the MMU has already been enabled.
	 * It should trigger an assert failure.
	 ******************************************************************/

	write_sctlr_el2(SCTLR_ELx_M_BIT);

	test_helpers_expect_assert_fail(true);
	mec_init_mmu();
	test_helpers_fail_if_no_assert_failed();
}

TEST_GROUP(no_mec)
{
	TEST_SETUP()
	{
		no_mec_test_setup();
	}

	TEST_TEARDOWN()
	{
		no_mec_test_teardown();
	}
};

TEST(no_mec, mec_realm_mecid_s1_init_TC1)
{
	unsigned int mecid = 1U;

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * mec_realm_mecid_s1_init() returns immediately when FEAT_MEC is
	 * not present and verifies that MECID_A1_EL2 register has not been
	 * accessed.
	 ******************************************************************/

	register_custom_mecid_a1_el2_callbacks();

	mec_realm_mecid_s1_init(mecid);

	CHECK_FALSE(check_mecid_a1_el2_modified_clear());
}

TEST(no_mec, mec_realm_mecid_s1_reset_TC1)
{
	/******************************************************************
	 * TEST CASE 1:
	 *
	 * mec_realm_mecid_s1_reset() returns immediately when FEAT_MEC is
	 * not present and verifies that MECID_A1_EL2 register has not been
	 * accessed.
	 ******************************************************************/

	register_custom_mecid_a1_el2_callbacks();

	mec_realm_mecid_s1_reset();

	CHECK_FALSE(check_mecid_a1_el2_modified_clear());
}

TEST(no_mec, is_mec_reset_realm_mecid_TC1)
{
	bool is_reset = false;

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Test whether is_mec_reset_realm_mecid() returns always true when
	 * FEAT_MEC is not present.
	 ******************************************************************/

	register_custom_mecid_a1_el2_callbacks();

	is_reset = is_mec_reset_realm_mecid();

	CHECK_TRUE(is_reset);
	CHECK_FALSE(check_mecid_a1_el2_read_clear());
}

TEST(no_mec, mec_is_realm_mecid_s1_init_TC1)
{
	bool is_init = false;

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Verify that mec_is_realm_mecid_s1_init() returns always true
	 * when FEAT_MEC is not present.
	 ******************************************************************/

	register_custom_mecid_a1_el2_callbacks();

	is_init = mec_is_realm_mecid_s1_init();

	CHECK_TRUE(is_init);
	CHECK_FALSE(check_mecid_a1_el2_read_clear());
}

TEST(no_mec, mec_realm_mecid_s2_init_TC1)
{
	unsigned int mecid = 1U;

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * mec_realm_mecid_s2_init() returns immediately when FEAT_MEC is
	 * not present. Test verifies that VMECID_P_EL2 has not been
	 * accessed.
	 ******************************************************************/

	register_custom_vmecid_p_el2_callbacks();

	mec_realm_mecid_s2_init(mecid);

	CHECK_FALSE(check_vmecid_p_el2_read_clear());
}

TEST(no_mec, mec_realm_mecid_s2_reset_TC1)
{
	/******************************************************************
	 * TEST CASE 1:
	 *
	 * mec_realm_mecid_s2_reset() returns immediately when FEAT_MEC is
	 * not present. Test verifies that VMECID_P_EL2 has not been
	 * accessed.
	 ******************************************************************/

	register_custom_vmecid_p_el2_callbacks();

	mec_realm_mecid_s2_reset();

	CHECK_FALSE(check_vmecid_p_el2_read_clear());
}

ASSERT_TEST(no_mec, mecid_max_TC1)
{	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Call mecid_max() when FEAT_MEC is not present. It should trigger
	 * an assert failure.
	 ******************************************************************/

	test_helpers_expect_assert_fail(true);
	(void)mecid_max();
	test_helpers_fail_if_no_assert_failed();
}

TEST(no_mec, mecid_free_TC1)
{
	unsigned int mecid = 1U;

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Call mecid_free(). It should return immediately when
	 * FEAT_MEC is not present. This test is for coverage purposes only.
	 ******************************************************************/

	mecid_free(mecid);
}

TEST(no_mec, mecid_alloc_TC1)
{
	unsigned int mecid = MECID_INVALID;

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Call mecid_alloc(). It should return the system MECID when
	 * FEAT_MEC is not present.
	 ******************************************************************/

	CHECK_TRUE(mecid_alloc(&mecid, false));
	CHECK_EQUAL(RESERVED_MECID_SYSTEM, mecid);
}

TEST(no_mec, mecid_private_count_TC1)
{
	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Verify that no private MECIDs are reported when FEAT_MEC is not
	 * present.
	 ******************************************************************/

	CHECK_EQUAL(0U, mecid_private_count());
}

TEST(no_mec, mec_is_realm_mecid_s2_pvt_TC1)
{
	bool is_pvt = false;

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Verify that mec_is_realm_mecid_s2_pvt() returns always false
	 * when FEAT_MEC is not present.
	 ******************************************************************/

	is_pvt = mec_is_realm_mecid_s2_pvt();

	CHECK_FALSE(is_pvt);
}

TEST(no_mec, mec_init_mmu_TC1)
{
	unsigned long sctlr2_el2;

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Call mec_init_mmu(). It should return immediately and leave EMEC
	 * disabled when FEAT_MEC is not present.
	 ******************************************************************/

	mec_init_mmu();

	sctlr2_el2 = read_sctlr2_el2();

	CHECK_EQUAL(0UL, sctlr2_el2 & SCTLR2_ELx_EMEC_BIT);
}

TEST_GROUP(mec_restore_after_assert1)
{
	unsigned int mecid1;
	unsigned int mecid2;

	TEST_SETUP()
	{
		mec_test_setup();
	}

	TEST_TEARDOWN()
	{
		/*
		 * MECID reference counters can't be reset manually, so
		 * MECID_A1_EL2 is set manually so reference counter and
		 * MECID_A1_EL2 can be reset through
		 * mec_realm_mecid_s1_reset() without triggering an assert
		 * failure. The expected assert is triggered after incrementing
		 * the S1 reference count, so unwind both init calls.
		 */
		write_mecid_a1_el2(mecid1);
		mec_realm_mecid_s1_reset();
		mec_realm_mecid_s1_reset();

		mecid_free(mecid1);
		mecid_free(mecid2);
	}
};

ASSERT_TEST(mec_restore_after_assert1, mec_realm_mecid_s1_init_TC1)
{
	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Attempt to set the MECID for a second time before resetting it
	 * to trigger an assert failure.
	 ******************************************************************/

	CHECK_TRUE(mecid_alloc(&mecid1, false));
	CHECK_TRUE(mecid_alloc(&mecid2, false));

	mec_realm_mecid_s1_init(mecid1);

	test_helpers_expect_assert_fail(true);
	mec_realm_mecid_s1_init(mecid2);
	test_helpers_fail_if_no_assert_failed();
}

TEST_GROUP(mec_restore_after_assert2)
{
	unsigned int mecid;

	TEST_SETUP()
	{
		mec_test_setup();
	}

	TEST_TEARDOWN()
	{
		/*
		* MECID reference counters can't be reset manually, so
		* MECID_A1_EL2 counter needs to be reset properly.
		* The register was set manually in the test, so just free the MECID.
		*/

		/* Reset register manually since test set it */
		write_mecid_a1_el2(RESERVED_MECID_SYSTEM);

		mecid_free(mecid);
	}
};

ASSERT_TEST(mec_restore_after_assert2, mec_realm_mecid_s1_init_TC1)
{
	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Set MECID_A1_EL2 to a value different than the default MECID and
	 * attempt to set the MECID to trigger an assert failure.
	 ******************************************************************/

	CHECK_TRUE(mecid_alloc(&mecid, false));

	write_mecid_a1_el2(1U);

	test_helpers_expect_assert_fail(true);
	mec_realm_mecid_s1_init(mecid);
	test_helpers_fail_if_no_assert_failed();
}

TEST_GROUP(mec_restore_after_assert3)
{
	TEST_SETUP()
	{
		mec_test_setup();
	}

	TEST_TEARDOWN()
	{
		/*
		* The test triggers an assert before any MECID is initialized,
		* so just clean up the state.
		*/
		/* No cleanup needed - the assert happened before any initialization */
	}
};

ASSERT_TEST(mec_restore_after_assert3, mec_realm_mecid_s1_reset_TC1)
{
	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Attempt to reset the MECID without setting it first to
	 * trigger an assert failure.
	 ******************************************************************/

	test_helpers_expect_assert_fail(true);
	mec_realm_mecid_s1_reset();
	test_helpers_fail_if_no_assert_failed();
}

TEST_GROUP(mec_restore_after_assert4)
{
	unsigned int mecid;
	bool should_free_mecid;
	bool should_reset_s2;

	TEST_SETUP()
	{
		mec_test_setup();
		mecid = 0U;
		should_free_mecid = false;
		should_reset_s2 = false;
	}

	TEST_TEARDOWN()
	{
		if (should_reset_s2) {
			write_vmecid_p_el2(RESERVED_MECID_SYSTEM);
		}

		/*
		 * Restore MECID_A1_EL2 to RESERVED_MECID_SYSTEM after the test
		 * case.
		 */
		write_mecid_a1_el2(RESERVED_MECID_SYSTEM);

		/* Release MECID after assert failure if it was allocated */
		if (should_free_mecid) {
			mecid_free(mecid);
		}
	}
};

ASSERT_TEST(mec_restore_after_assert4, mec_realm_mecid_s2_init_TC3)
{
	/******************************************************************
	 * TEST CASE 3:
	 *
	 * Allocate a private MECID, initialize it for Stage 2, then attempt
	 * to initialize it again. This should trigger an assert failure.
	 ******************************************************************/

	CHECK_TRUE(mecid_alloc(&mecid, false));
	should_free_mecid = true;

	mec_test_realm_mecid_s2_init(mecid);
	should_reset_s2 = true;

	test_helpers_expect_assert_fail(true);
	mec_test_realm_mecid_s2_init(mecid);
	test_helpers_fail_if_no_assert_failed();
}

ASSERT_TEST(mec_restore_after_assert4, mec_realm_mecid_s1_reset_TC1)
{
	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Manually override the MECID_A1_EL2 to a value different than
	 * the expected one and attempt to reset the MECID to trigger an
	 * assert failure.
	 ******************************************************************/

	CHECK_TRUE(mecid_alloc(&mecid, false));
	should_free_mecid = true;

	mec_realm_mecid_s1_init(mecid);
	write_mecid_a1_el2(RESERVED_MECID_SYSTEM);

	test_helpers_expect_assert_fail(true);
	mec_realm_mecid_s1_reset();
	test_helpers_fail_if_no_assert_failed();
}

ASSERT_TEST(mec_restore_after_assert4, mecid_free_TC1)
{
	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Attempt to free an invalid MECID value to trigger an assert
	 * failure.
	 ******************************************************************/

	mecid = 0x10000U;

	test_helpers_expect_assert_fail(true);
	mecid_free(mecid);
	test_helpers_fail_if_no_assert_failed();
}

ASSERT_TEST(mec_restore_after_assert4, mec_is_realm_mecid_s2_pvt_TC1)
{
	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Check whether the Stage 2 MECID is private when VMECID_P_EL2
	 * is the default MECID. It should trigger an assert failure.
	 ******************************************************************/

	test_helpers_expect_assert_fail(true);
	mec_is_realm_mecid_s2_pvt();
	test_helpers_fail_if_no_assert_failed();
}

TEST_GROUP(mec_restore_after_assert5)
{
	unsigned int mecid;
	bool should_reset_s1;

	TEST_SETUP()
	{
		mec_test_setup();
		mecid = 0U;
		should_reset_s1 = false;
	}

	TEST_TEARDOWN()
	{
		if (should_reset_s1) {
			mec_realm_mecid_s1_reset();
		}
		if (mecid != 0U) {
			mecid_free(mecid);
		}
	}
};

ASSERT_TEST(mec_restore_after_assert5, mecid_alloc_TC1)
{
	unsigned int next_mecid;

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Keep a Stage 1 MECID programmed and verify private allocation
	 * asserts before reserving another private MECID.
	 ******************************************************************/

	CHECK_TRUE(mecid_alloc(&mecid, false));
	mec_realm_mecid_s1_init(mecid);
	should_reset_s1 = true;

	test_helpers_expect_assert_fail(true);
	(void)mecid_alloc(&next_mecid, false);
	test_helpers_fail_if_no_assert_failed();
}

TEST_GROUP(mec_restore_after_assert6)
{
	TEST_SETUP()
	{
		mec_test_setup();
	}

	TEST_TEARDOWN()
	{
		/*
		 * mec_init_state() updates g_mec_state before validating the
		 * state size, so the assert path can leave g_mec_state pointing
		 * at the test-local state object. Restore the helper-owned state
		 * before mec_test_teardown() calls mec_test_reset().
		 */
		mec_test_setup();
		mec_test_teardown();
	}
};

ASSERT_TEST(mec_restore_after_assert6, mec_init_state_TC1)
{
	struct mec_state_s state = {};

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Pass a state buffer that is too small and verify mec_init_state()
	 * asserts after recording the provided state pointer.
	 ******************************************************************/

	test_helpers_expect_assert_fail(true);
	mec_init_state((uintptr_t)&state, sizeof(state) - 1U);
	test_helpers_fail_if_no_assert_failed();
}

ASSERT_TEST(mec_restore_after_assert6, mec_init_state_TC2)
{
	/******************************************************************
	 * TEST CASE 2:
	 *
	 * Pass a null state address and verify mec_init_state() asserts
	 * before updating the current MEC state pointer.
	 ******************************************************************/

	test_helpers_expect_assert_fail(true);
	mec_init_state(0UL, sizeof(struct mec_state_s));
	test_helpers_fail_if_no_assert_failed();
}

TEST_GROUP(no_sctlr2_mec)
{
	TEST_SETUP()
	{
		no_sctlr2_mec_test_setup();
	}

	TEST_TEARDOWN()
	{
		no_sctlr2_mec_test_teardown();
	}
};

TEST(no_sctlr2_mec, mec_init_mmu_TC1)
{
	unsigned long sctlr2_el2;

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Call mec_init_mmu() when FEAT_SCTRL2 is not present and verify
	 * that EMEC is not enabled.
	 ******************************************************************/

	mec_init_mmu();

	sctlr2_el2 = read_sctlr2_el2();

	CHECK_EQUAL(0UL, sctlr2_el2 & SCTLR2_ELx_EMEC_BIT);
}
