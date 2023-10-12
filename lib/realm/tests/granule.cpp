/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <CppUTest/CommandLineTestRunner.h>
#include <CppUTest/TestHarness.h>

extern "C" {
#include <buffer.h>
#include <buffer_private.h>
#include <cpuid.h>
#include <granule.h>	/* Interface to exercise */
#include <host_harness.h>
#include <host_utils.h>
#include <realm_test_utils.h>
#include <status.h>
#include <stdlib.h>
#include <string.h>
#include <test_harness.h>
#include <test_helpers.h>
#include <unistd.h>
#include <utils_def.h>
}

/* Function to get a random granule index in the range [1, NR_GRANULES - 2] */
static inline unsigned int get_rand_granule_idx(void)
{
	return (unsigned int)test_helpers_get_rand_in_range(1UL,
					test_helpers_get_nr_granules() - 2U);

}

/* Function to get the index of the last granule in the system */
static inline unsigned int get_last_granule_idx(void)
{
	return test_helpers_get_nr_granules() - 1U;
}

/*
 * Function to get a random address within the granules range.
 * The address will be aligned to granule size.
 */
static inline unsigned long get_rand_granule_addr(void)
{
	unsigned long addr;
	int random_granule = get_rand_granule_idx();

	addr = (unsigned long)(random_granule * GRANULE_SIZE)
						+ host_util_get_granule_base();

	return addr;
}

/*
 * Function generate an invalid granule address outside the valid range.
 * The address will be aligned to GRANULE_SIZE.
 *
 * If the address cannot be generated, the function will return false.
 */
static bool get_out_of_range_granule(unsigned long *addr, bool higher_range)
{
	if (addr == NULL) {
		return false;
	}

	if (higher_range == true) {
		*addr = (test_helpers_get_rand_in_range(
					test_helpers_get_nr_granules(),
					(test_helpers_get_nr_granules() + 10)) *
								GRANULE_SIZE);
		*addr += host_util_get_granule_base();
	} else {
		unsigned int granules_below;

		granules_below =
			(unsigned int)(host_util_get_granule_base() / GRANULE_SIZE);

		if (granules_below == 0) {
			return false;
		}

		*addr = host_util_get_granule_base();
		*addr -= (granules_below == 1U ?
			    GRANULE_SIZE :
			    GRANULE_SIZE * test_helpers_get_rand_in_range(1UL,
							granules_below - 1U));
	}

	return true;
}

/*
 * Function to set the lock of a granule to a non-zero value and
 * return the value.
 *
 * The input granule pointer must be valid.
 */
static inline unsigned int set_rand_non_zero_lock_value(struct granule *granule)
{
	unsigned int lock =
		(unsigned int)test_helpers_get_rand_in_range(1UL, INT_MAX);

	granule->lock.val = lock;
	return lock;
}

TEST_GROUP(granule) {


	TEST_SETUP()
	{
		test_helpers_init();

		/* Enable the platform with support for multiple PEs */
		test_helpers_rmm_start(true);

		/* Make sure current cpu id is 0 (primary processor) */
		host_util_set_cpuid(0U);

		test_helpers_expect_assert_fail(false);
	}

	TEST_TEARDOWN()
	{
		/*
		 * Clean RMM's internal struct granule array
		 * for a clean state for the next tests.
		 */
		memset((void *)realm_test_util_granule_struct_base(), 0,
			sizeof(struct granule) *
					test_helpers_get_nr_granules());

		/*
		 * Unregister any existing callback that might
		 * have been installed
		 */
		(void)test_helpers_unregister_cb(CB_BUFFER_MAP);
		(void)test_helpers_unregister_cb(CB_BUFFER_UNMAP);
	}
};

TEST(granule, addr_to_granule_TC1)
{
	struct granule *granule;
	struct granule *expected_granule;
	unsigned int granule_indexes[3] = {0U,
					   get_rand_granule_idx(),
					   get_last_granule_idx()};
	unsigned long addr;

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Verify the granule address for a valid physical address.
	 * Test the first and the last valid granules as well as random
	 * granules in between.
	 ******************************************************************/

	for (unsigned int i = 0U; i < 3; i++) {
		/* Calculate the expected granule address */
		expected_granule = realm_test_util_granule_struct_base() +
							granule_indexes[i];
		/* Calculated the expected PA for the granule */
		addr = (granule_indexes[i] * GRANULE_SIZE) +
						host_util_get_granule_base();
		granule = addr_to_granule(addr);
		POINTERS_EQUAL(expected_granule, granule);
	}
}

ASSERT_TEST(granule, addr_to_granule_TC2)
{
	/******************************************************************
	 * TEST CASE 2:
	 *
	 * Verify that addr_to_granule() asserts when the address is a
	 * NULL pointer
	 ******************************************************************/

	test_helpers_expect_assert_fail(true);
	(void)addr_to_granule((unsigned long)NULL);
	test_helpers_fail_if_no_assert_failed();
}

ASSERT_TEST(granule, addr_to_granule_TC3)
{
	unsigned long addr = get_rand_granule_addr();

	/******************************************************************
	 * TEST CASE 3:
	 *
	 * Verify that addr_to_granule() asserts with an unaligned address
	 ******************************************************************/

	addr += test_helpers_get_rand_in_range(1UL, GRANULE_SIZE - 2U);

	test_helpers_expect_assert_fail(true);
	(void)addr_to_granule(addr);
	test_helpers_fail_if_no_assert_failed();
}

ASSERT_TEST(granule, addr_to_granule_TC4)
{
	unsigned long addr = 0;

	/******************************************************************
	 * TEST CASE 4:
	 *
	 * Verify that addr_to_granule() asserts with an address below
	 * the valid range
	 ******************************************************************/

	/* Check an address below the valid range */
	(void)get_out_of_range_granule(&addr, false);
	test_helpers_expect_assert_fail(true);
	(void)addr_to_granule(addr);
	test_helpers_fail_if_no_assert_failed();
}

ASSERT_TEST(granule, addr_to_granule_TC5)
{
	unsigned long addr;

	/******************************************************************
	 * TEST CASE 5:
	 *
	 * Verify that addr_to_granule() asserts with an address over
	 * the valid range
	 ******************************************************************/

	/* Check an address over the valid range */
	(void)get_out_of_range_granule(&addr, true);
	test_helpers_expect_assert_fail(true);
	(void)addr_to_granule(addr);
	test_helpers_fail_if_no_assert_failed();
}

TEST(granule, granule_addr_TC1)
{
	struct granule *granule;
	unsigned int granule_indexes[3] = {0U,
					   get_rand_granule_idx(),
					   get_last_granule_idx()};
	unsigned long expected_address;
	unsigned long addr;

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Get a granule and verify that the physical address
	 * returned by granule_addr() matches the manually calculated one.
	 * Test the first and the last valid granules as well as random
	 * granules in between.
	 ******************************************************************/
	for (unsigned int i = 0U; i < 3U; i++) {
		granule = realm_test_util_granule_struct_base() +
							granule_indexes[i];
		expected_address = (granule_indexes[i] * GRANULE_SIZE) +
						host_util_get_granule_base();
		addr = granule_addr(granule);
		POINTERS_EQUAL(expected_address, addr);

		/*
		 * Verify that not other parameters of the granule
		 * are altered
		 */
		CHECK_EQUAL(0, granule->state);
		CHECK_EQUAL(0, granule->lock.val);
	}
}

ASSERT_TEST(granule, granule_addr_TC2)
{
	/******************************************************************
	 * TEST CASE 2:
	 *
	 * Verify that granule_addr() asserts with a NULL address
	 ******************************************************************/

	test_helpers_expect_assert_fail(true);
	(void)granule_addr(NULL);
	test_helpers_fail_if_no_assert_failed();
}

ASSERT_TEST(granule, granule_addr_TC3)
{
	struct granule *granule;
	unsigned int idx = get_last_granule_idx();

	/******************************************************************
	 * TEST CASE 3:
	 *
	 * Verify that granule_addr() asserts if the granule index >=
	 * NR_GRANULES
	 ******************************************************************/

	idx += (unsigned long)test_helpers_get_rand_in_range(1UL, 10UL);
	granule = realm_test_util_granule_struct_base() + idx;
	test_helpers_expect_assert_fail(true);
	(void)granule_addr(granule);
	test_helpers_fail_if_no_assert_failed();
}

ASSERT_TEST(granule, granule_addr_TC4)
{
	struct granule *granule;

	/******************************************************************
	 * TEST CASE 4:
	 *
	 * Verify that granule_addr() asserts if the granule address <
	 * granule[0];
	 ******************************************************************/

	granule = realm_test_util_granule_struct_base() - 1U;
	test_helpers_expect_assert_fail(true);
	(void)granule_addr(granule);
	test_helpers_fail_if_no_assert_failed();

}

ASSERT_TEST(granule, granule_addr_TC5)
{
	uintptr_t granule;

	/******************************************************************
	 * TEST CASE 5:
	 *
	 * Verify that granule_addr() asserts if the granule address is
	 * not properly aligned.
	 ******************************************************************/

	granule = (uintptr_t)realm_test_util_granule_struct_base();
	granule += test_helpers_get_rand_in_range(1UL,
					sizeof(struct granule) - 1U);
	test_helpers_expect_assert_fail(true);
	(void)granule_addr((struct granule *)granule);
	test_helpers_fail_if_no_assert_failed();

}

TEST(granule, granule_refcount_read_relaxed_TC1)
{
	struct granule *granule;
	unsigned long addr = get_rand_granule_addr();
	unsigned long val =
		(unsigned long)test_helpers_get_rand_in_range(10UL, INT_MAX);
	unsigned long read_val;

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Set the refcount for a granule manually and verify with
	 * granule_refcount_read_relaxed that the status is correct.
	 ******************************************************************/
	granule = addr_to_granule(addr);

	/* Set the refcount */
	granule->refcount = val;

	/* Read the value */
	read_val = granule_refcount_read_relaxed(granule);
	CHECK_EQUAL(val, read_val);

	/* Verify that not other parameters of the granule are altered */
	CHECK_EQUAL(0, granule->state);
	CHECK_EQUAL(0, granule->lock.val);

	/*
	 * granule_refcount_read_relaxed doesn't validate that the pointer
	 * to the granule is not NULL, so skip that test.
	 */
}

TEST(granule, granule_refcount_read_acquire_TC1)
{
	struct granule *granule;
	unsigned long addr = get_rand_granule_addr();
	unsigned long val =
		(unsigned long)test_helpers_get_rand_in_range(10UL, 10000UL);
	unsigned long read_val;

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Set the refcount for a granule manually and verify with
	 * granule_refcount_read_acquire that the status is correct.
	 ******************************************************************/
	granule = addr_to_granule(addr);

	/* Set the refcount */
	granule->refcount = val;

	/* Read the value */
	read_val = granule_refcount_read_acquire(granule);
	CHECK_EQUAL(val, read_val);

	/* Verify that not other parameters of the granule are altered */
	CHECK_EQUAL(0, granule->state);
	CHECK_EQUAL(0, granule->lock.val);

	/*
	 * granule_refcount_read_acquire doesn't validate that the pointer
	 * to the granule is not NULL, so skip that test.
	 */
}

TEST(granule, find_granule_TC1)
{
	struct granule *expected_granule;
	unsigned int granule_indexes[3] = {0U,
					   get_rand_granule_idx(),
					   get_last_granule_idx()};
	unsigned long address;
	struct granule *granule;

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Get a granule and verify that its physical address
	 * matches the calculated one.
	 * Test the first and the last valid granules as well as random
	 * granules in between.
	 ******************************************************************/

	for (unsigned int i = 0U; i < 3U; i++) {
		expected_granule = realm_test_util_granule_struct_base() +
							granule_indexes[i];
		address = (granule_indexes[i] * GRANULE_SIZE) +
						host_util_get_granule_base();
		granule = find_granule(address);
		POINTERS_EQUAL(expected_granule, granule);

		/*
		 * Verify that not other parameters of the granule are altered
		 */
		CHECK_TEXT(granule->state == 0, "Invalid granule state");
		CHECK_TEXT(granule->lock.val == 0,
					"Invalid granule lock status");
	}
}

TEST(granule, find_granule_TC2)
{
	unsigned long address;
	struct granule *granule;

	/***************************************************************
	 * TEST CASE 2:
	 *
	 * Try to get a granule for an unaligned address.
	 ***************************************************************/
	address = get_rand_granule_addr();
	address += test_helpers_get_rand_in_range(1UL, GRANULE_SIZE - 1U);

	granule = find_granule(address);
	POINTERS_EQUAL(NULL, granule);
}

TEST(granule, find_granule_TC3)
{
	unsigned long address;
	struct granule *granule;

	/***************************************************************
	 * TEST CASE 3:
	 *
	 * Try to get a granule for an address outside the valid range.
	 ***************************************************************/

	(void)get_out_of_range_granule(&address, true);
	granule = find_granule(address);

	POINTERS_EQUAL(NULL, granule);

	/* Try the lower boundary as well */
	if (get_out_of_range_granule(&address, false) == true) {
		granule = find_granule(address);
		POINTERS_EQUAL(NULL, granule);
	}
}

TEST(granule, find_lock_two_granules_TC1)
{
	unsigned long g1_index, g2_index;
	struct granule *exp_g1, *exp_g2;
	struct granule *g1, *g2;
	unsigned long addr1, addr2;
	bool retval;

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Find and lock two valid granules, with valid expected states
	 * (GRANULE_STATE_NS).
	 ******************************************************************/

	/* Get random indexes for the granules */
	do {
		g1_index = test_helpers_get_rand_in_range(1UL,
					test_helpers_get_nr_granules() - 1);
		g2_index = test_helpers_get_rand_in_range(1,
					test_helpers_get_nr_granules() - 1);
	} while (g1_index == g2_index);

	/* Get the expected address for the granules */
	exp_g1 = realm_test_util_granule_struct_base() + g1_index;
	exp_g2 = realm_test_util_granule_struct_base() + g2_index;

	/* Get the expected PA for the corresponding granules */
	addr1 = (g1_index * GRANULE_SIZE) + host_util_get_granule_base();
	addr2 = (g2_index * GRANULE_SIZE) + host_util_get_granule_base();

	g1 = NULL;
	g2 = NULL;

	/* Lock the granules */
	retval = find_lock_two_granules(addr1, GRANULE_STATE_NS, &g1,
					addr2, GRANULE_STATE_NS, &g2);

	CHECK(retval);
	CHECK_FALSE(g1 == NULL);
	CHECK_FALSE(g2 == NULL);
	POINTERS_EQUAL(exp_g1, g1);
	POINTERS_EQUAL(exp_g2, g2);
	CHECK_FALSE(g1->lock.val == 0);
	CHECK_FALSE(g2->lock.val == 0);
	CHECK_EQUAL(GRANULE_STATE_NS, g1->state);
	CHECK_EQUAL(GRANULE_STATE_NS, g2->state);
}

TEST(granule, find_lock_two_granules_TC2)
{
	struct granule *g1, *g2;
	unsigned long addr;
	bool retval;

	/******************************************************************
	 * TEST CASE 2:
	 *
	 * Find and lock two valid granules, with valid expected states
	 * (GRANULE_STATE_NS). Both granules' addresses are the same.
	 ******************************************************************/

	addr = get_rand_granule_addr();
	g1 = NULL;
	g2 = NULL;

	/* Lock the granules */
	retval = find_lock_two_granules(addr, GRANULE_STATE_NS, &g1,
					addr, GRANULE_STATE_NS, &g2);

	CHECK_FALSE(retval);

	/* Check that the granule address are the same as before calling */
	POINTERS_EQUAL(NULL, g1);
	POINTERS_EQUAL(NULL, g2);
}

TEST(granule, find_lock_two_granules_TC3)
{
	struct granule *g1, *g2;
	unsigned long addr1, addr2, tmp_addr;
	bool retval;

	/******************************************************************
	 * TEST CASE 3:
	 *
	 * Find and lock two valid granules, one of them to a valid address
	 * and the other to a misaligned one.
	 *
	 * Try all possible valid, non-valid permutations.
	 ******************************************************************/

	/* Get random PAs for two different granules */
	do {
		addr1 = get_rand_granule_addr();
		addr2 = get_rand_granule_addr();
	} while (addr1 == addr2);

	g1 = NULL;
	g2 = NULL;

	/* Get a misaligned address */
	tmp_addr = addr2 + test_helpers_get_rand_in_range(1UL, GRANULE_SIZE - 1);

	retval = find_lock_two_granules(tmp_addr, GRANULE_STATE_NS, &g1,
					addr1, GRANULE_STATE_NS, &g2);

	CHECK_FALSE(retval);

	/* Check that the granule address are the same as before calling */
	POINTERS_EQUAL(NULL, g1);
	POINTERS_EQUAL(NULL, g2);

	retval = find_lock_two_granules(addr1, GRANULE_STATE_NS, &g1,
					tmp_addr, GRANULE_STATE_NS, &g2);

	CHECK_FALSE(retval);

	/* Check that the granule address are the same as before calling */
	POINTERS_EQUAL(NULL, g1);
	POINTERS_EQUAL(NULL, g2);
}

TEST(granule, find_lock_two_granules_TC4)
{
	struct granule *g1, *g2;
	unsigned long addr1, addr2, tmp_addr;
	bool retval;

	/******************************************************************
	 * TEST CASE 4:
	 *
	 * Find and lock two valid granules, one of them to a valid address
	 * and the other to an out of range one.
	 *
	 * Try all possible valid, non-valid permutations.
	 ******************************************************************/

	/* Get random PAs for two different granules */
	do {
		addr1 = get_rand_granule_addr();
		addr2 = get_rand_granule_addr();
	} while (addr1 == addr2);

	g1 = NULL;
	g2 = NULL;

	(void)get_out_of_range_granule(&tmp_addr, true);
	retval = find_lock_two_granules(tmp_addr, GRANULE_STATE_NS, &g1,
					addr2, GRANULE_STATE_NS, &g2);

	CHECK_FALSE(retval);

	/* Check that the granule address are the same as before calling */
	POINTERS_EQUAL(NULL, g1);
	POINTERS_EQUAL(NULL, g2);

	/* Try the lower boundary as well if possible */
	if (get_out_of_range_granule(&tmp_addr, false) == true) {
		retval = find_lock_two_granules(tmp_addr, GRANULE_STATE_NS,
					&g1, addr2, GRANULE_STATE_NS, &g2);

		CHECK_FALSE(retval);

		/* Check that the granule address are the same as before calling */
		POINTERS_EQUAL(NULL, g1);
		POINTERS_EQUAL(NULL, g2);
	}

	(void)get_out_of_range_granule(&tmp_addr, true);
	retval = find_lock_two_granules(addr1, GRANULE_STATE_NS, &g1,
					tmp_addr, GRANULE_STATE_NS, &g2);

	CHECK_FALSE(retval);

	/* Check that the granule address are the same as before calling */
	POINTERS_EQUAL(NULL, g1);
	POINTERS_EQUAL(NULL, g2);

	/* Try the lower boundary as well if possible */
	if (get_out_of_range_granule(&tmp_addr, false) == true) {

		retval = find_lock_two_granules(addr1, GRANULE_STATE_NS, &g1,
					tmp_addr, GRANULE_STATE_NS, &g2);

		CHECK_FALSE(retval);

		/* Check that the granule address are the same as before calling */
		POINTERS_EQUAL(NULL, g1);
		POINTERS_EQUAL(NULL, g2);
	}
}

TEST(granule, find_lock_two_granules_TC5)
{
	struct granule *g1, *g2;
	unsigned long addr1, addr2;
	bool retval;

	/******************************************************************
	 * TEST CASE 5:
	 *
	 * Try to find and lock the granules for two valid addresses
	 * with an incorrect expected granule state.
	 *
	 * Try all possible non valid state combinations.
	 ******************************************************************/

	/* Get random PAs for two different granules */
	do {
		addr1 = get_rand_granule_addr();
		addr2 = get_rand_granule_addr();
	} while (addr1 == addr2);

	g1 = NULL;
	g2 = NULL;

	for (unsigned int state1 = GRANULE_STATE_NS;
	     state1 <= GRANULE_STATE_LAST; state1++) {

		for (unsigned int state2 = GRANULE_STATE_NS;
		     state2 <= GRANULE_STATE_LAST; state2++) {
			if (state1 == GRANULE_STATE_NS &&
			    state2 == GRANULE_STATE_NS) {
				/*
				 * Skip. Test case already checked as we expect
				 * the default state to be STATE_NS.
				 */
				continue;
			}
			retval = find_lock_two_granules(addr1,
					(enum granule_state)state1, &g1,
					addr2, (enum granule_state)state2, &g2);

			CHECK_FALSE(retval);

			/*
			 * Check that the granule address are the same
			 * as before calling
			 */
			POINTERS_EQUAL(NULL, g1);
			POINTERS_EQUAL(NULL, g2);
		} /* granule 2 state. */
	} /* granule 1 state. */
}

ASSERT_TEST(granule, find_lock_two_granules_TC6)
{
	struct granule *granule;
	unsigned long addr1, addr2;

	/******************************************************************
	 * TEST CASE 6:
	 *
	 * Verify that find_lock_two_granules() assert when the first
	 * reference to a granule pointer is NULL.
	 ******************************************************************/

	/* Get random PAs for two different granules */
	do {
		addr1 = get_rand_granule_addr();
		addr2 = get_rand_granule_addr();
	} while (addr1 == addr2);

	granule = NULL;

	test_helpers_expect_assert_fail(true);
	(void)find_lock_two_granules(addr1, GRANULE_STATE_DELEGATED, NULL,
				     addr2, GRANULE_STATE_DELEGATED, &granule);
	test_helpers_fail_if_no_assert_failed();
}

ASSERT_TEST(granule, find_lock_two_granules_TC7)
{
	struct granule *granule;
	unsigned long addr1, addr2;

	/******************************************************************
	 * TEST CASE 7:
	 *
	 * Verify that find_lock_two_granules() assert when the second
	 * reference to a granule pointer is NULL.
	 ******************************************************************/

	/* Get random PAs for two different granules */
	do {
		addr1 = get_rand_granule_addr();
		addr2 = get_rand_granule_addr();
	} while (addr1 == addr2);

	granule = NULL;

	test_helpers_expect_assert_fail(true);
	(void)find_lock_two_granules(addr1, GRANULE_STATE_DELEGATED, &granule,
				     addr2, GRANULE_STATE_DELEGATED, NULL);
	test_helpers_fail_if_no_assert_failed();
}

TEST(granule, find_lock_granule_TC1)
{
	struct granule *granule;
	unsigned long addrs[3] = {host_util_get_granule_base(),
				  (get_rand_granule_idx() * GRANULE_SIZE) +
					host_util_get_granule_base(),
				  ((test_helpers_get_nr_granules() - 1) *
								GRANULE_SIZE) +
					host_util_get_granule_base()};

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Find and lock a granule and verify that it is on the
	 * right state (granules should be in GRANULE_STATE_NS) by default.
	 * Test the first and the last valid granules as well as random
	 * granules in between.
	 ******************************************************************/
	for (unsigned int i = 0U; i < 3U; i++) {
		granule = find_lock_granule(addrs[i], GRANULE_STATE_NS);
		CHECK_FALSE(granule == NULL);
		CHECK_FALSE(granule->lock.val == 0);
	}
}

TEST(granule, find_lock_granule_TC2)
{
	struct granule *granule;
	unsigned long addrs[3] = {host_util_get_granule_base(),
				  (get_rand_granule_idx() * GRANULE_SIZE) +
					host_util_get_granule_base(),
				  ((test_helpers_get_nr_granules() - 1) *
								GRANULE_SIZE) +
					host_util_get_granule_base()};

	/***************************************************************
	 * TEST CASE 2:
	 *
	 * Try to find and lock a granule to all possible
	 * unexpected states.
	 * Test the first and the last valid granules as well as random
	 * granules in between.
	 ***************************************************************/
	for (unsigned int i = 0U; i < 3U; i++) {
		for (unsigned int state = GRANULE_STATE_NS + 1U;
		     state <= GRANULE_STATE_LAST; state++) {
			granule = find_lock_granule(addrs[i],
						    (enum granule_state)state);
			POINTERS_EQUAL(NULL, granule);
		}
	}
}

TEST(granule, find_lock_granule_TC3)
{
	struct granule *granule;
	unsigned long addr;

	/***************************************************************
	 * TEST CASE 3:
	 *
	 * Try to find and lock a granule for a misaligned address
	 * to all possible states.
	 ***************************************************************/
	addr = get_rand_granule_addr();
	addr += test_helpers_get_rand_in_range(1UL, GRANULE_SIZE - 1);
	for (unsigned int state = GRANULE_STATE_NS;
	     state <= GRANULE_STATE_LAST; state++) {
		granule = find_lock_granule(addr,
					    (enum granule_state)state);
		POINTERS_EQUAL(NULL, granule);
	}
}

TEST(granule, find_lock_granule_TC4)
{
	struct granule *granule;
	unsigned long addr;

	/***************************************************************
	 * TEST CASE 4:
	 *
	 * Try to find and lock a granule for an address outside the
	 * valid range to all possible states.
	 ***************************************************************/
	(void)get_out_of_range_granule(&addr, true);

	for (unsigned int state = GRANULE_STATE_NS;
	     state <= GRANULE_STATE_LAST; state++) {
		granule = find_lock_granule(addr,
					    (enum granule_state)state);
		POINTERS_EQUAL(NULL, granule);

		/* Try the lower boundary as well */
		if (get_out_of_range_granule(&addr, false) == true) {

			granule = find_lock_granule(addr,
						    (enum granule_state)state);
			POINTERS_EQUAL(NULL, granule);
		}
	}
}

TEST(granule, granule_lock_TC1)
{
	struct granule *granule;
	unsigned long addrs[3] = {host_util_get_granule_base(),
				  (get_rand_granule_idx() * GRANULE_SIZE) +
					host_util_get_granule_base(),
				  ((test_helpers_get_nr_granules() - 1) *
								GRANULE_SIZE) +
					host_util_get_granule_base()};

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Get a granule and set it to a specific state. Then lock
	 * it. Repeat for every possible state.
	 * Test the first and the last valid granules as well as random
	 * granules in between.
	 ******************************************************************/
	for (unsigned int i = 0U; i < 3U; i++) {
		granule = addr_to_granule(addrs[i]);

		for (unsigned int state = GRANULE_STATE_NS;
		     state <= GRANULE_STATE_LAST; state++) {

			/* Ensure the granule is unlocked */
			granule_unlock(granule);

			/* Set the granule state */
			granule_set_state(granule, (enum granule_state)state);

			/* Lock the granule */
			granule_lock(granule, (enum granule_state)state);
			CHECK_FALSE(granule->lock.val == 0);
		}
	}

	/*
	 * granule_lock() implementation expects to always
	 * receive a valid granule hence it doesn't make any checks
	 * to ensure the correctness of the granule. Therefore, skip any tests
	 * with invalid granules.
	 *
	 * In addition to that, granule_lock() also expects that the expected
	 * state belongs to enum granule_state so it doesn't perform any checks
	 * on that either.
	 */
}

ASSERT_TEST(granule, granule_lock_TC2)
{
	struct granule *granule;
	unsigned int state, expected;
	unsigned long addr = (get_rand_granule_idx() * GRANULE_SIZE) +
					host_util_get_granule_base();

	/******************************************************************
	 * TEST CASE 2:
	 *
	 * Verify that granule_lock() asserts when the expected state of
	 * the granule does not mach the current one.
	 ******************************************************************/

	granule = addr_to_granule(addr);
	do {
		state = (unsigned int)test_helpers_get_rand_in_range(
					(unsigned long)GRANULE_STATE_NS,
					(unsigned long)GRANULE_STATE_LAST);
		expected = (unsigned int)test_helpers_get_rand_in_range(
					(unsigned long)GRANULE_STATE_NS,
					(unsigned long)GRANULE_STATE_LAST);
	} while (state == expected);

	/* Ensure the granule is unlocked */
	granule_unlock(granule);

	/* Set the granule state */
	granule_set_state(granule, (enum granule_state)state);

	test_helpers_expect_assert_fail(true);
	/* Lock the granule */
	granule_lock(granule, (enum granule_state)expected);
	test_helpers_fail_if_no_assert_failed();
}

TEST(granule, granule_lock_on_state_match_TC1)
{
	struct granule *granule;
	unsigned long addrs[3] = {host_util_get_granule_base(),
				  (get_rand_granule_idx() * GRANULE_SIZE) +
					host_util_get_granule_base(),
				  ((test_helpers_get_nr_granules() - 1) *
								GRANULE_SIZE) +
					host_util_get_granule_base()};

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Get a granule and set it to a specific state. Then lock
	 * it. Repeat for every possible state.
	 * Test the first and the last valid granules as well as random
	 * granules in between.
	 ******************************************************************/
	for (unsigned int i = 0U; i < 3U; i++) {
		granule = addr_to_granule(addrs[i]);

		for (unsigned int state = GRANULE_STATE_NS;
		     state <= GRANULE_STATE_LAST; state++) {
			bool retval;

			/* Ensure the granule is unlocked */
			granule_unlock(granule);

			/* Set the granule state */
			granule_set_state(granule, (enum granule_state)state);

			/* Lock the granule */
			retval = granule_lock_on_state_match(granule,
						(enum granule_state)state);
			CHECK(retval);
			CHECK_FALSE(granule->lock.val == 0);
		}
	}
}

TEST(granule, granule_lock_on_state_match_TC2)
{
	struct granule *granule;
	unsigned long addrs[3] = {host_util_get_granule_base(),
				  (get_rand_granule_idx() * GRANULE_SIZE) +
					host_util_get_granule_base(),
				  ((test_helpers_get_nr_granules() - 1) *
								GRANULE_SIZE) +
					host_util_get_granule_base()};

	/***************************************************************
	 * TEST CASE 2:
	 *
	 * Get a granule and for all possible states, try
	 * to lock with all possible states other than the actual
	 * one on the granule.
	 * Test the first and the last valid granules as well as random
	 * granules in between.
	 ***************************************************************/
	for (unsigned int i = 0U; i < 3U; i++) {
		granule = addr_to_granule(addrs[i]);

		for (unsigned int state = GRANULE_STATE_NS;
		     state <= GRANULE_STATE_LAST; state++) {
			/* Set the granule state */
			granule_set_state(granule, (enum granule_state)state);

			for (unsigned int lock_state = GRANULE_STATE_NS;
			     lock_state <= GRANULE_STATE_LAST; lock_state++) {
				bool retval;

				if (lock_state == state) {
					/*
					 * skip this case as it will succeed.
					 * Already tested
					 */
					continue;
				}

				/* Lock the granule */
				retval = granule_lock_on_state_match(granule,
					(enum granule_state)lock_state);
				CHECK_FALSE(retval);
				CHECK_EQUAL(0, granule->lock.val);
			}
		}
	}

	/*
	 * granule_lock_on_state_match() implementation expects to always
	 * receive a valid granule hence it doesn't make any checks
	 * to ensure the correctness of the granule. Therefore, skip any tests
	 * with invalid granules.
	 *
	 * Likewise, it also expects that the next state belongs to
	 * enum granule_state, so it doesn't perform any checks on that either.
	 */
}

TEST(granule, granule_set_get_state_TC1)
{
	struct granule *granule;
	unsigned long addrs[3] = {host_util_get_granule_base(),
				  (get_rand_granule_idx() * GRANULE_SIZE) +
					host_util_get_granule_base(),
				  ((test_helpers_get_nr_granules() - 1) *
								GRANULE_SIZE) +
					host_util_get_granule_base()};

	/***************************************************************
	 * TEST CASE 1:
	 *
	 * Find a granule and transition it through all possible
	 * states. Then check that the states are correct.
	 * Test the first and the last valid granules as well as random
	 * granules in between.
	 ***************************************************************/
	for (unsigned int i = 0U; i < 3U; i++) {
		for (unsigned int state = GRANULE_STATE_NS;
		     state <= GRANULE_STATE_LAST;
		     state++) {
			unsigned int next_state = (state + 1) %
						((int)GRANULE_STATE_LAST + 1);

			/* Find and lock a granule */
			granule = find_lock_granule(addrs[i],
						    (enum granule_state)state);

			/* Change the granule state */
			granule_set_state(granule,
					  (enum granule_state)next_state);

			/* Check that the state is correct */
			CHECK_EQUAL(next_state, granule_get_state(granule));

			/*
			 * The granule must still be locked from
			 * find_lock_granule()
			 */
			CHECK_EQUAL(1, granule->lock.val);
		}
	}

	/*
	 * granule_{set, get}_state() implementation expects to always
	 * receive a valid granule and therefore it doesn't make any checks
	 * to ensure the correctness of the granule. Therefore, skip any tests
	 * with invalid granules.
	 *
	 * Likewise, it also expects that the next state belongs to
	 * enum granule_state, so it doesn't perform any checks on that either.
	 */
}

TEST(granule, granule_unlock_TC1)
{
	struct granule *granule;
	unsigned long addrs[3] = {host_util_get_granule_base(),
				  (get_rand_granule_idx() * GRANULE_SIZE) +
					host_util_get_granule_base(),
				  ((test_helpers_get_nr_granules() - 1) *
								GRANULE_SIZE) +
					host_util_get_granule_base()};

	/***************************************************************
	 * TEST CASE 1:
	 *
	 * Find and lock a granule, then unlock it.
	 * Iterate over all possible states, making sure it can be
	 * unlocked regardless of the state and that this doesn't change.
	 * Test the first and the last valid granules as well as random
	 * granules in between.
	 ***************************************************************/
	for (unsigned int i = 0U; i < 3U; i++) {
		for (unsigned int state = GRANULE_STATE_NS;
		     state <= GRANULE_STATE_LAST;
		     state++) {

			/* Find and lock a granule */
			granule = find_lock_granule(addrs[i], GRANULE_STATE_NS);

			/* Change the state of the granule */
			granule_set_state(granule, (enum granule_state)state);

			/* Unlock the granule */
			granule_unlock(granule);

			/* Check that the state is correct */
			CHECK_EQUAL(state, granule_get_state(granule));

			/*
			 * The granule must still be locked from
			 * find_lock_granule()
			 */
			CHECK_EQUAL(0, granule->lock.val);

			/*
			 * Leave the granule in a known state for
			 * the next iteration
			 */
			granule_set_state(granule, GRANULE_STATE_NS);
		}
	}

	/*
	 * granule_unlock() implementation expects to always
	 * receive a valid granule and therefore it doesn't make any checks
	 * to ensure the correctness of the granule. Therefore, skip any tests
	 * with invalid granules.
	 */
}

TEST(granule, granule_unlock_transition_TC1)
{
	struct granule *granule;
	unsigned long addrs[3] = {host_util_get_granule_base(),
				  (get_rand_granule_idx() * GRANULE_SIZE) +
					host_util_get_granule_base(),
				  ((test_helpers_get_nr_granules() - 1) *
								GRANULE_SIZE) +
					host_util_get_granule_base()};

	/***************************************************************
	 * TEST CASE 1:
	 *
	 * Find a granule and transition it through all possible
	 * states.
	 * Test the first and the last valid granules as well as random
	 * granules in between.
	 ***************************************************************/
	for (unsigned int i = 0U; i < 3U; i++) {
		for (unsigned int state = GRANULE_STATE_NS;
		     state <= GRANULE_STATE_LAST;
		     state++) {
			unsigned int next_state = (state + 1) %
						((int)GRANULE_STATE_LAST + 1);

			/* Find and lock a granule */
			granule = find_lock_granule(addrs[i],
						    (enum granule_state)state);

			/* Unlock the granule changing its state */
			granule_unlock_transition(granule,
					(enum granule_state)next_state);

			/* Check that the state is correct */
			CHECK_EQUAL(next_state, granule_get_state(granule));
			CHECK_EQUAL(0, granule->lock.val);
		}
	}

	/*
	 * granule_unlock_transition() implementation expects to always
	 * receive a valid granule and therefore it doesn't make any checks
	 * to ensure the correctness of the granule. Therefore, skip any tests
	 * with invalid granules.
	 *
	 * Likewise, it also expects that the next state belongs to
	 * enum granule_state, so it doesn't perform any checks on that either.
	 */
}

TEST(granule, granule_get_TC1)
{
	unsigned long address = get_rand_granule_addr();
	struct granule *granule = find_granule(address);
	unsigned int lock = set_rand_non_zero_lock_value(granule);

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Increase the refcount of a granule by invoking __granule_get().
	 * The refcount before the call is expected to be 0.
	 ******************************************************************/
	__granule_get(granule);

	CHECK_EQUAL(1UL, granule->refcount);

	/* Verify that not other parameters of the granule are altered */
	CHECK_EQUAL(0, granule->state);
	CHECK_EQUAL(lock, granule->lock.val);

	/*
	 * __granule_get() doesn't make any check to validate the granule
	 * pointer passed, so skip the testcase for NULL pointer.
	 */
}

TEST(granule, granule_put_TC1)
{
	unsigned long address = get_rand_granule_addr();
	struct granule *granule = find_granule(address);
	unsigned int lock = set_rand_non_zero_lock_value(granule);

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Increase the refcount of a granule by invoking __granule_get(),
	 * then decrease it again with __granule_put().
	 *
	 * The refcount before the test starts is expected to be 0.
	 ******************************************************************/
	__granule_get(granule);
	__granule_put(granule);

	CHECK_EQUAL(0UL, granule->refcount);

	/* Verify that not other parameters of the granule are altered */
	CHECK_EQUAL(0, granule->state);
	CHECK_EQUAL(lock, granule->lock.val);
}

TEST(granule, granule_put_TC2)
{
	unsigned long address = get_rand_granule_addr();
	struct granule *granule = find_granule(address);
	unsigned int get_count;
	unsigned int lock = set_rand_non_zero_lock_value(granule);

	/******************************************************************
	 * TEST CASE 2:
	 *
	 * Increase the refcount of a granule by invoking __granule_get()
	 * a random number of times, then decrease it again with
	 * __granule_put() only once.
	 *
	 * The refcount before the test starts is expected to be 0.
	 ******************************************************************/
	get_count = (unsigned int)test_helpers_get_rand_in_range(10UL, 1000UL);
	for (unsigned int i = 0; i < get_count; i++) {
		__granule_get(granule);
	}
	__granule_put(granule);

	LONGS_EQUAL((get_count - 1UL), granule->refcount);

	/* Verify that not other parameters of the granule are altered */
	CHECK_EQUAL(0, granule->state);
	CHECK_EQUAL(lock, granule->lock.val);

	/*
	 * __granule_put() doesn't make any check to validate the granule
	 * pointer passed, so skip the testcase for NULL pointer.
	 */
}

TEST(granule, granule_refcount_inc_TC1)
{
	unsigned long address = get_rand_granule_addr();
	struct granule *granule = find_granule(address);
	unsigned long val = test_helpers_get_rand_in_range(1UL, INT_MAX);

	unsigned int lock = set_rand_non_zero_lock_value(granule);

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Increase the refcount of a granule by invoking __granule_inc().
	 * The refcount before the call is expected to be 0.
	 ******************************************************************/
	__granule_refcount_inc(granule, val);

	CHECK_EQUAL(val, granule->refcount);

	/* Verify that not other parameters of the granule are altered */
	CHECK_EQUAL(0, granule->state);
	CHECK_EQUAL(lock, granule->lock.val);

	/*
	 * __granule_refcount_inc() doesn't make any check to validate
	 * the granule pointer passed, so skip the testcase for NULL pointer.
	 */
}

TEST(granule, granule_refcount_dec_TC1)
{
	unsigned long address = get_rand_granule_addr();
	struct granule *granule = find_granule(address);
	unsigned long val = test_helpers_get_rand_in_range(10UL, INT_MAX);

	unsigned int lock = set_rand_non_zero_lock_value(granule);

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Increase the refcount of a granule by invoking
	 * __granule_refcount_inc(), then decrease it again with
	 * __granule_refcount_dec().
	 *
	 * The refcount before the test starts is expected to be 0.
	 ******************************************************************/
	__granule_refcount_inc(granule, val);
	__granule_refcount_dec(granule, val);

	LONGS_EQUAL(0, granule->refcount);

	/* Verify that not other parameters of the granule are altered */
	CHECK_EQUAL(0, granule->state);
	CHECK_EQUAL(lock, granule->lock.val);
}

TEST(granule, granule_refcount_dec_TC2)
{
	unsigned long address = get_rand_granule_addr();
	struct granule *granule = find_granule(address);
	unsigned long val = test_helpers_get_rand_in_range(10UL, INT_MAX);

	unsigned int lock = set_rand_non_zero_lock_value(granule);

	/******************************************************************
	 * TEST CASE 2:
	 *
	 * Increase the refcount of a granule by invoking
	 * __granule_refcount_inc(), then decrease it again with
	 * __granule_refcount_dec() but using a lower value than the one
	 * used for inc.
	 *
	 * The refcount before the test starts is expected to be 0.
	 ******************************************************************/
	__granule_refcount_inc(granule, val);
	__granule_refcount_dec(granule, val - 1UL);

	LONGS_EQUAL(1, granule->refcount);

	/* Verify that not other parameters of the granule are altered */
	CHECK_EQUAL(0, granule->state);
	CHECK_EQUAL(lock, granule->lock.val);

	/*
	 * __granule_refcount_dec() doesn't make any check to validate
	 * the granule pointer passed, so skip the testcase for NULL pointer.
	 */
}

ASSERT_TEST(granule, granule_refcount_dec_TC3)
{
	unsigned long address = get_rand_granule_addr();
	struct granule *granule = find_granule(address);
	unsigned long val = test_helpers_get_rand_in_range(10UL, INT_MAX - 1U);

	set_rand_non_zero_lock_value(granule);

	/******************************************************************
	 * TEST CASE 3:
	 *
	 * Verify that granule_refcount_dec() asserts when the granule
	 * refcount is lower than the value passed.
	 ******************************************************************/

	__granule_refcount_inc(granule, val);
	test_helpers_expect_assert_fail(true);
	__granule_refcount_dec(granule, val + 1UL);
	test_helpers_fail_if_no_assert_failed();
}

TEST(granule, atomic_granule_get_TC1)
{
	unsigned long address = get_rand_granule_addr();
	struct granule *granule = find_granule(address);

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Increase the refcount of a granule by invoking
	 * atomic_granule_get().
	 * The refcount before the call is expected to be 0.
	 ******************************************************************/
	atomic_granule_get(granule);

	LONGS_EQUAL(1, granule->refcount);

	/* Verify that not other parameters of the granule are altered */
	CHECK_EQUAL(0, granule->state);
	CHECK_EQUAL(0, granule->lock.val);

	/*
	 * atomic_granule_get doesn't make any check to validate the granule
	 * pointer passed, so skip the testcase for NULL pointer.
	 */
}

TEST(granule, atomic_granule_put_TC1)
{
	unsigned long address = get_rand_granule_addr();
	struct granule *granule = find_granule(address);

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Increase the refcount of a granule by invoking atomic_granule_get,
	 * then decrease it again with atomic_granule_put().
	 *
	 * The refcount before the test starts is expected to be 0.
	 ******************************************************************/
	atomic_granule_get(granule);
	atomic_granule_put(granule);

	LONGS_EQUAL(0, granule->refcount);

	/* Verify that not other parameters of the granule are altered */
	CHECK_EQUAL(0, granule->state);
	CHECK_EQUAL(0, granule->lock.val);
}

TEST(granule, atomic_granule_put_TC2)
{
	unsigned long address = get_rand_granule_addr();
	struct granule *granule = find_granule(address);
	unsigned int get_count;

	/******************************************************************
	 * TEST CASE 2:
	 *
	 * Increase the refcount of a granule by invoking atomic_granule_get()
	 * a random number of times, then decrease it again with
	 * atomic_granule_put() only once.
	 *
	 * The refcount before the test starts is expected to be 0.
	 ******************************************************************/
	get_count = (unsigned int)test_helpers_get_rand_in_range(10UL, 1000UL);
	for (unsigned int i = 0; i < get_count; i++) {
		atomic_granule_get(granule);
	}
	atomic_granule_put(granule);

	LONGS_EQUAL((get_count - 1UL), granule->refcount);

	/* Verify that not other parameters of the granule are altered */
	CHECK_EQUAL(0, granule->state);
	CHECK_EQUAL(0, granule->lock.val);

	/*
	 * atomic_granule_put() doesn't make any check to validate the granule
	 * pointer passed, so skip the testcase for NULL pointer.
	 */
}

TEST(granule, atomic_granule_put_release_TC1)
{
	unsigned long address = get_rand_granule_addr();
	struct granule *granule = find_granule(address);

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Increase the refcount of a granule by invoking atomic_granule_get,
	 * then decrease it again with atomic_granule_put_release().
	 *
	 * The refcount before the test starts is expected to be 0.
	 ******************************************************************/
	atomic_granule_get(granule);
	atomic_granule_put_release(granule);

	LONGS_EQUAL(0, granule->refcount);

	/* Verify that not other parameters of the granule are altered */
	CHECK_EQUAL(0, granule->state);
	CHECK_EQUAL(0, granule->lock.val);
}

TEST(granule, atomic_granule_put_release_TC2)
{
	unsigned long address = get_rand_granule_addr();
	struct granule *granule = find_granule(address);
	unsigned int get_count;

	/******************************************************************
	 * TEST CASE 2:
	 *
	 * Increase the refcount of a granule by invoking atomic_granule_get()
	 * a random number of times, then decrease it again
	 * with atomic_granule_put_releae() only once.
	 *
	 * The refcount before the test starts is expected to be 0.
	 ******************************************************************/
	get_count = (unsigned int)test_helpers_get_rand_in_range(10UL, 1000UL);
	for (unsigned int i = 0; i < get_count; i++) {
		atomic_granule_get(granule);
	}
	atomic_granule_put_release(granule);

	LONGS_EQUAL((get_count - 1UL), granule->refcount);

	/* Verify that not other parameters of the granule are altered */
	CHECK_EQUAL(0, granule->state);
	CHECK_EQUAL(0, granule->lock.val);

	/*
	 * atomic_granule_put_release() doesn't make any check to validate
	 * the granule pointer passed, so skip the testcase for NULL pointer.
	 */
}

ASSERT_TEST(granule, atomic_granule_put_release_TC3)
{
	unsigned long address = get_rand_granule_addr();
	struct granule *granule = find_granule(address);

	/******************************************************************
	 * TEST CASE 3:
	 *
	 * Verify that atomic_granule_put_release() asserts if refcount
	 * reaches a value < 0;
	 ******************************************************************/

	test_helpers_expect_assert_fail(true);
	atomic_granule_put_release(granule);
	test_helpers_fail_if_no_assert_failed();
}

TEST(granule, find_lock_unused_granule_TC1)
{
	struct granule *granule;
	unsigned long addrs[3] = {host_util_get_granule_base(),
				  (get_rand_granule_idx() * GRANULE_SIZE) +
					host_util_get_granule_base(),
				  ((test_helpers_get_nr_granules() - 1) *
								GRANULE_SIZE) +
					host_util_get_granule_base()};

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Find and lock a granule and verify that it is on
	 * the right state (granules should be in GRANULE_STATE_DELEGATED)
	 * by default, as well as refcount and lock status.
	 * Test the first and the last valid granules as well as random
	 * granules in between.
	 ******************************************************************/

	for (unsigned int i = 0U; i < 3U; i++) {
		int ret;

		/* Find and lock the granule */
		granule = find_lock_granule(addrs[i], GRANULE_STATE_NS);

		/* Change status to avoid assertions on invariants checks */
		granule->state = GRANULE_STATE_RD;

		granule = NULL;
		ret = find_lock_unused_granule(addrs[i], GRANULE_STATE_RD, &granule);

		CHECK_TRUE(ret == 0);
		CHECK_FALSE(granule == NULL);
		CHECK_FALSE(granule->lock.val == 0UL);
		LONGS_EQUAL(0, granule->refcount);
	}
}

TEST(granule, find_lock_unused_granule_TC2)
{
	struct granule *granule;
	unsigned long addrs[3] = {host_util_get_granule_base(),
				  (get_rand_granule_idx() * GRANULE_SIZE) +
					host_util_get_granule_base(),
				  ((test_helpers_get_nr_granules() - 1) *
								GRANULE_SIZE) +
					host_util_get_granule_base()};

	/***************************************************************
	 * TEST CASE 2:
	 *
	 * Try to find and lock a granule with the wrong expected state.
	 * Test the first and the last valid granules as well as random
	 * granules in between.
	 ***************************************************************/

	for (unsigned int i = 0U; i < 3U; i++) {
		int ret;

		granule = find_granule(addrs[i]);

		/*
		 * Start the test with a granule in the same state as at the
		 * end of the previous test
		 */
		granule_set_state(granule, GRANULE_STATE_RD);

		for (unsigned int state = GRANULE_STATE_NS;
			state <= GRANULE_STATE_LAST; state++) {
			if (state == GRANULE_STATE_RD) {
				/* Skip as the state is the correct one */
				continue;
			}

			ret = find_lock_unused_granule(addrs[i],
						(enum granule_state)state,
						&granule);

			CHECK_TRUE(ret == -EINVAL);
			CHECK_TRUE(granule == NULL);
		}
	}
}

TEST(granule, find_lock_unused_granule_TC3)
{
	struct granule *granule;
	unsigned long addrs[3] = {host_util_get_granule_base(),
				  (get_rand_granule_idx() * GRANULE_SIZE) +
					host_util_get_granule_base(),
				  ((test_helpers_get_nr_granules() - 1) *
								GRANULE_SIZE) +
					host_util_get_granule_base()};

	/***************************************************************
	 * TEST CASE 3:
	 *
	 * Try to find and lock an used granule.
	 * Test the first and the last valid granules as well as random
	 * granules in between.
	 ***************************************************************/

	for (unsigned int i = 0U; i < 3U; i++) {
		int ret;

		/*
		 * Increase the refcount of the current granule to mark it
		 * as used.
		 */
		granule = addr_to_granule(addrs[i]);
		granule->refcount = 10UL;
		granule_set_state(granule, GRANULE_STATE_RD);

		ret = find_lock_unused_granule(addrs[i], GRANULE_STATE_RD,
						&granule);

		CHECK_TRUE(ret == -EBUSY);
		CHECK_TRUE(granule == NULL);
	}
}

TEST(granule, find_lock_unused_granule_TC4)
{
	struct granule *granule;
	unsigned long addr;
	int ret;

	/***************************************************************
	 * TEST CASE 4:
	 *
	 * Try to find and lock a granule for a misaligned address.
	 ***************************************************************/
	addr = get_rand_granule_addr();
	addr += test_helpers_get_rand_in_range(1UL, GRANULE_SIZE - 1);
	ret = find_lock_unused_granule(addr, GRANULE_STATE_NS, &granule);

	CHECK_TRUE(ret == -EINVAL);
	CHECK_TRUE(granule == NULL);
}

TEST(granule, find_lock_unused_granule_TC5)
{
	struct granule *granule;
	unsigned long addr;
	int ret;

	/***************************************************************
	 * TEST CASE 5:
	 *
	 * Try to find and lock a granule for an address outside the
	 * valid range.
	 ***************************************************************/
	(void)get_out_of_range_granule(&addr, true);
	ret = find_lock_unused_granule(addr, GRANULE_STATE_NS, &granule);

	CHECK_TRUE(ret == -EINVAL);
	CHECK_TRUE(granule == NULL);

	/* Try with the lower boundary as well if possible */
	if (get_out_of_range_granule(&addr, false) == true) {
		ret = find_lock_unused_granule(addr, GRANULE_STATE_NS,
						&granule);

		CHECK_TRUE(ret == -EINVAL);
		CHECK_TRUE(granule == NULL);
	}
}

TEST(granule, granule_memzero_TC1)
{
	unsigned long addrs[3] = {host_util_get_granule_base(),
				  (get_rand_granule_idx() * GRANULE_SIZE) +
					host_util_get_granule_base(),
				  ((test_helpers_get_nr_granules() - 1) *
								GRANULE_SIZE) +
					host_util_get_granule_base()};
	struct granule *granule;
	int *val;
	union test_harness_cbs cb;

	/* Register harness callbacks to use by this test */
	cb.buffer_map = test_buffer_map_access;
	(void)test_helpers_register_cb(cb, CB_BUFFER_MAP);
	cb.buffer_unmap = test_buffer_unmap_access;
	(void)test_helpers_register_cb(cb, CB_BUFFER_UNMAP);

	/***************************************************************
	 * TEST CASE 1:
	 *
	 * Map a granule to every possible slot type and memzero
	 * it. Verify then that the whole slot buffer is all 0.
	 * Test the first and the last valid granules as well as random
	 * granules in between.
	 * Repeat the operation on all possible CPUs.
	 *
	 * NOTE: granule_memzero() will fail with SLOT_NS, so skip that
	 *	 testcase.
	 ***************************************************************/

	for (unsigned int i = 0U; i < 3U; i++) {
		granule = addr_to_granule(addrs[i]);
		val = (int *)addrs[i];

		for (unsigned int j = 0U; j < MAX_CPUS; j++) {
			/* Configure the cpu id */
			host_util_set_cpuid(j);

			for (unsigned int k = 0; k < NR_CPU_SLOTS; k++) {
				if (k == SLOT_NS) {
					/* Not supported by granule_memzero */
					continue;
				}

				/* Initialize the granule with random data */
				memset((void *)addrs[i],
					(int)test_helpers_get_rand_in_range(1UL, INT_MAX),
					GRANULE_SIZE);
				granule_memzero(granule, (enum buffer_slot)k);

				for (unsigned int l = 0;
				     l < (GRANULE_SIZE / sizeof(int)); l++) {
					if (*(val + l) != 0) {
						FAIL_TEST("Memory not properly zeroed");
					}
				} /* GRANULE_SIZE */
			} /* NR_CPU_SLOTS */
		} /* MAX_CPUS */
	} /* Number of granules to test */
}

ASSERT_TEST(granule, granule_memzero_TC2)
{
	/***************************************************************
	 * TEST CASE 2:
	 *
	 * Verify that granule_memzero() asserts if granule is NULL
	 ***************************************************************/

	test_helpers_expect_assert_fail(true);
	granule_memzero(NULL, SLOT_DELEGATED);
	test_helpers_fail_if_no_assert_failed();
}

TEST(granule, granule_memzero_mapped_TC1)
{
	/*
	 * Current implementation for granule_memzero_mapped()
	 * is a wrapper for memset, so skip this test for now.
	 */
}
