/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <CppUTest/CommandLineTestRunner.h>
#include <CppUTest/TestHarness.h>

extern "C" {
#include <buffer.h>
#include <cpuid.h>
#include <dev_granule.h>
#include <granule.h>	/* Interface to exercise */
#include <host_harness.h>
#include <host_utils.h>
#include <status.h>
#include <stdlib.h>
#include <string.h>
#include <test_helpers.h>
#include <tracking_region_lock.h>
#include <tracking_region_pvt.h>
#include <utils_def.h>
}

#define SHORTS_EQUAL(expected, actual)	\
	LONGS_EQUAL((expected) & 0xffff, (actual) & 0xffff)

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
 * Function to generate an invalid granule address outside the valid range.
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

/* Function to set granule refcount field */
static void granule_set_refcount(struct granule *granule, unsigned short val)
{
	assert(val <= REFCOUNT_MAX);
	granule->descriptor &= ~(unsigned short)MASK(GRN_REFCOUNT);
	granule->descriptor |= val;
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
		 * Unregister any existing callback that might
		 * have been installed
		 */
		(void)test_helpers_unregister_cb(CB_BUFFER_MAP);
		(void)test_helpers_unregister_cb(CB_BUFFER_UNMAP);
		(void)test_helpers_unregister_cb(CB_BUFFER_VA_TO_SLOT);
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
		/* Calculated the expected PA for the granule */
		addr = (granule_indexes[i] * GRANULE_SIZE) +
						host_util_get_granule_base();
		granule = tr_addr_to_granule(addr);
		expected_granule = tr_find_fine_granule(addr);
		POINTERS_EQUAL(expected_granule, granule);
		UNSIGNED_LONGS_EQUAL(addr, tr_granule_addr(granule));
	}
}

ASSERT_TEST(granule, addr_to_granule_TC2)
{
	/******************************************************************
	 * TEST CASE 2:
	 *
	 * Verify that tr_addr_to_granule() asserts when the address is a
	 * NULL pointer
	 ******************************************************************/

	test_helpers_expect_assert_fail(true);
	(void)tr_addr_to_granule((unsigned long)NULL);
	test_helpers_fail_if_no_assert_failed();
}

ASSERT_TEST(granule, addr_to_granule_TC3)
{
	unsigned long addr = get_rand_granule_addr();

	/******************************************************************
	 * TEST CASE 3:
	 *
	 * Verify that tr_addr_to_granule() asserts with an unaligned address
	 ******************************************************************/

	addr += test_helpers_get_rand_in_range(1UL, GRANULE_SIZE - 2U);

	test_helpers_expect_assert_fail(true);
	(void)tr_addr_to_granule(addr);
	test_helpers_fail_if_no_assert_failed();
}

ASSERT_TEST(granule, addr_to_granule_TC4)
{
	unsigned long addr = 0;

	/******************************************************************
	 * TEST CASE 4:
	 *
	 * Verify that tr_addr_to_granule() asserts with an address below
	 * the valid range
	 ******************************************************************/

	/* Check an address below the valid range */
	(void)get_out_of_range_granule(&addr, false);
	test_helpers_expect_assert_fail(true);
	(void)tr_addr_to_granule(addr);
	test_helpers_fail_if_no_assert_failed();
}

ASSERT_TEST(granule, addr_to_granule_TC5)
{
	unsigned long addr;

	/******************************************************************
	 * TEST CASE 5:
	 *
	 * Verify that tr_addr_to_granule() asserts with an address over
	 * the valid range
	 ******************************************************************/

	/* Check an address over the valid range */
	(void)get_out_of_range_granule(&addr, true);
	test_helpers_expect_assert_fail(true);
	(void)tr_addr_to_granule(addr);
	test_helpers_fail_if_no_assert_failed();
}

TEST(granule, device_lookup_valid)
{
	unsigned long addr = host_util_get_dev_granule_base();
	enum dev_coh_type type = DEV_MEM_COHERENT;
	struct dev_granule *g = tr_addr_to_dev_granule(addr, &type);

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Verify that tr_addr_to_dev_granule() returns the fine struct dev_granule
	 * and non-coherent memory type for a valid device physical address.
	 * Check that the struct dev_granule converts back to the original address.
	 ******************************************************************/

	CHECK(g != NULL);
	LONGS_EQUAL(DEV_MEM_NON_COHERENT, type);
	UNSIGNED_LONGS_EQUAL(addr, tr_dev_granule_addr(g, type));
}

ASSERT_TEST(granule, device_lookup_invalid)
{
	enum dev_coh_type type = DEV_MEM_COHERENT;

	/******************************************************************
	 * TEST CASE 2:
	 *
	 * Verify that tr_addr_to_dev_granule() asserts when a Granule-aligned
	 * address belongs to conventional memory instead of a device bank.
	 ******************************************************************/

	test_helpers_expect_assert_fail(true);
	(void)tr_addr_to_dev_granule(host_util_get_granule_base(), &type);
	test_helpers_fail_if_no_assert_failed();
}

TEST(granule, fine_run_state_boundary)
{
	unsigned long addr = round_up(host_util_get_granule_base(),
				      tracking_region_get_size());
	struct granule *boundary = tr_addr_to_granule(addr + (2UL * GRANULE_SIZE));
	unsigned long count;
	unsigned long ret;

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Verify that tr_find_lock_fine_granule_run() locks the NS prefix
	 * before a DELEGATED granule and leaves that granule unlocked.
	 * Starting at the DELEGATED granule must return RMI_ERROR_INPUT
	 * with a zero count and no locks held.
	 ******************************************************************/

	granule_lock(boundary, GRANULE_STATE_NS);
	granule_unlock_transition(boundary, GRANULE_STATE_DELEGATED);
	ret = tr_find_lock_fine_granule_run(addr, addr + (3UL * GRANULE_SIZE),
					  GRANULE_STATE_NS, &count);
	UNSIGNED_LONGS_EQUAL(RMI_SUCCESS, ret);
	UNSIGNED_LONGS_EQUAL(2UL, count);
	CHECK_FALSE(LOCKED(boundary));
	for (unsigned long i = 0UL; i < count; i++) {
		struct granule *g = tr_addr_to_granule(addr + (i * GRANULE_SIZE));

		CHECK(LOCKED(g));
		granule_unlock(g);
	}

	ret = tr_find_lock_fine_granule_run(addr + (2UL * GRANULE_SIZE),
					  addr + (3UL * GRANULE_SIZE),
					  GRANULE_STATE_NS, &count);
	UNSIGNED_LONGS_EQUAL(RMI_ERROR_INPUT, ret);
	UNSIGNED_LONGS_EQUAL(0UL, count);
	CHECK_FALSE(LOCKED(boundary));
	granule_lock(boundary, GRANULE_STATE_DELEGATED);
	granule_unlock_transition(boundary, GRANULE_STATE_NS);
}

TEST(granule, fine_device_run_state_boundary)
{
	unsigned long addr = host_util_get_dev_granule_base();
	unsigned long region_top = round_up(addr + GRANULE_SIZE,
					    tracking_region_get_size());
	enum dev_coh_type type;
	struct dev_granule *boundary;
	unsigned long count;
	unsigned long ret;

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Verify that tr_find_lock_fine_dev_granule_run() locks the NS prefix
	 * before a DELEGATED device granule and reports its coherency type.
	 * The DELEGATED granule must remain unlocked. Starting at that
	 * granule must return RMI_ERROR_INPUT with a zero count and no
	 * locks held.
	 ******************************************************************/

	/* Keep all three pages in one region without skipping the small bank. */
	if ((region_top - addr) < (3UL * GRANULE_SIZE)) {
		addr = region_top;
	}
	boundary = tr_addr_to_dev_granule(addr + (2UL * GRANULE_SIZE), &type);
	CHECK(boundary != NULL);
	dev_granule_lock(boundary, DEV_GRANULE_STATE_NS);
	dev_granule_unlock_transition(boundary, DEV_GRANULE_STATE_DELEGATED);
	ret = tr_find_lock_fine_dev_granule_run(addr, addr + (3UL * GRANULE_SIZE),
					      DEV_GRANULE_STATE_NS, &type, &count);
	UNSIGNED_LONGS_EQUAL(RMI_SUCCESS, ret);
	UNSIGNED_LONGS_EQUAL(2UL, count);
	LONGS_EQUAL(DEV_MEM_NON_COHERENT, type);
	CHECK_FALSE(DEV_LOCKED(boundary));
	for (unsigned long i = 0UL; i < count; i++) {
		struct dev_granule *g = tr_addr_to_dev_granule(
						addr + (i * GRANULE_SIZE), &type);

		CHECK(DEV_LOCKED(g));
		dev_granule_unlock(g);
	}

	ret = tr_find_lock_fine_dev_granule_run(addr + (2UL * GRANULE_SIZE),
					      addr + (3UL * GRANULE_SIZE),
					      DEV_GRANULE_STATE_NS, &type, &count);
	UNSIGNED_LONGS_EQUAL(RMI_ERROR_INPUT, ret);
	UNSIGNED_LONGS_EQUAL(0UL, count);
	CHECK_FALSE(DEV_LOCKED(boundary));
	dev_granule_lock(boundary, DEV_GRANULE_STATE_DELEGATED);
	dev_granule_unlock_transition(boundary, DEV_GRANULE_STATE_NS);
}

TEST(granule, atomic_granule_get_TC1)
{
	unsigned long address = get_rand_granule_addr();
	struct granule *granule = tr_find_fine_granule(address);

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Increase the refcount of a granule by invoking
	 * atomic_granule_get().
	 * The refcount before the call is expected to be 0.
	 ******************************************************************/
	granule_bitlock_acquire(granule);

	atomic_granule_get(granule);

	SHORTS_EQUAL(1U, granule_refcount_read(granule));

	granule_bitlock_release(granule);

	/* Verify that not other parameters of the granule are altered */
	CHECK_FALSE(is_granule_locked(granule));
	CHECK_EQUAL(0U, granule_unlocked_state(granule));
}

ASSERT_TEST(granule, atomic_granule_get_TC2)
{
	/******************************************************************
	 * TEST CASE 2:
	 *
	 * Verify that atomic_granule_get() asserts when a granule pointer
	 * is NULL.
	 ******************************************************************/

	test_helpers_expect_assert_fail(true);
	atomic_granule_get(NULL);
	test_helpers_fail_if_no_assert_failed();
}

TEST(granule, atomic_granule_put_TC1)
{
	unsigned long address = get_rand_granule_addr();
	struct granule *granule = tr_find_fine_granule(address);

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Increase the refcount of a granule by invoking atomic_granule_get,
	 * then decrease it again with atomic_granule_put().
	 *
	 * The refcount before the test starts is expected to be 0.
	 ******************************************************************/
	granule_bitlock_acquire(granule);

	atomic_granule_get(granule);
	atomic_granule_put(granule);

	SHORTS_EQUAL(0U, granule_refcount_read(granule));

	granule_bitlock_release(granule);

	/* Verify that not other parameters of the granule are altered */
	CHECK_FALSE(is_granule_locked(granule));
	CHECK_EQUAL(0U, granule_unlocked_state(granule));
}

TEST(granule, atomic_granule_put_TC2)
{
	unsigned long address = get_rand_granule_addr();
	struct granule *granule = tr_find_fine_granule(address);
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
	granule_bitlock_acquire(granule);

	get_count = (unsigned int)test_helpers_get_rand_in_range(10UL, REFCOUNT_MAX);
	for (unsigned int i = 0; i < get_count; i++) {
		atomic_granule_get(granule);
	}

	atomic_granule_put(granule);

	SHORTS_EQUAL((get_count - 1U), granule_refcount_read(granule));

	granule_bitlock_release(granule);

	/* Verify that not other parameters of the granule are altered */
	CHECK_FALSE(is_granule_locked(granule));
	CHECK_EQUAL(0U, granule_unlocked_state(granule));
}

ASSERT_TEST(granule, atomic_granule_put_TC3)
{
	/******************************************************************
	 * TEST CASE 3:
	 *
	 * Verify atomic_granule_put() asserts when a granule
	 * pointer is NULL.
	 ******************************************************************/

	test_helpers_expect_assert_fail(true);
	atomic_granule_put(NULL);
	test_helpers_fail_if_no_assert_failed();
}

TEST(granule, atomic_granule_put_release_TC1)
{
	unsigned long address = get_rand_granule_addr();
	struct granule *granule = tr_find_fine_granule(address);

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Increase the refcount of a granule by invoking atomic_granule_get(),
	 * then decrease it again with atomic_granule_put_release().
	 *
	 * The refcount before the test starts is expected to be 0.
	 ******************************************************************/
	granule_bitlock_acquire(granule);

	atomic_granule_get(granule);
	atomic_granule_put_release(granule);

	SHORTS_EQUAL(0U, granule_refcount_read(granule));

	granule_bitlock_release(granule);

	/* Verify that not other parameters of the granule are altered */
	CHECK_FALSE(is_granule_locked(granule));
	CHECK_EQUAL(0U, granule_unlocked_state(granule));
}

TEST(granule, atomic_granule_put_release_TC2)
{
	unsigned long address = get_rand_granule_addr();
	struct granule *granule = tr_find_fine_granule(address);
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
	granule_bitlock_acquire(granule);

	get_count = (unsigned short)test_helpers_get_rand_in_range(10UL, REFCOUNT_MAX);
	for (unsigned int i = 0U; i < get_count; i++) {
		atomic_granule_get(granule);
	}
	atomic_granule_put_release(granule);

	SHORTS_EQUAL((get_count - 1U), granule_refcount_read(granule));

	granule_bitlock_release(granule);

	/* Verify that not other parameters of the granule are altered */
	CHECK_FALSE(is_granule_locked(granule));
	CHECK_EQUAL(0U, granule_unlocked_state(granule));
}

ASSERT_TEST(granule, atomic_granule_put_release_TC3)
{
	unsigned long address = get_rand_granule_addr();
	struct granule *granule = tr_find_fine_granule(address);

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

ASSERT_TEST(granule, atomic_granule_put_release_TC4)
{
	/******************************************************************
	 * TEST CASE 4:
	 *
	 * Verify atomic_granule_put_release() asserts when a granule
	 * pointer is NULL.
	 ******************************************************************/

	test_helpers_expect_assert_fail(true);
	atomic_granule_put_release(NULL);
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
	 * returned by tr_granule_addr() matches the manually calculated one.
	 * Test the first and the last valid granules as well as random
	 * granules in between.
	 ******************************************************************/
	for (unsigned int i = 0U; i < 3U; i++) {
		expected_address = (granule_indexes[i] * GRANULE_SIZE) +
						host_util_get_granule_base();
		granule = tr_addr_to_granule(expected_address);
		addr = tr_granule_addr(granule);
		POINTERS_EQUAL(expected_address, addr);

		/*
		 * Verify that not other parameters of the granule
		 * are altered
		 */
		CHECK_EQUAL(0U, granule_unlocked_state(granule));
		CHECK_FALSE(is_granule_locked(granule));
	}
}

ASSERT_TEST(granule, granule_addr_TC2)
{
	/******************************************************************
	 * TEST CASE 2:
	 *
	 * Verify that tr_granule_addr() asserts with a NULL address
	 ******************************************************************/

	test_helpers_expect_assert_fail(true);
	(void)tr_granule_addr(NULL);
	test_helpers_fail_if_no_assert_failed();
}

ASSERT_TEST(granule, granule_addr_TC3)
{
	struct granule *granule;
	unsigned long addr;

	/******************************************************************
	 * TEST CASE 3:
	 *
	 * Verify that tr_granule_addr() asserts for the struct granule immediately
	 * after the one representing the last valid platform Granule.
	 ******************************************************************/

	addr = host_util_get_granule_base() +
		((unsigned long)get_last_granule_idx() * GRANULE_SIZE);
	granule = tr_addr_to_granule(addr) + 1U;
	test_helpers_expect_assert_fail(true);
	(void)tr_granule_addr(granule);
	test_helpers_fail_if_no_assert_failed();
}

ASSERT_TEST(granule, granule_addr_TC4)
{
	struct granule *granule;

	/******************************************************************
	 * TEST CASE 4:
	 *
	 * Verify that tr_granule_addr() asserts if the granule address <
	 * granule[0];
	 ******************************************************************/

	granule = test_helpers_granule_struct_base() - 1U;
	test_helpers_expect_assert_fail(true);
	(void)tr_granule_addr(granule);
	test_helpers_fail_if_no_assert_failed();

}

ASSERT_TEST(granule, granule_addr_TC5)
{
	uintptr_t granule;

	/******************************************************************
	 * TEST CASE 5:
	 *
	 * Verify that tr_granule_addr() asserts if the granule address is
	 * not properly aligned.
	 ******************************************************************/

	granule = (uintptr_t)test_helpers_granule_struct_base();
	granule += test_helpers_get_rand_in_range(1UL,
					sizeof(struct granule) - 1U);
	test_helpers_expect_assert_fail(true);
	(void)tr_granule_addr((struct granule *)granule);
	test_helpers_fail_if_no_assert_failed();
}

TEST(granule, granule_refcount_read_TC1)
{
	struct granule *granule;
	unsigned long addr = get_rand_granule_addr();
	unsigned short val =
		(unsigned short)test_helpers_get_rand_in_range(1UL, REFCOUNT_MAX);
	unsigned short read_val;

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Set the refcount for a granule manually and verify with
	 * granule_refcount_read() that the status is correct.
	 ******************************************************************/
	granule = tr_addr_to_granule(addr);

	/* Set the refcount */
	granule_set_refcount(granule, val);

	/* Read the value */
	read_val = granule_refcount_read(granule);
	CHECK_EQUAL(val, read_val);

	/* Verify that not other parameters of the granule are altered */
	CHECK_EQUAL(0U, granule_unlocked_state(granule));
	CHECK_FALSE(is_granule_locked(granule));
}

ASSERT_TEST(granule, granule_refcount_read_TC2)
{
	/******************************************************************
	 * TEST CASE 2:
	 *
	 * Verify that granule_refcount_read() asserts when a granule
	 * pointer is NULL.
	 ******************************************************************/

	test_helpers_expect_assert_fail(true);

	/* Read the value */
	(void)granule_refcount_read(NULL);
	test_helpers_fail_if_no_assert_failed();
}

TEST(granule, granule_refcount_read_acquire_TC1)
{
	struct granule *granule;
	unsigned long addr = get_rand_granule_addr();
	unsigned short val =
		(unsigned short)test_helpers_get_rand_in_range(10UL, REFCOUNT_MAX);
	unsigned short read_val;

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Set the refcount for a granule manually and verify with
	 * granule_refcount_read_acquire() that the status is correct.
	 ******************************************************************/
	granule = tr_addr_to_granule(addr);

	/* Lock the granule */
	granule_bitlock_acquire(granule);

	/* Set the refcount */
	granule_set_refcount(granule, val);

	/* Read the value */
	read_val = granule_refcount_read_acquire(granule);
	CHECK_EQUAL(val, read_val);

	/* Unlock the granule */
	granule_bitlock_release(granule);

	/* Verify that not other parameters of the granule are altered */
	CHECK_FALSE(is_granule_locked(granule));
	CHECK_EQUAL(0U, granule_unlocked_state(granule));
}

ASSERT_TEST(granule, granule_refcount_read_acquire_TC2)
{
	/******************************************************************
	 * TEST CASE 2:
	 *
	 * Verify that granule_refcount_read_acquire() asserts when
	 * a granule pointer is NULL.
	 ******************************************************************/

	test_helpers_expect_assert_fail(true);

	/* Read the value */
	(void)granule_refcount_read_acquire(NULL);
	test_helpers_fail_if_no_assert_failed();
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
		address = (granule_indexes[i] * GRANULE_SIZE) +
						host_util_get_granule_base();
		expected_granule = tr_addr_to_granule(address);
		granule = tr_find_fine_granule(address);
		POINTERS_EQUAL(expected_granule, granule);

		/*
		 * Verify that not other parameters of the granule are altered
		 */
		CHECK_TEXT(granule_unlocked_state(granule) == 0U, "Invalid granule state");
		CHECK_TEXT(!is_granule_locked(granule), "Invalid granule lock status");
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

	granule = tr_find_fine_granule(address);
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
	granule = tr_find_fine_granule(address);

	POINTERS_EQUAL(NULL, granule);

	/* Try the lower boundary as well */
	if (get_out_of_range_granule(&address, false) == true) {
		granule = tr_find_fine_granule(address);
		POINTERS_EQUAL(NULL, granule);
	}
}

TEST(granule, find_lock_two_granules_TC1)
{
	unsigned long g1_index, g2_index;
	struct granule *exp_g1, *exp_g2;
	struct granule *g1, *g2;
	unsigned long addr1, addr2;
	unsigned long retval;

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

	/* Get the expected PA for the corresponding granules */
	addr1 = (g1_index * GRANULE_SIZE) + host_util_get_granule_base();
	addr2 = (g2_index * GRANULE_SIZE) + host_util_get_granule_base();
	exp_g1 = tr_addr_to_granule(addr1);
	exp_g2 = tr_addr_to_granule(addr2);

	g1 = NULL;
	g2 = NULL;

	/* Lock the granules */
	retval = tr_find_lock_two_fine_granules(addr1, GRANULE_STATE_NS, &g1,
					addr2, GRANULE_STATE_NS, &g2);

	UNSIGNED_LONGS_EQUAL(RMI_SUCCESS, retval);
	CHECK_FALSE(g1 == NULL);
	CHECK_FALSE(g2 == NULL);
	POINTERS_EQUAL(exp_g1, g1);
	POINTERS_EQUAL(exp_g2, g2);
	CHECK_TRUE(is_granule_locked(g1));
	CHECK_TRUE(is_granule_locked(g2));
	CHECK_EQUAL(GRANULE_STATE_NS, granule_get_state(g1));
	CHECK_EQUAL(GRANULE_STATE_NS, granule_get_state(g2));
}

TEST(granule, find_lock_two_granules_TC2)
{
	struct granule *g1, *g2;
	unsigned long addr;
	unsigned long retval;

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
	retval = tr_find_lock_two_fine_granules(addr, GRANULE_STATE_NS, &g1,
					addr, GRANULE_STATE_NS, &g2);

	UNSIGNED_LONGS_EQUAL(RMI_ERROR_INPUT, retval);

	/* Check that the granule address are the same as before calling */
	POINTERS_EQUAL(NULL, g1);
	POINTERS_EQUAL(NULL, g2);
}

TEST(granule, find_lock_two_granules_TC3)
{
	struct granule *g1, *g2;
	unsigned long addr1, addr2, tmp_addr;
	unsigned long retval;

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

	retval = tr_find_lock_two_fine_granules(tmp_addr, GRANULE_STATE_NS, &g1,
					addr1, GRANULE_STATE_NS, &g2);

	UNSIGNED_LONGS_EQUAL(RMI_ERROR_INPUT, retval);

	/* Check that the granule address are the same as before calling */
	POINTERS_EQUAL(NULL, g1);
	POINTERS_EQUAL(NULL, g2);

	retval = tr_find_lock_two_fine_granules(addr1, GRANULE_STATE_NS, &g1,
					tmp_addr, GRANULE_STATE_NS, &g2);

	UNSIGNED_LONGS_EQUAL(RMI_ERROR_INPUT, retval);

	/* Check that the granule address are the same as before calling */
	POINTERS_EQUAL(NULL, g1);
	POINTERS_EQUAL(NULL, g2);
}

TEST(granule, find_lock_two_granules_TC4)
{
	struct granule *g1, *g2;
	unsigned long addr1, addr2, tmp_addr;
	unsigned long retval;

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
	retval = tr_find_lock_two_fine_granules(tmp_addr, GRANULE_STATE_NS, &g1,
					addr2, GRANULE_STATE_NS, &g2);

	UNSIGNED_LONGS_EQUAL(RMI_ERROR_INPUT, retval);

	/* Check that the granule address are the same as before calling */
	POINTERS_EQUAL(NULL, g1);
	POINTERS_EQUAL(NULL, g2);

	/* Try the lower boundary as well if possible */
	if (get_out_of_range_granule(&tmp_addr, false) == true) {
		retval = tr_find_lock_two_fine_granules(tmp_addr, GRANULE_STATE_NS,
					&g1, addr2, GRANULE_STATE_NS, &g2);

		UNSIGNED_LONGS_EQUAL(RMI_ERROR_INPUT, retval);

		/* Check that the granule address are the same as before calling */
		POINTERS_EQUAL(NULL, g1);
		POINTERS_EQUAL(NULL, g2);
	}

	(void)get_out_of_range_granule(&tmp_addr, true);
	retval = tr_find_lock_two_fine_granules(addr1, GRANULE_STATE_NS, &g1,
					tmp_addr, GRANULE_STATE_NS, &g2);

	UNSIGNED_LONGS_EQUAL(RMI_ERROR_INPUT, retval);

	/* Check that the granule address are the same as before calling */
	POINTERS_EQUAL(NULL, g1);
	POINTERS_EQUAL(NULL, g2);

	/* Try the lower boundary as well if possible */
	if (get_out_of_range_granule(&tmp_addr, false) == true) {

		retval = tr_find_lock_two_fine_granules(addr1, GRANULE_STATE_NS, &g1,
					tmp_addr, GRANULE_STATE_NS, &g2);

		UNSIGNED_LONGS_EQUAL(RMI_ERROR_INPUT, retval);

		/* Check that the granule address are the same as before calling */
		POINTERS_EQUAL(NULL, g1);
		POINTERS_EQUAL(NULL, g2);
	}
}

TEST(granule, find_lock_two_granules_TC5)
{
	struct granule *g1, *g2;
	unsigned long addr1, addr2;
	unsigned long retval;

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

	for (unsigned char state1 = GRANULE_STATE_NS;
	     state1 <= GRANULE_STATE_LAST; state1++) {

		for (unsigned char state2 = GRANULE_STATE_NS;
		     state2 <= GRANULE_STATE_LAST; state2++) {
			if (state1 == GRANULE_STATE_NS &&
			    state2 == GRANULE_STATE_NS) {
				/*
				 * Skip. Test case already checked as we expect
				 * the default state to be STATE_NS.
				 */
				continue;
			}
			retval = tr_find_lock_two_fine_granules(
					addr1, state1, &g1,
					addr2, state2, &g2);

			UNSIGNED_LONGS_EQUAL(RMI_ERROR_INPUT, retval);

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
	 * Verify that tr_find_lock_two_fine_granules() asserts when the first
	 * reference to a granule pointer is NULL.
	 ******************************************************************/

	/* Get random PAs for two different granules */
	do {
		addr1 = get_rand_granule_addr();
		addr2 = get_rand_granule_addr();
	} while (addr1 == addr2);

	granule = NULL;

	test_helpers_expect_assert_fail(true);
	(void)tr_find_lock_two_fine_granules(addr1, GRANULE_STATE_DELEGATED, NULL,
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
	 * Verify that tr_find_lock_two_fine_granules() asserts when the second
	 * reference to a granule pointer is NULL.
	 ******************************************************************/

	/* Get random PAs for two different granules */
	do {
		addr1 = get_rand_granule_addr();
		addr2 = get_rand_granule_addr();
	} while (addr1 == addr2);

	granule = NULL;

	test_helpers_expect_assert_fail(true);
	(void)tr_find_lock_two_fine_granules(addr1, GRANULE_STATE_DELEGATED, &granule,
				     addr2, GRANULE_STATE_DELEGATED, NULL);
	test_helpers_fail_if_no_assert_failed();
}

TEST(granule, find_lock_granule_TC1)
{
	struct granule *granule;
	unsigned long ret;
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
		ret = tr_find_lock_granule(addrs[i], GRANULE_SIZE,
					   GRANULE_STATE_NS, &granule);
		LONGS_EQUAL(RMI_SUCCESS, ret);
		CHECK_FALSE(granule == NULL);
		CHECK_TRUE(is_granule_locked(granule));
	}
}

TEST(granule, find_lock_granule_TC2)
{
	struct granule *granule;
	unsigned long ret;
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
		for (unsigned char state = GRANULE_STATE_NS + 1U;
		     state <= GRANULE_STATE_LAST; state++) {
			ret = tr_find_lock_granule(addrs[i], GRANULE_SIZE,
						   state, &granule);
			LONGS_EQUAL(RMI_ERROR_INPUT, ret);
			POINTERS_EQUAL(NULL, granule);
		}
	}
}

TEST(granule, find_lock_granule_TC3)
{
	struct granule *granule;
	unsigned long addr;
	unsigned long ret;

	/***************************************************************
	 * TEST CASE 3:
	 *
	 * Try to find and lock a granule for a misaligned address
	 * to all possible states.
	 ***************************************************************/
	addr = get_rand_granule_addr();
	addr += test_helpers_get_rand_in_range(1UL, GRANULE_SIZE - 1);
	for (unsigned char state = GRANULE_STATE_NS;
	     state <= GRANULE_STATE_LAST; state++) {
		ret = tr_find_lock_granule(addr, GRANULE_SIZE, state, &granule);
		LONGS_EQUAL(RMI_ERROR_INPUT, ret);
		POINTERS_EQUAL(NULL, granule);
	}
}

TEST(granule, find_lock_granule_TC4)
{
	struct granule *granule;
	unsigned long addr;
	unsigned long ret;

	/***************************************************************
	 * TEST CASE 4:
	 *
	 * Try to find and lock a granule for an address outside the
	 * valid range to all possible states.
	 ***************************************************************/
	(void)get_out_of_range_granule(&addr, true);

	for (unsigned char state = GRANULE_STATE_NS;
	     state <= GRANULE_STATE_LAST; state++) {
		ret = tr_find_lock_granule(addr, GRANULE_SIZE, state, &granule);
		LONGS_EQUAL(RMI_ERROR_INPUT, ret);
		POINTERS_EQUAL(NULL, granule);

		/* Try the lower boundary as well */
		if (get_out_of_range_granule(&addr, false) == true) {
			ret = tr_find_lock_granule(addr, GRANULE_SIZE,
						   state, &granule);
			LONGS_EQUAL(RMI_ERROR_INPUT, ret);
			POINTERS_EQUAL(NULL, granule);
		}
	}
}

/* Acquire protected references in every valid state and release each lock. */
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
	 * Get a granule, lock and set it to a specific state. Then unlock
	 * it. Repeat for every possible state.
	 * Test the first and the last valid granules as well as random
	 * granules in between.
	 ******************************************************************/
	for (unsigned int i = 0U; i < 3U; i++) {
		granule = tr_addr_to_granule(addrs[i]);

		for (unsigned char state = GRANULE_STATE_NS;
		     state <= GRANULE_STATE_LAST; state++) {

			/* Ensure the granule is locked */
			granule_bitlock_acquire(granule);

			/* Set the granule state */
			__granule_set_state(granule, state);

			/* Unlock the granule */
			granule_bitlock_release(granule);
			CHECK_FALSE(is_granule_locked(granule));

			granule_lock(granule, state);
			CHECK_TRUE(is_granule_locked(granule));
			LONGS_EQUAL(state, granule_get_state(granule));
			granule_unlock(granule);
		}
	}

	/*
	 * The caller must supply a live, protected struct granule and a defined
	 * expected state. Invalid struct granule pointers are not exercised here;
	 * the state assertion is covered separately.
	 */
}

ASSERT_TEST(granule, granule_lock_TC2)
{
	struct granule *granule;
	unsigned char state, expected;
	unsigned long addr = (get_rand_granule_idx() * GRANULE_SIZE) +
					host_util_get_granule_base();

	/******************************************************************
	 * TEST CASE 2:
	 *
	 * Verify that granule_lock() asserts when the expected state of
	 * the granule does not mach the current one.
	 ******************************************************************/

	granule = tr_addr_to_granule(addr);
	do {
		state = (unsigned char)test_helpers_get_rand_in_range(
					(unsigned long)GRANULE_STATE_NS,
					(unsigned long)GRANULE_STATE_LAST);
		expected = (unsigned char)test_helpers_get_rand_in_range(
					(unsigned long)GRANULE_STATE_NS,
					(unsigned long)GRANULE_STATE_LAST);
	} while (state == expected);

	/* Ensure the granule is locked */
	granule_bitlock_acquire(granule);

	/* Set the granule state */
	__granule_set_state(granule, state);

	test_helpers_expect_assert_fail(true);

	/* Unlock the granule */
	granule_bitlock_release(granule);

	/* Lock the granule */
	granule_lock(granule, expected);
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
	 * Get a granule, lock and set it to a specific state. Then unlock
	 * it. Repeat for every possible state.
	 * Test the first and the last valid granules as well as random
	 * granules in between.
	 ******************************************************************/
	for (unsigned int i = 0U; i < 3U; i++) {
		granule = tr_addr_to_granule(addrs[i]);

		for (unsigned char state = GRANULE_STATE_NS;
		     state <= GRANULE_STATE_LAST; state++) {
			bool retval;

			/* Ensure the granule is locked */
			granule_bitlock_acquire(granule);

			/* Set the granule state */
			__granule_set_state(granule, state);

			/* Unlock the granule */
			granule_bitlock_release(granule);

			/* Lock the granule */
			retval = granule_lock_on_state_match(granule, state);
			CHECK(retval);
			CHECK_TRUE(is_granule_locked(granule));

			/* Unlock the granule */
			granule_bitlock_release(granule);
			CHECK_FALSE(is_granule_locked(granule));
		}
	}
}

/* Reject all mismatched expected states without retaining a granule lock. */
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
		granule = tr_addr_to_granule(addrs[i]);

		for (unsigned char state = GRANULE_STATE_NS;
		     state <= GRANULE_STATE_LAST; state++) {

			/* Ensure the granule is locked */
			granule_bitlock_acquire(granule);

			/* Set the granule state */
			__granule_set_state(granule, state);

			/* Unlock the granule */
			granule_bitlock_release(granule);

			for (unsigned char lock_state = GRANULE_STATE_NS;
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
								lock_state);
				CHECK_FALSE(retval);
				CHECK_FALSE(is_granule_locked(granule));
			}
		}
	}

	/*
	 * The caller must supply a live struct granule and a defined expected state.
	 * Invalid struct granule pointers cannot be dereferenced safely and are not
	 * exercised here.
	 */
}

TEST(granule, granule_refcount_inc_TC1)
{
	unsigned long address = get_rand_granule_addr();
	struct granule *granule = tr_find_fine_granule(address);
	unsigned short val = test_helpers_get_rand_in_range(1U, REFCOUNT_MAX);

	granule_bitlock_acquire(granule);

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Increase the refcount of a granule by invoking
	 * granule_refcount_inc().
	 * The refcount before the call is expected to be 0.
	 ******************************************************************/
	granule_refcount_inc(granule, val);

	SHORTS_EQUAL(val, granule_refcount_read(granule));

	/* Verify that not other parameters of the granule are altered */
	CHECK_EQUAL(0, granule_get_state(granule));
	CHECK_TRUE(is_granule_locked(granule));
}

ASSERT_TEST(granule, granule_refcount_inc_TC2)
{
	/******************************************************************
	 * TEST CASE 2:
	 *
	 * Verify that granule_refcount_inc() asserts when a granule
	 * pointer is NULL.
	 ******************************************************************/

	test_helpers_expect_assert_fail(true);
	granule_refcount_inc(NULL, 0U);
	test_helpers_fail_if_no_assert_failed();
}

TEST(granule, granule_refcount_dec_TC1)
{
	unsigned long address = get_rand_granule_addr();
	struct granule *granule = tr_find_fine_granule(address);
	unsigned short val = (unsigned short)test_helpers_get_rand_in_range(10U, REFCOUNT_MAX);

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Increase the refcount of a granule by invoking
	 * granule_refcount_inc(), then decrease it again with
	 * granule_refcount_dec().
	 *
	 * The refcount before the test starts is expected to be 0.
	 ******************************************************************/
	granule_bitlock_acquire(granule);

	granule_refcount_inc(granule, val);
	granule_refcount_dec(granule, val);

	SHORTS_EQUAL(0U, granule_refcount_read(granule));

	/* Verify that not other parameters of the granule are altered */
	CHECK_EQUAL(0, granule_get_state(granule));
	CHECK_TRUE(is_granule_locked(granule));
}

TEST(granule, granule_refcount_dec_TC2)
{
	unsigned long address = get_rand_granule_addr();
	struct granule *granule = tr_find_fine_granule(address);
	unsigned short val = (unsigned short)test_helpers_get_rand_in_range(10U, REFCOUNT_MAX);

	/******************************************************************
	 * TEST CASE 2:
	 *
	 * Increase the refcount of a granule by invoking
	 * granule_refcount_inc(), then decrease it again with
	 * granule_refcount_dec() but using a lower value than the one
	 * used for inc.
	 *
	 * The refcount before the test starts is expected to be 0.
	 ******************************************************************/
	granule_bitlock_acquire(granule);

	granule_refcount_inc(granule, val);
	granule_refcount_dec(granule, val - 1U);

	SHORTS_EQUAL(1U, granule_refcount_read(granule));

	/* Verify that not other parameters of the granule are altered */
	CHECK_EQUAL(0U, granule_get_state(granule));
	CHECK_TRUE(is_granule_locked(granule));
}

ASSERT_TEST(granule, granule_refcount_dec_TC3)
{
	unsigned long address = get_rand_granule_addr();
	struct granule *granule = tr_find_fine_granule(address);
	unsigned short val = (unsigned short)test_helpers_get_rand_in_range(1U, REFCOUNT_MAX - 1U);

	/******************************************************************
	 * TEST CASE 3:
	 *
	 * Verify that granule_refcount_dec() asserts when the granule
	 * refcount is lower than the value passed.
	 ******************************************************************/
	granule_bitlock_acquire(granule);

	granule_refcount_inc(granule, val);
	test_helpers_expect_assert_fail(true);
	granule_refcount_dec(granule, val + 1U);
	test_helpers_fail_if_no_assert_failed();
}

ASSERT_TEST(granule, granule_refcount_dec_TC4)
{
	/******************************************************************
	 * TEST CASE 4:
	 *
	 * Verify that granule_refcount_dec() asserts when a granule
	 * pointer is NULL.
	 ******************************************************************/

	test_helpers_expect_assert_fail(true);
	granule_refcount_dec(NULL, 0U);
	test_helpers_fail_if_no_assert_failed();
}

ASSERT_TEST(granule, granule_get_state_TC1)
{
	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Verify granule_get_state() asserts when a granule
	 * pointer is NULL.
	 ******************************************************************/

	test_helpers_expect_assert_fail(true);
	(void)granule_get_state(NULL);
	test_helpers_fail_if_no_assert_failed();
}

ASSERT_TEST(granule, granule_set_state_TC1)
{
	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Verify granule_get_state() asserts when a granule
	 * pointer is NULL for all possible states.
	 ******************************************************************/
	for (unsigned char state = GRANULE_STATE_NS;
	     state <= GRANULE_STATE_LAST; state++) {
		test_helpers_expect_assert_fail(true);

		/* Change the granule state */
		__granule_set_state(NULL, state);
		test_helpers_fail_if_no_assert_failed();
	}
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
		for (unsigned char state = GRANULE_STATE_NS;
		     state <= GRANULE_STATE_LAST; state++) {
			unsigned char next_state = (state + 1) %
						((int)GRANULE_STATE_LAST + 1);
			unsigned long ret;

			/* Find and lock a granule */
			ret = tr_find_lock_granule(addrs[i], GRANULE_SIZE,
						   state, &granule);
			LONGS_EQUAL(RMI_SUCCESS, ret);

			/* Change the granule state */
			__granule_set_state(granule, next_state);

			/* Check that the state is correct */
			CHECK_EQUAL(next_state, granule_get_state(granule));

			/*
			 * The granule must still be locked from
			 * tr_find_lock_granule()
			 */
			CHECK_TRUE(is_granule_locked(granule));

			/* Unlock the granule */
			granule_unlock(granule);
		}
	}

	/*
	 * granule_{set, get}_state() implementation expects that the next state
	 * belongs to the defined values, so it doesn't perform any checks on
	 * that.
	 */
}

TEST(granule, granule_set_get_unlocked_state_TC1)
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
		for (unsigned char state = GRANULE_STATE_NS;
		     state <= GRANULE_STATE_LAST;
		     state++) {
			unsigned char next_state = (state + 1) %
						((int)GRANULE_STATE_LAST + 1);
			unsigned long ret;

			/* Find and lock a granule */
			ret = tr_find_lock_granule(addrs[i], GRANULE_SIZE,
						   state, &granule);
			LONGS_EQUAL(RMI_SUCCESS, ret);

			/* Change the granule state */
			__granule_set_state(granule, next_state);

			/* Unlock the granule */
			granule_unlock(granule);

			/* The granule must be unlocked */
			CHECK_FALSE(is_granule_locked(granule));

			/* Check that the state of unlocked granule is correct */
			CHECK_EQUAL(next_state, granule_unlocked_state(granule));
		}
	}

	/*
	 * granule_{set, get}_state() implementation expects that the next state
	 * belongs to the defined values, so it doesn't perform any checks on
	 * that.
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
		for (unsigned char state = GRANULE_STATE_NS;
		     state <= GRANULE_STATE_LAST;
		     state++) {
			unsigned long ret;

			/* Find and lock a granule */
			ret = tr_find_lock_granule(addrs[i], GRANULE_SIZE,
						   GRANULE_STATE_NS, &granule);
			LONGS_EQUAL(RMI_SUCCESS, ret);

			/* Change the state of the granule */
			__granule_set_state(granule, state);

			/* Check that the state is correct */
			CHECK_EQUAL(state, granule_get_state(granule));

			/*
			 * The granule must still be locked from
			 * tr_find_lock_granule()
			 */
			CHECK_TRUE(is_granule_locked(granule));

			/*
			 * Leave the granule in a known state for
			 * the next iteration
			 */
			__granule_set_state(granule, GRANULE_STATE_NS);

			/* Unlock the granule */
			granule_bitlock_release(granule);
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
		for (unsigned char state = GRANULE_STATE_NS;
		     state <= GRANULE_STATE_LAST;
		     state++) {
			unsigned char next_state = (state + 1) %
						((int)GRANULE_STATE_LAST + 1);
			unsigned long ret;

			/* Find and lock a granule */
			ret = tr_find_lock_granule(addrs[i], GRANULE_SIZE,
						   state, &granule);
			LONGS_EQUAL(RMI_SUCCESS, ret);

			/* Unlock the granule changing its state */
			granule_unlock_transition(granule, next_state);

			/* Check that the state is correct */
			CHECK_FALSE(is_granule_locked(granule));
			CHECK_EQUAL(next_state, granule_unlocked_state(granule));
		}
	}

	/*
	 * granule_unlock_transition() implementation expects to always
	 * receive a valid granule and therefore it doesn't make any checks
	 * to ensure the correctness of the granule. Therefore, skip any tests
	 * with invalid granules.
	 *
	 * Likewise, it also expects that the next state belongs to
	 * the defined values, so it doesn't perform any checks on that either.
	 */
}

TEST(granule, granule_sanitize_1_mapped_TC1)
{
	unsigned char buf[GRANULE_SIZE];
	unsigned char ref[GRANULE_SIZE];

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Sanitize a granule using the scrub method 1 (seed).
	 ******************************************************************/

	memset((void *)buf, 0x0, GRANULE_SIZE);
	memset((void *)ref, 0x0, GRANULE_SIZE);

	granule_sanitize_1_mapped((void *)buf);

	CHECK_FALSE(memcmp((void *)buf, (void *)ref, GRANULE_SIZE) == 0);
}

TEST(granule, granule_sanitize_mapped_TC1)
{
	unsigned char buf[GRANULE_SIZE];
	unsigned char ref[GRANULE_SIZE];

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Sanitize a granule using the default scrub method 0 (zeroing).
	 ******************************************************************/

	memset((void *)buf, 0xFF, GRANULE_SIZE);
	memset((void *)ref, 0x0, GRANULE_SIZE);

	granule_sanitize_mapped((void *)buf);

	MEMCMP_EQUAL((void *)buf, (void *)ref, GRANULE_SIZE);
}

TEST(granule, granule_dcci_poe_TC1)
{
	struct granule *granule;
	unsigned char ref[GRANULE_SIZE];
	unsigned long addr;
	unsigned long ret;

	/***************************************************************
	 * TEST CASE 4:
	 *
	 * Perform a DC CIPAE operation on the granule memory.
	 ***************************************************************/
	addr = get_rand_granule_addr();
	ret = tr_find_lock_granule(addr, GRANULE_SIZE,
				  GRANULE_STATE_NS, &granule);

	UNSIGNED_LONGS_EQUAL(RMI_SUCCESS, ret);
	CHECK_TRUE(granule != NULL);
	CHECK_TRUE(is_granule_locked(granule));

	memset((void *)tr_granule_addr(granule), 0xFF, GRANULE_SIZE);
	memset((void *)ref, 0xFF, GRANULE_SIZE);

	granule_dcci_poe(granule);

	MEMCMP_EQUAL((void *)tr_granule_addr(granule), (void *)ref, GRANULE_SIZE);
}

TEST(granule, granule_unlock_transition_to_delegated_TC1)
{
	struct granule *granule;
	unsigned long addr;
	unsigned long ret;

	/******************************************************************
	 * TEST CASE 1:
	 *
	 * Find and lock a granule, then unlock it transitioning it to
	 * the DELEGATED state.
	 ******************************************************************/

	addr = get_rand_granule_addr();
	ret = tr_find_lock_granule(addr, GRANULE_SIZE,
				  GRANULE_STATE_NS, &granule);

	__granule_set_state(granule, GRANULE_STATE_RD);

	UNSIGNED_LONGS_EQUAL(RMI_SUCCESS, ret);
	CHECK_TRUE(granule != NULL);
	CHECK_TRUE(is_granule_locked(granule));

	granule_unlock_transition_to_delegated(granule);

	CHECK_FALSE(is_granule_locked(granule));
	CHECK_EQUAL(GRANULE_STATE_DELEGATED,
			granule_unlocked_state(granule));
}
