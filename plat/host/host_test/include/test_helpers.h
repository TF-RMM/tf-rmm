/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef TEST_HELPERS_H
#define TEST_HELPERS_H

#include <assert.h>
#include <stdbool.h>

/*
 * Definitions used for assertion tests.
 * clang++ older than v14 can cause problems when enabling
 * assertion control on unit tests.
 */
#if ((NDEBUG) || \
	((defined __clang_major__) && (__clang_major__ < 14)))
#define ASSERT_TEST IGNORE_TEST
#else
#define ASSERT_TEST TEST
#endif

/*
 * Macro to replace CHECK_TRUE() with an equivalent that also prints
 * a verbose message with a "PASS"/"FAIL" tail.
 */
#define CHECK_VERBOSE(condition, ...)					\
	do {								\
		VERBOSE(__VA_ARGS__);					\
		VERBOSE(" : %s\n", ((condition) == true) ? "PASS" : "FAIL"); \
		CHECK_TRUE((condition));				\
	} while (false)

/*
 * Callback identifiers for all the possible host harness
 * callbacks that can be installed by the unit tests.
 */
enum cb_ids {
	CB_ID0 = 0,
	CB_BUFFER_MAP = CB_ID0,
	CB_BUFFER_UNMAP,
	CB_IDS
};

/*
 * Below are the declarations for callbacks for functions to be defined
 * by the tests which allow them to implement specific host harness APIs.
 * Each callback is identified by an unique ID.
 */

/*
 * Callback ID: CB_BUFFER_MAP
 *
 * Map a given granule address to a specific slot buffer
 * Args
 *	slot - Slot buffer type where to map to
 *	addr - Granule address to map
 * Return
 *	The VA (or platform equivalent) where the granule was mapped to
 */

typedef void *(*cb_buffer_map)(unsigned int slot, unsigned long addr);

/*
 * Callback ID: CB_BUFFER_UNMAP
 *
 * Unmap a given granule from its corresponding slot buffer given the
 * mapped granule address.
 */
typedef void (*cb_buffer_unmap)(void *buf);

union test_harness_cbs {
	cb_buffer_map buffer_map;
	cb_buffer_unmap buffer_unmap;
};

/*
 * Register a host harness callback to be used for testing,
 * overwriting any existing one.
 *
 * Args:
 *	- cb: Pointer to the callback to use
 *	- id: Unique ID for the callback
 * Return:
 *	- 0 If the callback is successfully registered
 *	- -EINVAL on an argument error
 */
int test_helpers_register_cb(union test_harness_cbs cb, enum cb_ids id);

/*
 * Unregister a system callback for testing.
 *
 * Args:
 *	- id: Unique ID for the callback
 * Return:
 *	- 0 If the callback is successfully registered
 *	- -EINVAL on an argument error
 */
int test_helpers_unregister_cb(enum cb_ids id);

/*
 * Return a random value within [min, max] range.
 */
unsigned long test_helpers_get_rand_in_range(unsigned long min,
					     unsigned long max);

/*
 * Defines whether we expect or not an assert to fail.
 *
 * Arguments:
 *	- expected: True if we are expecting assertion to fail.
 *		    False if we do not expect an assertion to fail.
 *	- check: If NULL and expected is True, it will consider any
 *		 assertion failure as valid. If not NULL, the assertion check
 *		 that failed must match the one in check to be considered
 *		 valid.
 *
 * If, during the execution of the test, an assertion fails and it is not
 * expected or the check fails, the current unittest with FAIL.
 *
 * Conversely, if an expected assertion failure happens, the test will FINISH
 * and will be marked as PASSED.
 *
 * NOTE: After an assertion failure, regardless of whether it was expected or
 * not, the next assertion failure will be considered unexpected and
 * therefore the test will fail. If we expect another assertion to fail, then
 * this API must be called again to indicate that. It is recommended to setup
 * the expected assert() behavior during TEST_SETUP().
 *
 * NOTE2: If an assertion failure was expected but did not happen, it will
 * not cause the test to FAIL and therefore the test will continue. If no
 * other condition causes a test failure and the call that was expected to
 * cause the assert failure manages to return, the unittest must fail
 * immediately.
 * See test_helpers_fail_if_not_assertion()
 */
void test_helpers_expect_assert_fail_with_check(bool expected, char *check);

/*
 * Defines whether we expect or not an assert to fail.
 *
 * Arguments:
 *	- expected: True if we are expecting assertion to fail.
 *		    False if we do not expect an assertion to fail.
 *
 * If, during the execution of the test, an assertion fails and it is not
 * expected, the current unittest with FAIL.
 *
 * Conversely, if an expected assertion failure happens, the test will FINISH
 * and will be marked as PASSED.
 *
 * NOTE: After an assertion failure, regardless of whether it was expected or
 * not, the next assertion failure will be considered unexpected and
 * therefore the test will fail. If we expect another assertion to fail, then
 * this API must be called again to indicate that. It is recommended to setup
 * the expected assert() behavior during TEST_SETUP().
 *
 * NOTE2: If an assertion failure was expected but did not happen, it will
 * not cause the test to FAIL and therefore the test will continue. If no
 * other condition causes a test failure and the call that was expected to
 * cause the assert failure manages to return, the unittest must fail
 * immediately.
 * See test_helpers_fail_if_not_assertion()
 */
void test_helpers_expect_assert_fail(bool expected);

/*
 * Call this function to fail a test if an expected assert fail did not happen.
 * This is preferred than fail with FAIL_TEST().
 */
void test_helpers_fail_if_no_assert_failed(void);

/*
 * Helper function to fully initialize RMM.
 *
 * Args
 *	secondaries - If true, support for secondary PEs is enabled.
 */
void test_helpers_rmm_start(bool secondaries);

/*
 * Helper function to get the total number of memory granules available
 * to the system.
 */
unsigned int test_helpers_get_nr_granules(void);

/*
 * Initializes the test helper library
 */
void test_helpers_init(void);

/*
 * Return a pointer to the first available granule structure
 */
struct granule *test_helpers_granule_struct_base(void);

#endif
