/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef TEST_HELPERS_H
#define TEST_HELPERS_H

#include <buffer.h>

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

typedef void *(*cb_buffer_map)(enum buffer_slot slot, unsigned long addr);

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
int test_helpers_get_rand_in_range(int min, int max);

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

#endif
