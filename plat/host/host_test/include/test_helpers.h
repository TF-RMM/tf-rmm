/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef TEST_HELPERS_H
#define TEST_HELPERS_H

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
