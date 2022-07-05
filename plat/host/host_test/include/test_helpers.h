/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef TEST_HELPERS_H
#define TEST_HELPERS_H

/*
 * Helper function to fully initialize RMM.
 *
 * Args
 *	secondaries - If true, support for secondary PEs is enabled.
 */
void test_helper_rmm_start(bool secondaries);

/*
 * Helper function to get the total number of memory granules available
 * to the system.
 */
unsigned int test_helper_get_nr_granules(void);

#endif
