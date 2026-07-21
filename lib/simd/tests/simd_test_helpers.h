/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef SIMD_TEST_HELPERS_H
#define SIMD_TEST_HELPERS_H

#include <host_utils.h>
#include <simd.h>
#include <stdlib.h>
#include <test_helpers.h>

/*
 * Should be called before each unit test to set up the testing environment,
 * e.g. resetting all sysregs to default values.
 */
void simd_test_helpers_init(void);

/*
 * Should be called after each unit test to unregister any callbacks.
 */
void simd_test_helpers_teardown(void);

/*
 * Setup the ID registers for SIMD.
 *
 * Arguments:
 * - is_sve_en: Specifies if SVE should be enabled.
 * - is_sme_en: Specifies if SME should be enabled.
 */
void simd_test_helpers_setup_id_regs(bool is_sve_en, bool is_sme_en);

#endif /* SIMD_TEST_HELPERS_H */
