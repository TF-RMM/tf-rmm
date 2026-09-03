/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <CppUTest/CommandLineTestRunner.h>
#include <CppUTest/TestHarness.h>

extern "C" {
#include <rec.h>
#include <rsi-handler.h>
#include <s2ap_ind.h>
#include <smc-rsi.h>
#include <string.h>
}

TEST_GROUP(rsi_memory_tests) {
};

/*
 * Initialize valid RSI_MEM_SET_PERM_VALUE inputs for the single auxiliary
 * Plane in @rec.  Tests replace one input at a time to exercise validation.
 */
static void init_set_perm_value_inputs(struct rec *rec, struct rsi_result *res)
{
	(void)memset(rec, 0, sizeof(*rec));
	(void)memset(res, 0, sizeof(*res));

	/* One auxiliary Plane makes Plane 1 a valid command target. */
	rec->realm_info.num_aux_planes = 1U;
	rec->plane[PLANE_0_ID].regs[1U] = 1UL;
	rec->plane[PLANE_0_ID].regs[2U] =
		S2AP_NUM_PERM_OVERLAY_INDICES - 1U;
	rec->plane[PLANE_0_ID].regs[3U] = S2AP_IND_PERM_RW_upX;
}

/* Verify the shared S2AP permission-value validator accepts only four bits. */
TEST(rsi_memory_tests, perm_value_validator_enforces_field_width)
{
	CHECK_TRUE(s2ap_is_perm_value_valid(S2AP_IND_PERM_COUNT - 1U));
	CHECK_FALSE(s2ap_is_perm_value_valid(S2AP_IND_PERM_COUNT));
}

/*
 * Verify that RSI_MEM_SET_PERM_VALUE rejects a value wider than the S2AP
 * permission-indirection field before attempting to access the RD.
 */
TEST(rsi_memory_tests, set_perm_value_rejects_out_of_range_permission)
{
	struct rec rec;
	struct rsi_result res;

	init_set_perm_value_inputs(&rec, &res);
	rec.plane[PLANE_0_ID].regs[3U] = 0xF0UL;

	handle_rsi_mem_set_perm_value(&rec, &res);

	UNSIGNED_LONGS_EQUAL(RSI_ERROR_INPUT, res.smc_res.x[0U]);
	CHECK_EQUAL(UPDATE_REC_RETURN_TO_REALM, res.action);
}

/* Verify that the primary Plane cannot update auxiliary Plane permissions. */
TEST(rsi_memory_tests, set_perm_value_rejects_primary_plane)
{
	struct rec rec;
	struct rsi_result res;

	init_set_perm_value_inputs(&rec, &res);
	rec.plane[PLANE_0_ID].regs[1U] = PLANE_0_ID;

	handle_rsi_mem_set_perm_value(&rec, &res);

	UNSIGNED_LONGS_EQUAL(RSI_ERROR_INPUT, res.smc_res.x[0U]);
	CHECK_EQUAL(UPDATE_REC_RETURN_TO_REALM, res.action);
}

/* Verify that a Plane ID outside the Realm's Plane count is rejected. */
TEST(rsi_memory_tests, set_perm_value_rejects_out_of_range_plane)
{
	struct rec rec;
	struct rsi_result res;

	init_set_perm_value_inputs(&rec, &res);
	rec.plane[PLANE_0_ID].regs[1U] = rec.realm_info.num_aux_planes + 1U;

	handle_rsi_mem_set_perm_value(&rec, &res);

	UNSIGNED_LONGS_EQUAL(RSI_ERROR_INPUT, res.smc_res.x[0U]);
	CHECK_EQUAL(UPDATE_REC_RETURN_TO_REALM, res.action);
}

/* Verify that the immutable unprotected overlay index is not a valid target. */
TEST(rsi_memory_tests, set_perm_value_rejects_out_of_range_permission_index)
{
	struct rec rec;
	struct rsi_result res;

	init_set_perm_value_inputs(&rec, &res);
	rec.plane[PLANE_0_ID].regs[2U] = S2AP_NUM_PERM_OVERLAY_INDICES;

	handle_rsi_mem_set_perm_value(&rec, &res);

	UNSIGNED_LONGS_EQUAL(RSI_ERROR_INPUT, res.smc_res.x[0U]);
	CHECK_EQUAL(UPDATE_REC_RETURN_TO_REALM, res.action);
}
