/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <CppUTest/CommandLineTestRunner.h>
#include <CppUTest/TestHarness.h>

extern "C" {
#include <rec.h>
#include <ripas.h>
#include <rsi-handler.h>
#include <s2ap_ind.h>
#include <smc-rmi.h>
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

/*
 * RSI_IPA_STATE_SET input fields.
 *
 * DEN0137 2.0-bet3 B5.4.7.1.1: ripas is X3[7:0] (RsiRipas, X3[63:8] SBZ) and
 * flags is X4 of type RsiRipasChangeFlags, whose only field is destroyed in
 * bit 0 (B5.5.22, B5.5.23; X4[63:1] Reserved SBZ). B5.4.7.2 ripas_valid
 * looks at the ripas field only. The handler must therefore record
 * flags.destroyed from bit 0 alone, so that the RMM's subsequent
 * DESTROYED to RAM decision (B4.5.71.1.2 walk_top_pre) does not depend on
 * reserved bits, and must accept a ripas value whose reserved bits are set.
 */
static void init_ipa_state_set_inputs(struct rec *rec,
				      struct rmi_rec_exit *rec_exit,
				      struct rsi_result *res)
{
	(void)memset(rec, 0, sizeof(*rec));
	(void)memset(rec_exit, 0, sizeof(*rec_exit));
	(void)memset(res, 0, sizeof(*res));

	/* Protected IPA space [0, 8KB): base and top lie inside it. */
	rec->realm_info.primary_s2_ctx.ipa_bits = GRANULE_SHIFT + 2U;
	rec->plane[PLANE_0_ID].regs[1U] = 0UL;
	rec->plane[PLANE_0_ID].regs[2U] = GRANULE_SIZE;
	rec->plane[PLANE_0_ID].regs[3U] = (unsigned long)RIPAS_RAM;
	rec->plane[PLANE_0_ID].regs[4U] = RSI_CHANGE_DESTROYED;
}

/* Control: destroyed = 1 with all reserved bits clear. */
TEST(rsi_memory_tests, ipa_state_set_records_destroyed_flag)
{
	struct rec rec;
	struct rmi_rec_exit rec_exit;
	struct rsi_result res;

	init_ipa_state_set_inputs(&rec, &rec_exit, &res);

	handle_rsi_ipa_state_set(&rec, &rec_exit, &res);

	UNSIGNED_LONGS_EQUAL(RSI_SUCCESS, res.smc_res.x[0U]);
	CHECK_EQUAL(UPDATE_REC_EXIT_TO_HOST, res.action);
	UNSIGNED_LONGS_EQUAL(RMI_EXIT_RIPAS_CHANGE, rec_exit.exit_reason);
	CHECK_EQUAL(RIPAS_RAM, rec.set_ripas.ripas_val);
	CHECK_EQUAL(CHANGE_DESTROYED, rec.set_ripas.change_destroyed);
}

/* Control: destroyed = 0 with a reserved bit set still means "no change". */
TEST(rsi_memory_tests, ipa_state_set_reserved_bit_without_destroyed)
{
	struct rec rec;
	struct rmi_rec_exit rec_exit;
	struct rsi_result res;

	init_ipa_state_set_inputs(&rec, &rec_exit, &res);
	rec.plane[PLANE_0_ID].regs[4U] = 0x2UL;

	handle_rsi_ipa_state_set(&rec, &rec_exit, &res);

	UNSIGNED_LONGS_EQUAL(RSI_SUCCESS, res.smc_res.x[0U]);
	CHECK_EQUAL(NO_CHANGE_DESTROYED, rec.set_ripas.change_destroyed);
}

/* B5.5.23: destroyed is bit 0; a set reserved bit does not clear it. */
TEST(rsi_memory_tests, ipa_state_set_reserved_bit_keeps_destroyed_flag)
{
	struct rec rec;
	struct rmi_rec_exit rec_exit;
	struct rsi_result res;

	init_ipa_state_set_inputs(&rec, &rec_exit, &res);
	rec.plane[PLANE_0_ID].regs[4U] = 0x3UL;

	handle_rsi_ipa_state_set(&rec, &rec_exit, &res);

	UNSIGNED_LONGS_EQUAL(RSI_SUCCESS, res.smc_res.x[0U]);
	CHECK_EQUAL(CHANGE_DESTROYED, rec.set_ripas.change_destroyed);
}

/* B5.5.23: bit 32 is reserved too, and must behave like bit 1. */
TEST(rsi_memory_tests, ipa_state_set_high_reserved_bit_keeps_destroyed_flag)
{
	struct rec rec;
	struct rmi_rec_exit rec_exit;
	struct rsi_result res;

	init_ipa_state_set_inputs(&rec, &rec_exit, &res);
	rec.plane[PLANE_0_ID].regs[4U] = 0x100000001UL;

	handle_rsi_ipa_state_set(&rec, &rec_exit, &res);

	UNSIGNED_LONGS_EQUAL(RSI_SUCCESS, res.smc_res.x[0U]);
	CHECK_EQUAL(CHANGE_DESTROYED, rec.set_ripas.change_destroyed);
}

/* Control, B5.4.7.2 ripas_valid: a ripas value other than EMPTY or RAM. */
TEST(rsi_memory_tests, ipa_state_set_rejects_invalid_ripas)
{
	struct rec rec;
	struct rmi_rec_exit rec_exit;
	struct rsi_result res;

	init_ipa_state_set_inputs(&rec, &rec_exit, &res);
	rec.plane[PLANE_0_ID].regs[3U] = (unsigned long)RIPAS_DESTROYED;

	handle_rsi_ipa_state_set(&rec, &rec_exit, &res);

	UNSIGNED_LONGS_EQUAL(RSI_ERROR_INPUT, res.smc_res.x[0U]);
	CHECK_EQUAL(UPDATE_REC_RETURN_TO_REALM, res.action);
}

/* B5.4.7.1.1: ripas is X3[7:0]; a set bit above it is not part of it. */
TEST(rsi_memory_tests, ipa_state_set_ripas_field_ignores_upper_bits)
{
	struct rec rec;
	struct rmi_rec_exit rec_exit;
	struct rsi_result res;

	init_ipa_state_set_inputs(&rec, &rec_exit, &res);
	rec.plane[PLANE_0_ID].regs[3U] = 0x100UL | (unsigned long)RIPAS_RAM;

	handle_rsi_ipa_state_set(&rec, &rec_exit, &res);

	UNSIGNED_LONGS_EQUAL(RSI_SUCCESS, res.smc_res.x[0U]);
	CHECK_EQUAL(RIPAS_RAM, rec.set_ripas.ripas_val);
}
