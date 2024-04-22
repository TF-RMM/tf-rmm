/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 *
 * This file was AUTOGENERATED from the RMM specification.
 * RMM specification source version: 790fd539
 */

#include "tb.h"
#include "tb_rmi_rec_aux_count.h"

bool tb_rmi_rec_aux_count(
	uint64_t rd)
{
	/*
	 * Initialize registers
	 */

	struct tb_regs __tb_regs = __tb_arb_regs();

	__tb_regs.X0 = SMC_RMM_REC_AUX_COUNT;
	__tb_regs.X1 = (uint64_t)rd;

	/*
	 * Initialize global state
	 */

	__init_global_state(__tb_regs.X0);

	/*
	 * Pre-conditions
	 */

	bool failure_rd_align_pre = !AddrIsGranuleAligned(rd);
	bool failure_rd_bound_pre = !PaIsDelegable(rd);
	bool failure_rd_state_pre = Granule(rd).state != RD;
	bool no_failures_pre = !failure_rd_align_pre
		&& !failure_rd_bound_pre
		&& !failure_rd_state_pre;

	/*
	 * Execute command and read the result.
	 */

	tb_handle_smc(&__tb_regs);
	uint64_t result = __tb_regs.X0;
	uint64_t aux_count = __tb_regs.X1;

	/*
	 * Post-conditions
	 */

	bool failure_rd_align_post = ResultEqual_2(result, RMI_ERROR_INPUT);
	bool failure_rd_bound_post = ResultEqual_2(result, RMI_ERROR_INPUT);
	bool failure_rd_state_post = ResultEqual_2(result, RMI_ERROR_INPUT);
	bool success_aux_count_post = aux_count == RecAuxCount(rd);

	/*
	 * Failure condition assertions
	 */

	bool prop_failure_rd_align_ante = failure_rd_align_pre;

	__COVER(prop_failure_rd_align_ante);
	if (prop_failure_rd_align_ante) {
		bool prop_failure_rd_align_cons = failure_rd_align_post;

		__COVER(prop_failure_rd_align_cons);
		__ASSERT(prop_failure_rd_align_cons, "prop_failure_rd_align_cons");
	}

	bool prop_failure_rd_bound_ante = !failure_rd_align_pre
		&& failure_rd_bound_pre;

	__COVER(prop_failure_rd_bound_ante);
	if (prop_failure_rd_bound_ante) {
		bool prop_failure_rd_bound_cons = failure_rd_bound_post;

		__COVER(prop_failure_rd_bound_cons);
		__ASSERT(prop_failure_rd_bound_cons, "prop_failure_rd_bound_cons");
	}

	bool prop_failure_rd_state_ante = !failure_rd_align_pre
		&& !failure_rd_bound_pre
		&& failure_rd_state_pre;

	__COVER(prop_failure_rd_state_ante);
	if (prop_failure_rd_state_ante) {
		bool prop_failure_rd_state_cons = failure_rd_state_post;

		__COVER(prop_failure_rd_state_cons);
		__ASSERT(prop_failure_rd_state_cons, "prop_failure_rd_state_cons");
	}

	/*
	 * Result assertion
	 */

	bool prop_result_ante = no_failures_pre;

	__COVER(prop_result_ante);
	if (prop_result_ante) {
		bool prop_result_cons = result == RMI_SUCCESS;

		__COVER(prop_result_cons);
		__ASSERT(prop_result_cons, "prop_result_cons");
	}

	/*
	 * Success condition assertions
	 */

	bool prop_success_aux_count_ante = no_failures_pre;

	__COVER(prop_success_aux_count_ante);
	if (prop_success_aux_count_ante) {
		bool prop_success_aux_count_cons = success_aux_count_post
		&& (result == RMI_SUCCESS);

		__COVER(prop_success_aux_count_cons);
		__ASSERT(prop_success_aux_count_cons, "prop_success_aux_count_cons");
	}

	/*
	 * Assertion used to check consistency of the testbench
	 */
	__tb_expect_fail();

	return no_failures_pre;
}