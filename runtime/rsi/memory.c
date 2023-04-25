/*
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <realm.h>
#include <ripas.h>
#include <rsi-memory.h>
#include <smc-rsi.h>
#include <status.h>

bool handle_rsi_ipa_state_set(struct rec *rec, struct rmi_rec_exit *rec_exit)
{
	unsigned long start = rec->regs[1];
	unsigned long size = rec->regs[2];
	unsigned long end = start + size;
	enum ripas ripas_val = (enum ripas)rec->regs[3];

	if (ripas_val > RIPAS_RAM) {
		return true;
	}

	if (!GRANULE_ALIGNED(start)) {
		return true;
	}

	if (!GRANULE_ALIGNED(size)) {
		return true;
	}

	if (end <= start) {
		/* Size is zero, or range overflows */
		return true;
	}

	if (!region_in_rec_par(rec, start, end)) {
		return true;
	}

	rec->set_ripas.base = start;
	rec->set_ripas.top = end;
	rec->set_ripas.addr = start;
	rec->set_ripas.ripas_val = ripas_val;

	rec_exit->exit_reason = RMI_EXIT_RIPAS_CHANGE;
	rec_exit->ripas_base = start;
	rec_exit->ripas_size = size;
	rec_exit->ripas_value = (unsigned int)ripas_val;

	return false;
}

struct rsi_walk_smc_result handle_rsi_ipa_state_get(struct rec *rec)
{
	struct rsi_walk_smc_result res = { 0 };
	enum s2_walk_status ws;
	unsigned long rtt_level, ipa;
	enum ripas ripas_val;

	ipa = rec->regs[1];

	/* Exit to realm */
	res.walk_result.abort = false;

	if (!GRANULE_ALIGNED(ipa) || !addr_in_rec_par(rec, ipa)) {
		res.smc_res.x[0] = RSI_ERROR_INPUT;
		return res;
	}

	ws = realm_ipa_get_ripas(rec, ipa, &ripas_val, &rtt_level);
	if (ws == WALK_SUCCESS) {
		res.smc_res.x[0] = RSI_SUCCESS;
		res.smc_res.x[1] = ripas_val;
	} else {
		/* Exit to Host */
		res.walk_result.abort = true;
		res.walk_result.rtt_level = rtt_level;
	}

	return res;
}
