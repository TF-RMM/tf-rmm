/*
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <realm.h>
#include <ripas.h>
#include <rsi-handler.h>
#include <smc-rsi.h>

void handle_rsi_ipa_state_set(struct rec *rec,
			      struct rmi_rec_exit *rec_exit,
			      struct rsi_result *res)
{
	unsigned long base = rec->regs[1];
	unsigned long top = rec->regs[2];
	enum ripas ripas_val = (enum ripas)rec->regs[3];
	enum ripas_change_destroyed change_destroyed =
			(enum ripas_change_destroyed)rec->regs[4];

	if ((ripas_val > RIPAS_RAM) ||
	    !GRANULE_ALIGNED(base)  || !GRANULE_ALIGNED(top) ||
	    (top <= base)	    || /* Size is zero, or range overflows */
	    !region_in_rec_par(rec, base, top)) {
		res->action = UPDATE_REC_RETURN_TO_REALM;
		res->smc_res.x[0] = RSI_ERROR_INPUT;
		return;
	}

	rec->set_ripas.base = base;
	rec->set_ripas.top = top;
	rec->set_ripas.addr = base;
	rec->set_ripas.ripas_val = ripas_val;
	rec->set_ripas.change_destroyed = change_destroyed;

	rec_exit->exit_reason = RMI_EXIT_RIPAS_CHANGE;
	rec_exit->ripas_base = base;
	rec_exit->ripas_top = top;
	rec_exit->ripas_value = (unsigned char)ripas_val;

	res->action = UPDATE_REC_EXIT_TO_HOST;
	res->smc_res.x[0] = RSI_SUCCESS;
	res->smc_res.x[1] = top;
}

void handle_rsi_ipa_state_get(struct rec *rec,
			      struct rsi_result *res)
{
	unsigned long start = rec->regs[1];
	unsigned long end = rec->regs[2];
	unsigned long top = start;
	enum s2_walk_status ws;
	enum ripas ripas_val = RIPAS_EMPTY;

	res->action = UPDATE_REC_RETURN_TO_REALM;

	if (!GRANULE_ALIGNED(start) || !addr_in_rec_par(rec, start) ||
	    !GRANULE_ALIGNED(end) || !addr_in_rec_par(rec, end - 1UL) ||
	    (start >= end)) {
		res->smc_res.x[0] = RSI_ERROR_INPUT;
		return;
	}

	ws = realm_ipa_get_ripas(rec, start, end, &top, &ripas_val);
	if (ws == WALK_SUCCESS) {
		res->smc_res.x[0] = RSI_SUCCESS;
		res->smc_res.x[1] = (top > end) ? end : top;
		res->smc_res.x[2] = (unsigned long)ripas_val;
	} else {
		res->smc_res.x[0] = RSI_ERROR_INPUT;
	}
}
