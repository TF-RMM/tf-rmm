/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <granule.h>
#include <realm.h>
#include <rsi-config.h>
#include <rsi-walk.h>
#include <smc-rsi.h>

struct rsi_walk_smc_result handle_rsi_realm_config(struct rec *rec)
{
	struct rsi_walk_smc_result res = { 0 };
	unsigned long ipa = rec->regs[1];
	enum s2_walk_status walk_status;
	struct s2_walk_result walk_res;
	struct granule *gr;
	struct rsi_realm_config *config;

	if (!GRANULE_ALIGNED(ipa) || !addr_in_rec_par(rec, ipa)) {
		res.smc_res.x[0] = RSI_ERROR_INPUT;
		return res;
	}

	walk_status = realm_ipa_to_pa(rec, ipa, &walk_res);

	if (walk_status == WALK_FAIL) {
		if (walk_res.ripas_val == RIPAS_EMPTY) {
			res.smc_res.x[0] = RSI_ERROR_INPUT;
		} else {
			/* Exit to Host */
			res.walk_result.abort = true;
			res.walk_result.rtt_level = walk_res.rtt_level;
		}
		return res;
	}

	if (walk_status == WALK_INVALID_PARAMS) {
		/* Return error to Realm */
		res.smc_res.x[0] = RSI_ERROR_INPUT;
		return res;
	}

	/* Map Realm data granule to RMM address space */
	gr = find_granule(walk_res.pa);
	config = (struct rsi_realm_config *)granule_map(gr, SLOT_RSI_CALL);

	/* Populate config structure */
	config->ipa_width = rec->realm_info.ipa_bits;

	/* Unmap Realm data granule */
	buffer_unmap(config);

	/* Unlock last level RTT */
	granule_unlock(walk_res.llt);

	/* Write output values */
	res.smc_res.x[0] = RSI_SUCCESS;
	return res;
}
