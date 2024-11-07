/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <buffer.h>
#include <granule.h>
#include <realm.h>
#include <rsi-handler.h>
#include <rsi-host-call.h>
#include <smc-rsi.h>
#include <string.h>

/*
 * If the RIPAS of the target IPA is empty then return value is RSI_ERROR_INPUT.
 *
 * If the RTT walk fails then:
 *   - @rsi_walk_result.abort is true and @rsi_walk_result.rtt_level is the
 *     last level reached by the walk.
 *   - Return value is RSI_SUCCESS.
 *
 * If the RTT walk succeeds then:
 *   - If @rec_exit is not NULL and @rec_enter is NULL, then copy host call
 *     arguments from host call data structure (in Realm memory) to @rec_exit.
 *   - If @rec_exit is NULL and @rec_enter is not NULL, then copy host call
 *     results to host call data structure (in Realm memory).
 *   - Return value is RSI_SUCCESS.
 */
static void do_host_call(struct rec *rec, struct rmi_rec_exit *rec_exit,
			 struct rmi_rec_enter *rec_enter,
			 struct rsi_result *res)
{
	enum s2_walk_status walk_status;
	struct s2_walk_result walk_result;
	unsigned long ipa = rec->regs[1];
	unsigned long page_ipa;
	struct granule *gr;
	uintptr_t data;
	struct rsi_host_call *host_call;
	unsigned int i;

	assert(addr_in_rec_par(rec, ipa));

	/* Only 'rec_enter' or 'rec_exit' should be set */
	assert((rec_enter != NULL) != (rec_exit != NULL));

	page_ipa = ipa & GRANULE_MASK;
	walk_status = realm_ipa_to_pa(rec, page_ipa, &walk_result);

	switch (walk_status) {
	case WALK_SUCCESS:
		break;
	case WALK_FAIL:
		if (walk_result.ripas_val == RIPAS_EMPTY) {
			res->smc_res.x[0] = RSI_ERROR_INPUT;
		} else {
			res->action = STAGE_2_TRANSLATION_FAULT;
			res->rtt_level = walk_result.rtt_level;
		}
		return;
	case WALK_INVALID_PARAMS:
	default:
		assert(false);
		break;
	}

	/* Map Realm data granule to RMM address space */
	gr = find_granule(walk_result.pa);
	data = (uintptr_t)buffer_granule_map(gr, SLOT_RSI_CALL);
	assert(data != 0UL);

	host_call = (struct rsi_host_call *)(data + ipa - page_ipa);

	if (rec_exit != NULL) {
		/* Copy host call arguments to REC exit data structure */
		rec_exit->imm = host_call->imm;
		for (i = 0U; i < RSI_HOST_CALL_NR_GPRS; i++) {
			rec_exit->gprs[i] = host_call->gprs[i];
		}

		/* Record that a host call is pending */
		rec->host_call = true;

		/*
		 * Notify the Host.
		 * Leave REC registers unchanged,
		 * these will be read and updated by complete_rsi_host_call.
		 */
		res->action = EXIT_TO_HOST;
		rec_exit->exit_reason = RMI_EXIT_HOST_CALL;
	} else {
		/* Copy host call results to host call data structure */
		for (i = 0U; i < RSI_HOST_CALL_NR_GPRS; i++) {
			host_call->gprs[i] = rec_enter->gprs[i];
		}

		rec->regs[0] = RSI_SUCCESS;
	}

	/* Unmap Realm data granule */
	buffer_unmap((void *)data);

	/* Unlock last level RTT */
	granule_unlock(walk_result.llt);
}

void handle_rsi_host_call(struct rec *rec, struct rmi_rec_exit *rec_exit,
			  struct rsi_result *res)
{
	unsigned long ipa = rec->regs[1];

	res->action = UPDATE_REC_RETURN_TO_REALM;

	if (!ALIGNED(ipa, sizeof(struct rsi_host_call))) {
		res->smc_res.x[0] = RSI_ERROR_INPUT;
		return;
	}

	if ((ipa / GRANULE_SIZE) !=
		((ipa + sizeof(struct rsi_host_call) - 1UL) / GRANULE_SIZE)) {
		res->smc_res.x[0] = RSI_ERROR_INPUT;
		return;
	}

	if (!addr_in_rec_par(rec, ipa)) {
		res->smc_res.x[0] = RSI_ERROR_INPUT;
		return;
	}

	do_host_call(rec, rec_exit, NULL, res);
}

struct rsi_walk_result complete_rsi_host_call(struct rec *rec,
					      struct rmi_rec_enter *rec_enter)
{
	struct rsi_result res = { (enum rsi_action)0U };
	struct rsi_walk_result walk_res = { false, 0UL };

	/*
	 * Do the necessary to walk the S2 RTTs and copy args from NS Host
	 * to the host call data structure. But it is possible for the
	 * RIPAS of the IPA to be EMPTY and hence this call can return
	 * RSI_ERROR_INPUT. In this case, we return RSI_SUCCESS to Realm
	 * and Realm may take an abort on accessing the IPA (depending on
	 * the RIPAS of IPA at that time). This is a situation which can be
	 * controlled from Realm and Realm should avoid this.
	 */
	do_host_call(rec, NULL, rec_enter, &res);

	if (res.action == STAGE_2_TRANSLATION_FAULT) {
		walk_res.abort = true;
		walk_res.rtt_level = res.rtt_level;
	}

	return walk_res;
}
