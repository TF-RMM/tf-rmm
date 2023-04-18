/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <buffer.h>
#include <granule.h>
#include <realm.h>
#include <rsi-host-call.h>
#include <smc-rsi.h>
#include <status.h>
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
 *   - If @rec_exit is not NULL and @rec_entry is NULL, then copy host call
 *     arguments from host call data structure (in Realm memory) to @rec_exit.
 *   - If @rec_exit is NULL and @rec_entry is not NULL, then copy host call
 *     results to host call data structure (in Realm memory).
 *   - Return value is RSI_SUCCESS.
 */
static unsigned int do_host_call(struct rec *rec,
				 struct rmi_rec_exit *rec_exit,
				 struct rmi_rec_entry *rec_entry,
				 struct rsi_walk_result *rsi_walk_result)
{
	enum s2_walk_status walk_status;
	struct s2_walk_result walk_result;
	unsigned long ipa = rec->regs[1];
	unsigned long page_ipa;
	struct granule *gr;
	unsigned char *data;
	struct rsi_host_call *host_call;
	unsigned int i;
	unsigned int ret = RSI_SUCCESS;

	assert(addr_in_rec_par(rec, ipa));

	/* Only 'rec_entry' or 'rec_exit' should be set */
	assert((rec_entry != NULL) ^ (rec_exit != NULL));

	page_ipa = ipa & GRANULE_MASK;
	walk_status = realm_ipa_to_pa(rec, page_ipa, &walk_result);

	switch (walk_status) {
	case WALK_SUCCESS:
		break;
	case WALK_FAIL:
		if (walk_result.ripas_val == RIPAS_EMPTY) {
			ret = RSI_ERROR_INPUT;
		} else {
			rsi_walk_result->abort = true;
			rsi_walk_result->rtt_level = walk_result.rtt_level;
		}
		return ret;
	case WALK_INVALID_PARAMS:
		assert(false);
		break;
	}

	/* Map Realm data granule to RMM address space */
	gr = find_granule(walk_result.pa);
	data = (unsigned char *)granule_map(gr, SLOT_RSI_CALL);
	host_call = (struct rsi_host_call *)(data + (ipa - page_ipa));

	if (rec_exit != NULL) {
		/* Copy host call arguments to REC exit data structure */
		rec_exit->imm = host_call->imm;
		for (i = 0U; i < RSI_HOST_CALL_NR_GPRS; i++) {
			rec_exit->gprs[i] = host_call->gprs[i];
		}
	} else {
		/* Copy host call results to host call data structure */
		for (i = 0U; i < RSI_HOST_CALL_NR_GPRS; i++) {
			host_call->gprs[i] = rec_entry->gprs[i];
		}
	}

	/* Unmap Realm data granule */
	buffer_unmap(data);

	/* Unlock last level RTT */
	granule_unlock(walk_result.llt);

	return ret;
}

struct rsi_host_call_result handle_rsi_host_call(struct rec *rec,
						 struct rmi_rec_exit *rec_exit)
{
	struct rsi_host_call_result res = { { false, 0UL } };
	unsigned long ipa = rec->regs[1];

	if (!ALIGNED(ipa, sizeof(struct rsi_host_call))) {
		res.smc_result = RSI_ERROR_INPUT;
		return res;
	}

	if ((ipa / GRANULE_SIZE) !=
		((ipa + sizeof(struct rsi_host_call) - 1UL) / GRANULE_SIZE)) {
		res.smc_result = RSI_ERROR_INPUT;
		return res;
	}

	if (!addr_in_rec_par(rec, ipa)) {
		res.smc_result = RSI_ERROR_INPUT;
		return res;
	}

	res.smc_result = do_host_call(rec, rec_exit, NULL, &res.walk_result);

	return res;
}

struct rsi_walk_result complete_rsi_host_call(struct rec *rec,
					      struct rmi_rec_entry *rec_entry)
{
	struct rsi_walk_result res = { false, 0UL };

	/*
	 * Do the necessary to walk the S2 RTTs and copy args from NS Host
	 * to the host call data structure. But it is possible for the
	 * RIPAS of the IPA to be EMPTY and hence this call can return
	 * RSI_ERROR_INPUT. In this case, we return RSI_SUCCESS to Realm
	 * and Realm may take an abort on accessing the IPA (depending on
	 * the RIPAS of IPA at that time). This is a situation which can be
	 * controlled from Realm and Realm should avoid this.
	 */
	(void)do_host_call(rec, NULL, rec_entry, &res);

	return res;
}
