/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <buffer.h>
#include <gic.h>
#include <granule.h>
#include <realm.h>
#include <rsi-handler.h>
#include <smc-rsi.h>

COMPILER_ASSERT(RSI_RPV_SIZE == RPV_SIZE);

void handle_rsi_realm_config(struct rec *rec, struct rsi_result *res)
{
	struct rec_plane *plane = rec_active_plane(rec);
	unsigned long ipa;
	struct granule *llt = NULL;
	struct rsi_realm_config *config = NULL;
	struct rd *rd;

	assert(plane != NULL);

	ipa = plane->regs[1];

	res->action = UPDATE_REC_RETURN_TO_REALM;

	if (!GRANULE_ALIGNED(ipa) || !addr_in_rec_par(rec, ipa)) {
		res->smc_res.x[0] = RSI_ERROR_INPUT;
		return;
	}

	if (!realm_mem_lock_map(rec, ipa, (void **)&config, &llt, res)) {
		/* In case of failure res is updated */
		return;
	}

	assert((config != NULL) && (llt != NULL));

	/* Populate config structure */
	config->ipa_width = rec->realm_info.primary_s2_ctx.ipa_bits;
	if (rec->realm_info.algorithm == HASH_SHA_256) {
		config->algorithm = RSI_HASH_SHA_256;
	} else {
		config->algorithm = RSI_HASH_SHA_512;
	}

	config->num_aux_planes = rec->realm_info.num_aux_planes;
	config->gicv3_vtr = (unsigned int)gic_get_ich_vtr();

	/* Map rd granule */
	rd = buffer_granule_map(rec->realm_info.g_rd, SLOT_RD);
	assert(rd != NULL);

	config->ats_plane = rd->ats_plane;

	/* Populate Realm Personalization Value */
	(void)memcpy(config->rpv, rd->rpv, RSI_RPV_SIZE);

	/* Unmap rd granule */
	buffer_unmap(rd);

	/* Unmap Realm data granule */
	buffer_unmap(config);

	/* Unlock last level RTT */
	granule_unlock(llt);

	/* Write output values */
	res->smc_res.x[0] = RSI_SUCCESS;
}
