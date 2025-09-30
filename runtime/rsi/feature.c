/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <feature.h>
#include <rec.h>
#include <rsi-handler.h>

void handle_rsi_features(struct rec *rec, struct rsi_result *res)
{
	struct rec_plane *plane;

	/* This command returns to Realm with RSI_SUCCESS */
	res->action = UPDATE_REC_RETURN_TO_REALM;
	res->smc_res.x[0] = RSI_SUCCESS;

	/* RSI calls can only be issued by Plane 0 */
	plane = rec_plane_0(rec);

	if (plane->regs[1] == RSI_FEATURE_REGISTER_0_INDEX) {
		res->smc_res.x[1] = rec->realm_info.cached_rsi_feature_reg0;
	} else {
		res->smc_res.x[1] = 0UL;
	}
}
