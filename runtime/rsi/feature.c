/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */
#include <rec.h>
#include <rsi-handler.h>
#include <smc-rsi.h>

void handle_rsi_features(struct rec *rec, struct rsi_result *res)
{
	(void)rec;

	res->action = UPDATE_REC_RETURN_TO_REALM;
	res->smc_res.x[0] = RSI_SUCCESS;

	/* Return zero regardless of the index provided */
	res->smc_res.x[1] = 0UL;
}
