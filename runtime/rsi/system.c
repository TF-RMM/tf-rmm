/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */
#include <assert.h>
#include <rsi-handler.h>
#include <smc-rsi.h>

COMPILER_ASSERT(RSI_ABI_VERSION_MAJOR <= 0x7FFF);
COMPILER_ASSERT(RSI_ABI_VERSION_MINOR <= 0xFFFF);

void handle_rsi_version(struct rsi_result *res)
{
	res->action = UPDATE_REC_RETURN_TO_REALM;
	res->smc_res.x[0] = RSI_ABI_VERSION;
}
