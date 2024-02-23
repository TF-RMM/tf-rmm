/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

/* This file is only used for CBMC analysis. */

#ifdef CBMC

#include <rec.h>
#include <rsi-handler.h>
#include <tb_common.h>

void handle_rsi_attest_token_init(struct rec *rec, struct rsi_result *res)
{
	ASSERT(false, "handle_rsi_attest_token_init");
}

void handle_rsi_attest_token_continue(struct rec *rec,
				      struct rmi_rec_exit *rec_exit,
				      struct rsi_result *res)
{
	ASSERT(false, "handle_rsi_attest_token_continue");
}

void handle_rsi_measurement_read(struct rec *rec, struct rsi_result *res)
{
	ASSERT(false, "handle_rsi_measurement_read");
}

void handle_rsi_measurement_extend(struct rec *rec, struct rsi_result *res)
{
	ASSERT(false, "handle_rsi_measurement_extend");
}

#endif /* CBMC */
