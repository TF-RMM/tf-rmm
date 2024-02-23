/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

/* This file is only used for CBMC analysis. */

#ifdef CBMC

#include <rec.h>
#include <rsi-handler.h>
#include <rsi-walk.h>
#include <stdbool.h>
#include <tb_common.h>

struct rsi_walk_result complete_rsi_host_call(struct rec *rec,
					      struct rmi_rec_enter *rec_enter)
{
	struct rsi_walk_result r = {0};

	ASSERT(false, "complete_rsi_host_call");
	return r;
}

void handle_rsi_host_call(struct rec *rec, struct rmi_rec_exit *rec_exit,
			  struct rsi_result *res)
{
	ASSERT(false, "handle_rsi_host_call");
}

#endif /* CBMC */
