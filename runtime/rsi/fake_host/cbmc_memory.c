/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

/* This file is only used for CBMC analysis. */

#ifdef CBMC

#include <rec.h>
#include <rsi-handler.h>
#include <tb_common.h>

void handle_rsi_ipa_state_set(struct rec *rec,
			      struct rmi_rec_exit *rec_exit,
			      struct rsi_result *res)
{
	ASSERT(false, "handle_rsi_ipa_state_set");
}

void handle_rsi_ipa_state_get(struct rec *rec,
			      struct rsi_result *res)
{
	ASSERT(false, "handle_rsi_ipa_state_get");
}

void handle_rsi_mem_set_perm_index(struct rec *rec,
				   struct rmi_rec_exit *rec_exit,
				   struct rsi_result *res)
{
	ASSERT(false, "handle_rsi_mem_set_perm_index");
}

void handle_rsi_mem_set_perm_value(struct rec *rec, struct rsi_result *res)
{
	ASSERT(false, "handle_rsi_mem_set_perm_value");
}

void handle_rsi_mem_get_perm_value(struct rec *rec, struct rsi_result *res)
{
	ASSERT(false, "handle_rsi_mem_get_perm_value");
}

#endif /* CBMC */
