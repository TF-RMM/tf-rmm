/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

/* This file is only used for CBMC analysis. */

#ifdef CBMC

#include <rec.h>
#include <rsi-handler.h>
#include <tb_common.h>

void handle_rsi_plane_enter(struct rec *rec, struct rsi_result *res)
{
	ASSERT(false, "handle_rsi_plane_enter");
}

void handle_rsi_plane_sysreg_read(struct rec *rec, struct rsi_result *res)
{
	ASSERT(false, "handle_rsi_plane_sysreg_read");
}

void handle_rsi_plane_sysreg_write(struct rec *rec, struct rsi_result *res)
{
	ASSERT(false, "handle_rsi_plane_sysreg_write");
}

#endif /* CBMC */
