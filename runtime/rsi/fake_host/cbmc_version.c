/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

/* This file is only used for CBMC analysis. */

#ifdef CBMC

#include <rec.h>
#include <rsi-handler.h>
#include <tb_common.h>

unsigned long rsi_get_highest_supported_version(void)
{
	ASSERT(false, "rsi_get_highest_supported_version");
	return 0UL;
}

void handle_rsi_version(struct rec *rec, struct rsi_result *res)
{
	ASSERT(false, "handle_rsi_version");
}

#endif /* CBMC */
