/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

/* This file is only used for CBMC analysis. */

#ifdef CBMC

#include <rec.h>
#include <rsi-handler.h>
#include <tb_common.h>

unsigned long psci_complete_request(struct rec *calling_rec,
				    struct rec *target_rec, unsigned long status)
{
	ASSERT(false, "psci_complete_request");
	return 0UL;
}

void handle_psci(struct rec *rec, struct rmi_rec_exit *rec_exit,
		 struct rsi_result *res)
{
	ASSERT(false, "handle_psci");
}

#endif /* CBMC */
