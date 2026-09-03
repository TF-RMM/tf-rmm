/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <granule.h>
#include <realm.h>
#include <rec.h>
#include <rsi-handler.h>
#include <smc-rsi.h>

void handle_rsi_arch_dev_activate(struct rec *rec, struct rsi_result *res)
{
	struct rec_plane *plane = rec_plane_0(rec);
	unsigned long base = plane->regs[1U];
	unsigned long dev_type = plane->regs[2U];

	res->action = UPDATE_REC_RETURN_TO_REALM;

	if (!GRANULE_ALIGNED(base) || !addr_in_rec_par(rec, base) ||
	    (dev_type != RSI_ARCH_DEV_SMMUV3)) {
		res->smc_res.x[0U] = RSI_ERROR_INPUT;
		return;
	}

	/*
	 * TODO: Walk the primary RTT and check for RTTE_ARCH_DEV, ensure the
	 * referenced VSMMU is inactive, and verify RIPAS_DEV over its range.
	 */

	/* To be implemented: activate the architectural device. */
	/* To be implemented: replace this dummy result when activation exists. */
	res->smc_res.x[0U] = RSI_SUCCESS;
}
