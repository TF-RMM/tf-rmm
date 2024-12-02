/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <buffer.h>
#include <dev.h>
#include <granule.h>
#include <limits.h>
#include <realm.h>
#include <rsi-handler.h>
#include <smc-rsi.h>

void handle_rsi_rdev_get_instance_id(struct rec *rec,
				     struct rmi_rec_exit *rec_exit,
				     struct rsi_result *res)
{
	unsigned long rsi_rc;
	enum rsi_action rsi_action;
	struct rec_plane *plane = rec_active_plane(rec);
	if (!rec->da_enabled) {
		rsi_action = UPDATE_REC_RETURN_TO_REALM;
		rsi_rc = RSI_ERROR_STATE;
		goto set_rsi_action;
	}

	/* X1: Realm device identifier */
	rec->vdev.id = plane->regs[1];
	rec->vdev.inst_id_valid = false;
	rec_set_pending_op(rec, REC_PENDING_VDEV_COMPLETE);

	rec_exit->vdev_id = plane->regs[1];
	rec_exit->exit_reason = RMI_EXIT_VDEV_REQUEST;
	rsi_action = UPDATE_REC_EXIT_TO_HOST;

set_rsi_action:

	if (rsi_action == UPDATE_REC_RETURN_TO_REALM) {
		res->smc_res.x[0] = rsi_rc;
	}
	res->action = rsi_action;
}
