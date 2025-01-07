/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch.h>
#include <arch_features.h>
#include <buffer.h>
#include <debug.h>
#include <dev.h>
#include <feature.h>
#include <granule.h>
#include <realm.h>
#include <sizes.h>
#include <smc-handler.h>
#include <smc-rmi.h>
#include <smc-rsi.h>
#include <string.h>
#include <utils_def.h>

static unsigned long validate_vdev_params(
	unsigned long vdev_params_ptr,
	struct rmi_vdev_params *vdev_params)
{
	struct granule *g_vdev_params;

	/* Map and copy VDEV parameters */
	g_vdev_params = find_granule(vdev_params_ptr);
	if ((g_vdev_params == NULL) ||
	    (granule_unlocked_state(g_vdev_params) != GRANULE_STATE_NS)) {
		return RMI_ERROR_INPUT;
	}

	if (!ns_buffer_read(SLOT_NS, g_vdev_params, 0U,
			    sizeof(struct rmi_vdev_params), vdev_params)) {
		return RMI_ERROR_INPUT;
	}

	if (vdev_params->num_aux != 0U) {
		return RMI_ERROR_INPUT;
	}

	if (vdev_params->flags != 0U) {
		return RMI_ERROR_INPUT;
	}

	/* TODO: Verify tdi_id is unique for the associated PDEV segment */

	/* TODO: Ensure vdev_id is within the rid bounds of PDEV */

	return RMI_SUCCESS;
}

/*
 * smc_vdev_create
 *
 * rd_addr		- PA of RD
 * pdev_ptr		- PA of the PDEV
 * vdev_ptr		- PA of the VDEV
 * vdev_params_ptr	- PA of VDEV parameters
 */
unsigned long smc_vdev_create(unsigned long rd_addr, unsigned long pdev_ptr,
			      unsigned long vdev_ptr,
			      unsigned long vdev_params_ptr)
{
	struct rmi_vdev_params vdev_params; /* this consumes 4k of stack */
	struct granule *g_rd;
	struct granule *g_pdev;
	struct granule *g_vdev;
	struct rd *rd;
	struct pdev *pd;
	struct vdev *vd;
	unsigned long rc;

	if (!is_rmi_feat_da_enabled()) {
		return SMC_NOT_SUPPORTED;
	}

	if (!GRANULE_ALIGNED(rd_addr) || !GRANULE_ALIGNED(pdev_ptr) ||
	    !GRANULE_ALIGNED(vdev_ptr) || !GRANULE_ALIGNED(vdev_params_ptr)) {
		return RMI_ERROR_INPUT;
	}

	/* coverity[uninit_use_in_call:SUPPRESS] */
	rc = validate_vdev_params(vdev_params_ptr, &vdev_params);
	if (rc != RMI_SUCCESS) {
		return rc;
	}

	if (!find_lock_two_granules(rd_addr, GRANULE_STATE_RD, &g_rd,
				    pdev_ptr, GRANULE_STATE_PDEV, &g_pdev)) {
		return RMI_ERROR_INPUT;
	}

	/* Lock vdev granule and map it */
	g_vdev = find_lock_granule(vdev_ptr, GRANULE_STATE_DELEGATED);
	if (g_vdev == NULL) {
		granule_unlock(g_rd);
		granule_unlock(g_pdev);
		return RMI_ERROR_INPUT;
	}

	rd = buffer_granule_map(g_rd, SLOT_RD);
	assert(rd != NULL);

	if (!rd->da_enabled) {
		rc = RMI_ERROR_REALM;
		goto out_unmap_rd;
	}

	/*
	 * Currently we only support a single VDEV per Realm.
	 * TODO: Revisit the following condition if multiple VDEV support is
	 * added.
	 */
	if (rd->g_vdev != NULL) {
		rc = RMI_ERROR_REALM;
		goto out_unmap_rd;
	}

	pd = buffer_granule_map(g_pdev, SLOT_PDEV);
	assert(pd != NULL);

	if (pd->rmi_state != RMI_PDEV_STATE_READY) {
		rc = RMI_ERROR_DEVICE;
		goto out_unmap_pd;
	}

	vd = buffer_granule_map(g_vdev, SLOT_VDEV);
	assert(vd != NULL);

	/* Initialize VDEV fields */
	vd->g_rd = g_rd;
	vd->g_pdev = g_pdev;

	vd->id = vdev_params.vdev_id;
	vd->tdi_id = vdev_params.tdi_id;

	/*
	 * Get the current VDEV instance id from RD and at the same time update
	 * the same.
	 */
	vd->inst_id = rd_vdev_inst_counter_inc(rd);

	vd->rmi_state = RMI_VDEV_STATE_READY;

	/* Initialize RDEV */
	vd->rdev.rsi_state = RSI_RDEV_STATE_UNLOCKED;
	vd->rdev.op = RDEV_OP_NONE;
	vd->rdev.vdev_ptr = vdev_ptr;

	/* Update Realm */
	rd->g_vdev = g_vdev;
	rd_vdev_refcount_inc(rd);

	/* Update PDEV */
	pd->num_vdevs += 1U;

	buffer_unmap(vd);
out_unmap_pd:
	buffer_unmap(pd);
out_unmap_rd:
	buffer_unmap(rd);

	if (rc == RMI_SUCCESS) {
		granule_unlock_transition(g_vdev, GRANULE_STATE_VDEV);
	} else {
		granule_unlock(g_vdev);
	}
	granule_unlock(g_pdev);
	granule_unlock(g_rd);

	return rc;
}

/*
 * Completes a pending VDEV request.
 *
 * rec_ptr		- PA of RD
 * vdev_ptr		- PA of the VDEV
 */
unsigned long smc_vdev_complete(unsigned long rec_ptr, unsigned long vdev_ptr)
{
	struct granule *g_rec;
	struct granule *g_vdev;
	struct rec *rec;
	struct vdev *vd;
	struct rec_plane *plane;
	unsigned long rmi_rc;

	if (!is_rmi_feat_da_enabled()) {
		return SMC_NOT_SUPPORTED;
	}

	if (!GRANULE_ALIGNED(rec_ptr) || !GRANULE_ALIGNED(vdev_ptr)) {
		return RMI_ERROR_INPUT;
	}

	/* Lock REC granule and map it */
	g_rec = find_lock_granule(rec_ptr, GRANULE_STATE_REC);
	if (g_rec == NULL) {
		return RMI_ERROR_INPUT;
	}
	rec = buffer_granule_map(g_rec, SLOT_REC);
	assert(rec != NULL);

	/* Lock VDEV granule and map it */
	g_vdev = find_lock_granule(vdev_ptr, GRANULE_STATE_VDEV);
	if (g_vdev == NULL) {
		rmi_rc = RMI_ERROR_INPUT;
		goto out_unmap_rec;
	}
	vd = buffer_granule_map(g_vdev, SLOT_VDEV);
	assert(vd != NULL);

	/* Check if the REC pending operation is for VDEV request */
	if ((rec->pending_op != REC_PENDING_VDEV_COMPLETE)) {
		rmi_rc = RMI_ERROR_INPUT;
		goto out_unmap_vdev;
	}

	/* Check the Realm owner and the Device ID of the REC and VDEV */
	if ((rec->realm_info.g_rd != vd->g_rd) || (rec->vdev.id != vd->id)) {
		rmi_rc = RMI_ERROR_INPUT;
		goto out_unmap_vdev;
	}

	plane = rec_active_plane(rec);

	if (rec->vdev.inst_id_valid) {
		/* Compare instance id */
		if (rec->vdev.inst_id == vd->inst_id) {
			plane->regs[0] = RSI_SUCCESS;
			/* todo: Update VDEV comm state */
			rmi_rc = RMI_SUCCESS;
		} else {
			rmi_rc = RMI_ERROR_INPUT;
		}
	} else {
		/* Get instance id */
		plane->regs[0] = RSI_SUCCESS;
		plane->regs[1] = vd->inst_id;
		rmi_rc = RMI_SUCCESS;
	}

	if (rmi_rc == RMI_SUCCESS) {
		/* Cache the vdev granule */
		rec->vdev.g_vdev = g_vdev;

		/* Clear the REC pending request operation */
		rec_set_pending_op(rec, REC_PENDING_NONE);
	}

out_unmap_vdev:
	buffer_unmap(vd);
	granule_unlock(g_vdev);
out_unmap_rec:
	buffer_unmap(rec);
	granule_unlock(g_rec);

	return rmi_rc;
}

/*
 * smc_vdev_communicate
 *
 * pdev_ptr	- PA of the PDEV
 * vdev_ptr	- PA of the VDEV
 * data_ptr	- PA of the communication data structure
 */
unsigned long smc_vdev_communicate(unsigned long pdev_ptr,
				   unsigned long vdev_ptr,
				   unsigned long dev_comm_data_ptr)
{
	struct granule *g_pdev = NULL;
	struct granule *g_vdev = NULL;
	struct granule *g_dev_comm_data;
	struct pdev *pd = NULL;
	struct vdev *vd = NULL;
	unsigned long rmi_rc;

	if (!is_rmi_feat_da_enabled()) {
		return SMC_NOT_SUPPORTED;
	}

	if (!GRANULE_ALIGNED(pdev_ptr) || !GRANULE_ALIGNED(vdev_ptr) ||
	    !GRANULE_ALIGNED(dev_comm_data_ptr)) {
		return RMI_ERROR_INPUT;
	}

	/* Map PDEV and VDEV. */
	g_pdev = find_lock_granule(pdev_ptr, GRANULE_STATE_PDEV);
	if (g_pdev == NULL) {
		return RMI_ERROR_INPUT;
	}

	pd = buffer_granule_map(g_pdev, SLOT_PDEV);
	assert(pd != NULL);

	g_vdev = find_lock_granule(vdev_ptr, GRANULE_STATE_VDEV);
	if (g_vdev == NULL) {
		rmi_rc = RMI_ERROR_INPUT;
		goto out_error;
	}

	vd = buffer_granule_map(g_vdev, SLOT_VDEV);
	assert(vd != NULL);

	if (vd->g_pdev != g_pdev) {
		rmi_rc = RMI_ERROR_INPUT;
		goto out_error;
	}

	g_dev_comm_data = find_granule(dev_comm_data_ptr);
	if ((g_dev_comm_data == NULL) ||
		(granule_unlocked_state(g_dev_comm_data) != GRANULE_STATE_NS)) {
		rmi_rc = RMI_ERROR_INPUT;
		goto out_error;
	}

	if (vd->rmi_state == RMI_VDEV_STATE_COMMUNICATING) {
		if (vd->rdev.op == RDEV_OP_NONE) {
			rmi_rc = RMI_ERROR_DEVICE;
			goto out_error;
		}
	} else if (vd->rmi_state != RMI_VDEV_STATE_STOPPING) {
		rmi_rc = RMI_ERROR_DEVICE;
		goto out_error;
	}

	rmi_rc = dev_communicate(pd, vd, g_dev_comm_data);
	/* Do not return early here in case of error. Instead do the state
	 * transition below based on pd->dev_comm_state set by dev_communicate.
	 */

	/*
	 * Transistion VDEV state based on device communication state. VDEV
	 * do not have dev_comm state as there is only one session to the device
	 * which is created and maintained by PDEV. So use PDEV's comm_state to
	 * update VDEV rmi_state.
	 */
	switch (pd->dev_comm_state) {
	case DEV_COMM_ERROR:
		if (vd->rmi_state == RMI_VDEV_STATE_STOPPING) {
			vd->rmi_state = RMI_VDEV_STATE_STOPPED;
		} else {
			vd->rmi_state = RMI_VDEV_STATE_ERROR;
		}
		break;
	case DEV_COMM_IDLE:
		/*
		 * Last device communication is completed, move the PDEV state
		 * to next state based on the current state.
		 */
		if (vd->rmi_state == RMI_VDEV_STATE_COMMUNICATING) {
			vd->rmi_state = RMI_VDEV_STATE_READY;
		} else if (vd->rmi_state == RMI_VDEV_STATE_STOPPING) {
			vd->rmi_state = RMI_VDEV_STATE_STOPPED;
		} else {
			/*
			 * Transition to error as Host can trigger vdev
			 * communicate in IDLE state.
			 */
			vd->rmi_state = RMI_VDEV_STATE_ERROR;
		}
		break;
	case DEV_COMM_ACTIVE:
		/* No state change required */
		break;
	case DEV_COMM_PENDING:
		ERROR("VDEV Communicate: Dev comm state is Pending due of communication error.\n");
		break;
	default:
		assert(false);
	}

	rdev_state_transition(&vd->rdev, pd->dev_comm_state);

out_error:
	if (vd != NULL) {
		buffer_unmap(vd);
	}
	if (g_vdev != NULL) {
		granule_unlock(g_vdev);
	}
	if (pd != NULL) {
		buffer_unmap(pd);
	}
	granule_unlock(g_pdev);

	return rmi_rc;
}
