/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch.h>
#include <arch_features.h>
#include <buffer.h>
#include <debug.h>
#include <dev.h>
#include <dev_assign_app.h>
#include <feature.h>
#include <granule.h>
#include <random_app.h>
#include <realm.h>
#include <sizes.h>
#include <smc-handler.h>
#include <smc-rmi.h>
#include <smc-rsi.h>
#include <smmuv3.h>
#include <string.h>
#include <utils_def.h>

static unsigned long validate_vdev_params(
	unsigned long vdev_params_addr,
	struct rmi_vdev_params *vdev_params)
{
	struct granule *g_vdev_params;

	/* Map and copy VDEV parameters */
	g_vdev_params = find_granule(vdev_params_addr);
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
 * pdev_addr		- PA of the PDEV
 * vdev_addr		- PA of the VDEV
 * vdev_params_addr	- PA of VDEV parameters
 */
unsigned long smc_vdev_create(unsigned long rd_addr, unsigned long pdev_addr,
			      unsigned long vdev_addr,
			      unsigned long vdev_params_addr)
{
	struct rmi_vdev_params vdev_params; /* this consumes 4KB of stack */
	struct granule *g_rd;
	struct granule *g_pdev;
	struct granule *g_vdev;
	struct rd *rd;
	struct pdev *pd;
	struct vdev *vd;
	struct s2tt_context *plane_0_s2_context;
	struct smmu_stg2_config s2_cfg;
	unsigned long rc;

	if (!is_rmi_feat_da_enabled()) {
		return SMC_NOT_SUPPORTED;
	}

	if (!GRANULE_ALIGNED(rd_addr) || !GRANULE_ALIGNED(pdev_addr) ||
	    !GRANULE_ALIGNED(vdev_addr) || !GRANULE_ALIGNED(vdev_params_addr)) {
		return RMI_ERROR_INPUT;
	}

	/* coverity[uninit_use_in_call:SUPPRESS] */
	rc = validate_vdev_params(vdev_params_addr, &vdev_params);
	if (rc != RMI_SUCCESS) {
		return rc;
	}

	if (!find_lock_two_granules(rd_addr, GRANULE_STATE_RD, &g_rd,
				    pdev_addr, GRANULE_STATE_PDEV, &g_pdev)) {
		return RMI_ERROR_INPUT;
	}

	/* Lock vdev granule and map it */
	g_vdev = find_lock_granule(vdev_addr, GRANULE_STATE_DELEGATED);
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

	if (EXTRACT(RMI_PDEV_FLAGS_CATEGORY, pd->rmi_flags) != RMI_PDEV_SMEM) {
		rc = RMI_ERROR_DEVICE;
		goto out_unmap_pd;
	}

	vd = buffer_granule_map(g_vdev, SLOT_VDEV);
	assert(vd != NULL);

	plane_0_s2_context = plane_to_s2_context(rd, PLANE_0_ID);

	s2_cfg.s2ttb = granule_addr(plane_0_s2_context->g_rtt) & MASK(TTBRx_EL2_BADDR);
	s2_cfg.vtcr = realm_vtcr(rd);
	s2_cfg.vmid = plane_0_s2_context->vmid;

	if ((smmuv3_allocate_ste(SMMU_IDX, (unsigned int)vdev_params.tdi_id) != 0) ||
	    (smmuv3_configure_stream(SMMU_IDX, &s2_cfg,
					(unsigned int)vdev_params.tdi_id) != 0)) {
		rc = RMI_ERROR_DEVICE;
		goto out_unmap_vd;
	}

	/* Initialize VDEV fields */
	vd->g_rd = g_rd;
	vd->g_pdev = g_pdev;

	/* TODO_ALP17: check whether vdev_id and tdi_id are free */
	vd->id = vdev_params.vdev_id;
	vd->tdi_id = vdev_params.tdi_id;

	vd->rmi_state = RMI_VDEV_STATE_NEW;
	vd->dma_state = RMI_VDEV_DMA_DISABLED;
	vd->op = VDEV_OP_UNLOCK;
	vd->comm_state = DEV_COMM_PENDING;
	vd->num_map = 0U;
	vd->attest_info = (struct vdev_attest_info){0u, 0U, 0U};

	/* Update Realm */
	rd->g_vdev = g_vdev;
	rd_vdev_refcount_inc(rd);

	/* Update PDEV */
	pd->num_vdevs++;

out_unmap_vd:
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
 * smc_vdev_lock
 *
 * rd_addr		- PA of RD
 * pdev_addr		- PA of the PDEV
 * vdev_addr		- PA of the VDEV
 */
unsigned long smc_vdev_lock(unsigned long rd_addr, unsigned long pdev_addr,
			      unsigned long vdev_addr)
{
	struct granule *g_rd;
	struct granule *g_pdev;
	struct granule *g_vdev;
	struct vdev *vdev;
	unsigned long rmi_rc;
	struct dev_tdisp_params *tdisp_params;

	if (!is_rmi_feat_da_enabled()) {
		return SMC_NOT_SUPPORTED;
	}

	if (!GRANULE_ALIGNED(rd_addr) || !GRANULE_ALIGNED(pdev_addr) ||
	    !GRANULE_ALIGNED(vdev_addr)) {
		return RMI_ERROR_INPUT;
	}

	g_rd = find_granule(rd_addr);
	if ((g_rd == NULL) ||
	    (granule_unlocked_state(g_rd) != GRANULE_STATE_RD)) {
		return RMI_ERROR_INPUT;
	}

	g_pdev = find_granule(pdev_addr);
	if ((g_pdev == NULL) ||
	    (granule_unlocked_state(g_pdev) != GRANULE_STATE_PDEV)) {
		return RMI_ERROR_INPUT;
	}

	g_vdev = find_lock_granule(vdev_addr, GRANULE_STATE_VDEV);
	if (g_vdev == NULL) {
		return RMI_ERROR_INPUT;
	}

	vdev = buffer_granule_map(g_vdev, SLOT_VDEV);
	assert(vdev != NULL);

	if (vdev->g_rd != g_rd) {
		rmi_rc = RMI_ERROR_INPUT;
		goto out;
	}

	if ((vdev->g_pdev != g_pdev) ||
	    (vdev->rmi_state != RMI_VDEV_STATE_UNLOCKED) ||
	    (vdev->comm_state != DEV_COMM_IDLE)) {
		rmi_rc = RMI_ERROR_DEVICE;
		goto out;
	}

	/* Set TDISP parameters */
	tdisp_params = &vdev->op_params.tdisp_params;
	(void)memset(tdisp_params, 0, sizeof(struct dev_tdisp_params));
	(void)memset(vdev->start_interface_nonce, 0,
		     sizeof(vdev->start_interface_nonce));

	tdisp_params->tdi_id = (uint32_t)(vdev->tdi_id & 0xffffUL);
	tdisp_params->start_interface_nonce = vdev->start_interface_nonce;

	vdev->op = VDEV_OP_LOCK;
	vdev->comm_state = DEV_COMM_PENDING;
	rmi_rc = RMI_SUCCESS;

out:
	buffer_unmap(vdev);
	granule_unlock(g_vdev);

	return rmi_rc;
}

/*
 * smc_vdev_start
 *
 * rd_addr		- PA of RD
 * pdev_addr		- PA of the PDEV
 * vdev_addr		- PA of the VDEV
 */
unsigned long smc_vdev_start(unsigned long rd_addr, unsigned long pdev_addr,
			      unsigned long vdev_addr)
{
	struct granule *g_rd;
	struct granule *g_pdev;
	struct granule *g_vdev;
	struct vdev *vdev;
	unsigned long rmi_rc;
	struct dev_tdisp_params *tdisp_params;

	if (!is_rmi_feat_da_enabled()) {
		return SMC_NOT_SUPPORTED;
	}

	if (!GRANULE_ALIGNED(rd_addr) || !GRANULE_ALIGNED(pdev_addr) ||
	    !GRANULE_ALIGNED(vdev_addr)) {
		return RMI_ERROR_INPUT;
	}

	g_rd = find_granule(rd_addr);
	if ((g_rd == NULL) ||
	    (granule_unlocked_state(g_rd) != GRANULE_STATE_RD)) {
		return RMI_ERROR_INPUT;
	}

	g_pdev = find_granule(pdev_addr);
	if ((g_pdev == NULL) ||
	    (granule_unlocked_state(g_pdev) != GRANULE_STATE_PDEV)) {
		return RMI_ERROR_INPUT;
	}

	g_vdev = find_lock_granule(vdev_addr, GRANULE_STATE_VDEV);
	if (g_vdev == NULL) {
		return RMI_ERROR_INPUT;
	}

	vdev = buffer_granule_map(g_vdev, SLOT_VDEV);
	assert(vdev != NULL);

	if (vdev->g_rd != g_rd) {
		rmi_rc = RMI_ERROR_INPUT;
		goto out;
	}

	if ((vdev->g_pdev != g_pdev) ||
	    (vdev->rmi_state != RMI_VDEV_STATE_LOCKED) ||
	    (vdev->comm_state != DEV_COMM_IDLE)) {
		rmi_rc = RMI_ERROR_DEVICE;
		goto out;
	}

	/* Set TDISP parameters */
	tdisp_params = &vdev->op_params.tdisp_params;
	(void)memset(tdisp_params, 0, sizeof(struct dev_tdisp_params));

	tdisp_params->tdi_id = (uint32_t)(vdev->tdi_id & 0xffffUL);
	tdisp_params->start_interface_nonce = vdev->start_interface_nonce;

	vdev->op = VDEV_OP_START;
	vdev->comm_state = DEV_COMM_PENDING;
	rmi_rc = RMI_SUCCESS;

out:
	buffer_unmap(vdev);
	granule_unlock(g_vdev);

	return rmi_rc;
}

/*
 * Completes a pending VDEV request.
 *
 * rec_addr		- PA of REC
 * vdev_addr		- PA of the VDEV
 */
unsigned long smc_vdev_complete(unsigned long rec_addr, unsigned long vdev_addr)
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

	if (!GRANULE_ALIGNED(rec_addr) || !GRANULE_ALIGNED(vdev_addr)) {
		return RMI_ERROR_INPUT;
	}

	/* Lock REC granule and map it */
	g_rec = find_lock_granule(rec_addr, GRANULE_STATE_REC);
	if (g_rec == NULL) {
		return RMI_ERROR_INPUT;
	}
	rec = buffer_granule_map(g_rec, SLOT_REC);
	assert(rec != NULL);

	/* Lock VDEV granule and map it */
	g_vdev = find_lock_granule(vdev_addr, GRANULE_STATE_VDEV);
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

/* Generate random numbers as nonce
 * Returns 0 on success.
 */
static int generate_attest_info_nonce(unsigned long *nonce)
{
	struct app_data_cfg *random_app_data = random_app_get_data_cfg();

	assert(nonce != NULL);
	return random_app_prng_get_random(random_app_data, (uint8_t *)nonce, sizeof(*nonce));
}

/*
 * smc_vdev_communicate
 *
 * rd_addr		- PA of the RD
 * pdev_addr		- PA of the PDEV
 * vdev_addr		- PA of the VDEV
 * dev_comm_data_addr	- PA of the communication data structure
 */
unsigned long smc_vdev_communicate(unsigned long rd_addr,
				   unsigned long pdev_addr,
				   unsigned long vdev_addr,
				   unsigned long dev_comm_data_addr)
{
	struct granule *g_pdev = NULL;
	struct granule *g_vdev = NULL;
	struct granule *g_dev_comm_data;
	struct granule *g_rd = NULL;
	struct pdev *pd = NULL;
	struct vdev *vd = NULL;
	unsigned long rmi_rc;

	if (!is_rmi_feat_da_enabled()) {
		return SMC_NOT_SUPPORTED;
	}

	if (!GRANULE_ALIGNED(rd_addr) || !GRANULE_ALIGNED(pdev_addr) ||
	    !GRANULE_ALIGNED(vdev_addr) || !GRANULE_ALIGNED(dev_comm_data_addr)) {
		return RMI_ERROR_INPUT;
	}

	/* Check RD */
	g_rd = find_granule(rd_addr);
	if ((g_rd == NULL) ||
	    (granule_unlocked_state(g_rd) != GRANULE_STATE_RD)) {
		return RMI_ERROR_INPUT;
	}

	/* Map PDEV and VDEV. */
	g_pdev = find_lock_granule(pdev_addr, GRANULE_STATE_PDEV);
	if (g_pdev == NULL) {
		return RMI_ERROR_INPUT;
	}

	pd = buffer_granule_map(g_pdev, SLOT_PDEV);
	assert(pd != NULL);

	g_vdev = find_lock_granule(vdev_addr, GRANULE_STATE_VDEV);
	if (g_vdev == NULL) {
		rmi_rc = RMI_ERROR_INPUT;
		goto out;
	}

	vd = buffer_granule_map(g_vdev, SLOT_VDEV);
	assert(vd != NULL);

	if (vd->g_rd != g_rd) {
		rmi_rc = RMI_ERROR_INPUT;
		goto out;
	}

	g_dev_comm_data = find_granule(dev_comm_data_addr);
	if ((g_dev_comm_data == NULL) ||
		(granule_unlocked_state(g_dev_comm_data) != GRANULE_STATE_NS)) {
		rmi_rc = RMI_ERROR_INPUT;
		goto out;
	}

	if (vd->g_pdev != g_pdev) {
		rmi_rc = RMI_ERROR_DEVICE;
		goto out;
	}

	/* TODO_ALP17: if PdevIsBusy(pdev) then ResultEqual(result, RMI_BUSY) */

	rmi_rc = dev_communicate(pd, vd, g_dev_comm_data);
	/* Do not return early here in case of error. Instead do the state
	 * transition below based on pd->dev_comm_state set by dev_communicate.
	 */

	/*
	 * Transistion VDEV state based on device communication state.
	 */
	if (vd->comm_state == DEV_COMM_ERROR) {
		vd->rmi_state = RMI_VDEV_STATE_ERROR;
	} else if (vd->comm_state == DEV_COMM_IDLE) {
		switch (vd->op) {
		case VDEV_OP_UNLOCK:
			vd->rmi_state = RMI_VDEV_STATE_UNLOCKED;
			break;
		case VDEV_OP_LOCK:
			vd->rmi_state = RMI_VDEV_STATE_LOCKED;
			/* coverity[overrun-buffer-val:SUPPRESS] */
			if (generate_attest_info_nonce(&(vd->attest_info.lock_nonce)) != 0) {
				vd->rmi_state = RMI_VDEV_STATE_ERROR;
			}
			break;
		case VDEV_OP_START:
			vd->rmi_state = RMI_VDEV_STATE_STARTED;
			break;
		case VDEV_OP_GET_MEAS:
			/* The get measurement operation doesn't change the VDEV's state */
			/* coverity[overrun-buffer-val:SUPPRESS] */
			if (generate_attest_info_nonce(&(vd->attest_info.meas_nonce)) != 0) {
				vd->rmi_state = RMI_VDEV_STATE_ERROR;
			}
			break;
		case VDEV_OP_GET_REPORT:
			/* The get if report operation doesn't change the VDEV's state */
			/* coverity[overrun-buffer-val:SUPPRESS] */
			if (generate_attest_info_nonce(&(vd->attest_info.report_nonce)) != 0) {
				vd->rmi_state = RMI_VDEV_STATE_ERROR;
			}
			break;
		default:
			assert(false);
		}
		vd->op = VDEV_OP_NONE;
	}

out:
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

/*
 * smc_vdev_aux_count
 *
 * Get number of auxiliary Granules required for a VDEV.
 *
 * pdev_flags	- PDEV flags
 * vdev_flags	- VDEV flags
 * res		- SMC result
 */
void smc_vdev_aux_count(unsigned long pdev_flags, unsigned long vdev_flags,
			struct smc_result *res)
{
	/* VDEV aux granules will be enabled when VSMMU support is enabled */
	(void)pdev_flags;
	(void)vdev_flags;

	if (is_rmi_feat_da_enabled()) {
		res->x[0] = RMI_SUCCESS;
		res->x[1] = 0UL;
	} else {
		res->x[0] = SMC_NOT_SUPPORTED;
	}
}

/*
 * smc_vdev_get_state
 *
 * Get state of a VDEV.
 *
 * vdev_addr	- PA of the VDEV
 * res		- SMC result
 */
void smc_vdev_get_state(unsigned long vdev_addr, struct smc_result *res)
{
	struct granule *g_vdev;
	struct vdev *vd;

	if (!is_rmi_feat_da_enabled()) {
		res->x[0] = SMC_NOT_SUPPORTED;
		return;
	}

	if (!GRANULE_ALIGNED(vdev_addr)) {
		goto out_err_input;
	}

	/* Lock vdev granule and map it */
	g_vdev = find_lock_granule(vdev_addr, GRANULE_STATE_VDEV);
	if (g_vdev == NULL) {
		goto out_err_input;
	}

	vd = buffer_granule_map(g_vdev, SLOT_VDEV);
	assert(vd != NULL);

	res->x[0] = RMI_SUCCESS;
	res->x[1] = vd->rmi_state;

	buffer_unmap(vd);
	granule_unlock(g_vdev);

	return;

out_err_input:
	res->x[0] = RMI_ERROR_INPUT;
}

/*
 * smc_vdev_abort
 *
 * vdev_addr	- PA of the VDEV
 */
unsigned long smc_vdev_abort(unsigned long vdev_addr)
{
	int rc __unused;
	struct granule *g_pdev;
	struct granule *g_vdev;
	void *aux_mapped_addr;
	unsigned long smc_rc;
	struct pdev *pd;
	struct vdev *vd;

	if (!is_rmi_feat_da_enabled()) {
		return SMC_NOT_SUPPORTED;
	}

	if (!GRANULE_ALIGNED(vdev_addr)) {
		return RMI_ERROR_INPUT;
	}

	/* Lock the vdev granule and map it, to get the pdev granule address. */
	g_vdev = find_lock_granule(vdev_addr, GRANULE_STATE_VDEV);
	if (g_vdev == NULL) {
		return RMI_ERROR_INPUT;
	}

	vd = buffer_granule_map(g_vdev, SLOT_VDEV);
	assert(vd != NULL);

	g_pdev = vd->g_pdev;

	/*
	 * To lock and map pdev, we first need to unlock vdev, and lock the
	 * granules again in the pdev-vdev order, so locking order is
	 * maintained.
	 */
	buffer_unmap(vd);
	granule_unlock(g_vdev);

	granule_lock(g_pdev, GRANULE_STATE_PDEV);
	pd = buffer_granule_map(g_pdev, SLOT_PDEV);
	assert(pd != NULL);

	granule_lock(g_vdev, GRANULE_STATE_VDEV);
	vd = buffer_granule_map(g_vdev, SLOT_VDEV);
	assert(vd != NULL);

	if (vd->comm_state == DEV_COMM_IDLE) {
		smc_rc = RMI_ERROR_DEVICE;
		goto out_vdev_buf_unmap;
	}

	/*
	 * If there is no active device communication, then mapping aux
	 * granules and cancelling an existing communication is not required.
	 *
	 * todo: add helper routine dev_communicate_abort() in pdev.c
	 */
	if (pd->dev_comm_state != DEV_COMM_ACTIVE) {
		goto vdev_reset_state;
	}

	/* Map PDEV aux granules */
	/* coverity[overrun-buffer-val:SUPPRESS] */
	aux_mapped_addr = buffer_pdev_aux_granules_map(pd->g_aux, pd->num_aux);
	assert(aux_mapped_addr != NULL);

	/*
	 * This will resume the blocked CMA SPDM command and the recv callback
	 * handler will return error and abort the command.
	 */
	rc = dev_assign_abort_app_operation(&pd->da_app_data);
	assert(rc == 0);

	/* Unmap all PDEV aux granules */
	buffer_pdev_aux_unmap(aux_mapped_addr, pd->num_aux);

vdev_reset_state:
	vd->rmi_state = RMI_VDEV_STATE_ERROR;
	vd->comm_state = DEV_COMM_IDLE;
	smc_rc = RMI_SUCCESS;

out_vdev_buf_unmap:
	buffer_unmap(vd);
	granule_unlock(g_vdev);
	buffer_unmap(pd);
	granule_unlock(g_pdev);

	return smc_rc;
}

/*
 * smc_vdev_destroy
 *
 * rd_addr	- PA of RD
 * pdev_addr	- PA of the PDEV
 * vdev_addr	- PA of the VDEV
 */
unsigned long smc_vdev_destroy(unsigned long rd_addr, unsigned long pdev_addr,
			       unsigned long vdev_addr)
{
	struct granule *g_rd = NULL;
	struct granule *g_pdev = NULL;
	struct granule *g_vdev = NULL;
	struct rd *rd = NULL;
	struct pdev *pd = NULL;
	struct vdev *vd = NULL;
	unsigned long smc_rc;

	if (!is_rmi_feat_da_enabled()) {
		return SMC_NOT_SUPPORTED;
	}

	if (!GRANULE_ALIGNED(rd_addr) || !GRANULE_ALIGNED(pdev_addr) ||
	    !GRANULE_ALIGNED(vdev_addr)) {
		return RMI_ERROR_INPUT;
	}

	if (!find_lock_two_granules(rd_addr, GRANULE_STATE_RD, &g_rd,
				    pdev_addr, GRANULE_STATE_PDEV, &g_pdev)) {
		return RMI_ERROR_INPUT;
	}

	rd = buffer_granule_map(g_rd, SLOT_RD);
	assert(rd != NULL);

	pd = buffer_granule_map(g_pdev, SLOT_PDEV);
	assert(pd != NULL);

	/* Lock vdev granule and map it */
	g_vdev = find_lock_granule(vdev_addr, GRANULE_STATE_VDEV);
	if (g_vdev == NULL) {
		smc_rc = RMI_ERROR_INPUT;
		goto out_err_input;
	}
	vd = buffer_granule_map(g_vdev, SLOT_VDEV);
	assert(vd != NULL);

	if ((vd->g_rd != g_rd) ||
	    (vd->g_pdev != g_pdev)) {
		smc_rc = RMI_ERROR_INPUT;
		goto out_err_input;
	}

	if ((vd->rmi_state != RMI_VDEV_STATE_NEW) &&
	    (vd->rmi_state != RMI_VDEV_STATE_UNLOCKED) &&
	    (vd->rmi_state != RMI_VDEV_STATE_ERROR)) {
		smc_rc = RMI_ERROR_DEVICE;
		goto out_err_input;
	}

	if (vd->dma_state == RMI_VDEV_DMA_ENABLED) {
		if (smmuv3_disable_ste(SMMU_IDX, (unsigned int)vd->tdi_id) != 0) {
			smc_rc = RMI_ERROR_DEVICE;
			goto out_err_input;
		}
	}

	if (smmuv3_release_ste(SMMU_IDX, (unsigned int)vd->tdi_id) != 0) {
		smc_rc = RMI_ERROR_DEVICE;
		goto out_err_input;
	}

	/* Update Realm */
	rd_vdev_refcount_dec(rd);

	/* Update PDEV. */
	pd->num_vdevs -= 1U;

	buffer_unmap(vd);

	/* Move the VDEV granule from VDEV to delegated state */
	granule_unlock_transition_to_delegated(g_vdev);
	vd = NULL;
	g_vdev = NULL;
	smc_rc = RMI_SUCCESS;

	/* No aux granules allocated */

out_err_input:
	if (vd != NULL) {
		buffer_unmap(vd);
	}
	if (g_vdev != NULL) {
		granule_unlock(g_vdev);
	}

	if (pd != NULL) {
		buffer_unmap(pd);
	}
	if (g_pdev != NULL) {
		granule_unlock(g_pdev);
	}

	if (rd != NULL) {
		buffer_unmap(rd);
	}
	granule_unlock(g_rd);

	return smc_rc;
}

static unsigned long validate_vdev_get_measurements_params(
	unsigned long params_addr,
	struct rmi_vdev_measure_params *measurement_params,
	bool *all)
{
	struct granule *g_vdev_measurements_params;

	/* Map and copy VDEV parameters */
	g_vdev_measurements_params = find_granule(params_addr);
	if ((g_vdev_measurements_params == NULL) ||
	    (granule_unlocked_state(g_vdev_measurements_params) != GRANULE_STATE_NS)) {
		return RMI_ERROR_INPUT;
	}

	if (!ns_buffer_read(SLOT_NS, g_vdev_measurements_params, 0U,
			    sizeof(struct rmi_vdev_measure_params), measurement_params)) {
		return RMI_ERROR_INPUT;
	}

	/* indices bit[255] must be 0. */
	if ((measurement_params->indices[VDEV_MEAS_PARAM_INDICES_LEN - 1U] & 0x80U) != 0U) {
		return RMI_ERROR_INPUT;
	}
	/* In case bit[254] is 1, bit[253:0] must all be 0 */
	if ((measurement_params->indices[VDEV_MEAS_PARAM_INDICES_LEN - 1U] & 0x40U) != 0U) {
		if ((measurement_params->indices[VDEV_MEAS_PARAM_INDICES_LEN - 1U] & 0x3FU) != 0U) {
			return RMI_ERROR_INPUT;
		}
		for (unsigned int i = 0; i < (VDEV_MEAS_PARAM_INDICES_LEN - 2U); ++i) {
			if (measurement_params->indices[i] != 0U) {
				return RMI_ERROR_INPUT;
			}
		}
		*all = true;
	} else {
		*all = false;
	}

	/*
	 * In case bit[255:254] of indices is 0, then any pattern in bit[253:0]
	 * is valid .
	 */
	return RMI_SUCCESS;
}

unsigned long smc_vdev_get_measurements(unsigned long rd_addr, unsigned long pdev_addr,
					unsigned long vdev_addr, unsigned long params_addr)
{
	struct granule *g_rd = NULL;
	struct granule *g_pdev = NULL;
	struct granule *g_vdev = NULL;
	struct dev_meas_params *spdm_meas_params;
	struct rmi_vdev_measure_params measurement_params;
	struct pdev *pd = NULL;
	struct vdev *vd = NULL;
	bool all;

	unsigned long smc_rc;

	if (!is_rmi_feat_da_enabled()) {
		return SMC_NOT_SUPPORTED;
	}

	if (!GRANULE_ALIGNED(rd_addr) || !GRANULE_ALIGNED(pdev_addr) ||
	    !GRANULE_ALIGNED(vdev_addr)) {
		return RMI_ERROR_INPUT;
	}

	if (!find_lock_two_granules(rd_addr, GRANULE_STATE_RD, &g_rd,
				    pdev_addr, GRANULE_STATE_PDEV, &g_pdev)) {
		return RMI_ERROR_INPUT;
	}

	g_vdev = find_lock_granule(vdev_addr, GRANULE_STATE_VDEV);
	if (g_vdev == NULL) {
		smc_rc = RMI_ERROR_INPUT;
		goto out_err_input;
	}

	vd = buffer_granule_map(g_vdev, SLOT_VDEV);
	assert(vd != NULL);

	if ((vd->g_rd != g_rd) ||
	    (vd->g_pdev != g_pdev)) {
		smc_rc = RMI_ERROR_DEVICE;
		goto out_err_input;
	}

	pd = buffer_granule_map(g_pdev, SLOT_PDEV);
	assert(pd != NULL);

	if (pd->dev_comm_state != DEV_COMM_IDLE) {
		smc_rc = RMI_ERROR_DEVICE;
		goto out_err_input;
	}

	smc_rc = validate_vdev_get_measurements_params(params_addr, &measurement_params, &all);
	if (smc_rc != RMI_SUCCESS) {
		goto out_err_input;
	}

	spdm_meas_params = &vd->op_params.meas_params;

	(void)memset(spdm_meas_params, 0, sizeof(struct dev_meas_params));

	/* TODO_ALP17: In case of signed flag, only the last call should call sig */
	/* TODO_ALP17: Both request and response must be cached by the Host */

	if (EXTRACT(RMI_VDEV_MEASURE_FLAGS_SIGNED, measurement_params.flags) != 0U) {
		spdm_meas_params->sign = true;
		(void)memcpy(spdm_meas_params->nonce, &measurement_params.nonce,
			     sizeof(spdm_meas_params->nonce));
	} else {
		spdm_meas_params->sign = false;
	}

	if (EXTRACT(RMI_VDEV_MEASURE_FLAGS_RAW, measurement_params.flags) != 0U) {
		spdm_meas_params->raw = true;
	} else {
		spdm_meas_params->raw = false;
	}

	spdm_meas_params->all = all;
	if (!all) {
		(void)memcpy(spdm_meas_params->indices, &measurement_params.indices,
			     sizeof(spdm_meas_params->indices));
	}

	vd->op = VDEV_OP_GET_MEAS;
	vd->comm_state = DEV_COMM_PENDING;

out_err_input:
	if (vd != NULL) {
		buffer_unmap(vd);
	}
	if (g_vdev != NULL) {
		granule_unlock(g_vdev);
	}

	if (pd != NULL) {
		buffer_unmap(pd);
	}
	if (g_pdev != NULL) {
		granule_unlock(g_pdev);
	}

	granule_unlock(g_rd);

	return smc_rc;
}

unsigned long smc_vdev_get_interface_report(unsigned long rd_addr, unsigned long pdev_addr,
					    unsigned long vdev_addr)
{
	struct granule *g_rd = NULL;
	struct granule *g_pdev = NULL;
	struct granule *g_vdev = NULL;
	struct dev_tdisp_params *tdisp_params;
	struct vdev *vd = NULL;

	unsigned long smc_rc;

	if (!is_rmi_feat_da_enabled()) {
		return SMC_NOT_SUPPORTED;
	}

	if (!GRANULE_ALIGNED(rd_addr) || !GRANULE_ALIGNED(pdev_addr) ||
	    !GRANULE_ALIGNED(vdev_addr)) {
		return RMI_ERROR_INPUT;
	}

	if (!find_lock_two_granules(rd_addr, GRANULE_STATE_RD, &g_rd,
				    pdev_addr, GRANULE_STATE_PDEV, &g_pdev)) {
		return RMI_ERROR_INPUT;
	}

	g_vdev = find_lock_granule(vdev_addr, GRANULE_STATE_VDEV);
	if (g_vdev == NULL) {
		smc_rc = RMI_ERROR_INPUT;
		goto out_err_input;
	}

	vd = buffer_granule_map(g_vdev, SLOT_VDEV);
	assert(vd != NULL);

	if ((vd->g_rd != g_rd) ||
	    (vd->g_pdev != g_pdev)) {
		smc_rc = RMI_ERROR_DEVICE;
		goto out_err_input;
	}

	if ((vd->rmi_state != RMI_VDEV_STATE_LOCKED) &&
	    (vd->rmi_state != RMI_VDEV_STATE_STARTED)) {
		smc_rc = RMI_ERROR_DEVICE;
		goto out_err_input;
	}

	if (vd->comm_state != DEV_COMM_IDLE) {
		smc_rc = RMI_ERROR_DEVICE;
		goto out_err_input;
	}

	/* Set TDISP parameters */
	tdisp_params = &vd->op_params.tdisp_params;
	(void)memset(tdisp_params, 0, sizeof(struct dev_tdisp_params));
	tdisp_params->tdi_id = (uint32_t)(vd->tdi_id & 0xffffUL);

	vd->op = VDEV_OP_GET_REPORT;
	vd->comm_state = DEV_COMM_PENDING;

	smc_rc = RMI_SUCCESS;

out_err_input:
	if (vd != NULL) {
		buffer_unmap(vd);
	}
	if (g_vdev != NULL) {
		granule_unlock(g_vdev);
	}

	if (g_pdev != NULL) {
		granule_unlock(g_pdev);
	}

	granule_unlock(g_rd);

	return smc_rc;
}

unsigned long smc_vdev_unlock(unsigned long rd_addr, unsigned long pdev_addr,
				unsigned long vdev_addr)
{
	struct granule *g_rd = NULL;
	struct granule *g_pdev = NULL;
	struct granule *g_vdev = NULL;
	struct dev_tdisp_params *tdisp_params;
	struct vdev *vd = NULL;

	unsigned long smc_rc;

	if (!is_rmi_feat_da_enabled()) {
		return SMC_NOT_SUPPORTED;
	}

	if (!GRANULE_ALIGNED(rd_addr) || !GRANULE_ALIGNED(pdev_addr) ||
	    !GRANULE_ALIGNED(vdev_addr)) {
		return RMI_ERROR_INPUT;
	}

	if (!find_lock_two_granules(rd_addr, GRANULE_STATE_RD, &g_rd,
				    pdev_addr, GRANULE_STATE_PDEV, &g_pdev)) {
		return RMI_ERROR_INPUT;
	}

	g_vdev = find_lock_granule(vdev_addr, GRANULE_STATE_VDEV);
	if (g_vdev == NULL) {
		smc_rc = RMI_ERROR_INPUT;
		goto out_err_input;
	}

	vd = buffer_granule_map(g_vdev, SLOT_VDEV);
	assert(vd != NULL);

	if ((vd->g_rd != g_rd) ||
	    (vd->g_pdev != g_pdev)) {
		smc_rc = RMI_ERROR_DEVICE;
		goto out_err_input;
	}

	if ((vd->rmi_state != RMI_VDEV_STATE_LOCKED) &&
	    (vd->rmi_state != RMI_VDEV_STATE_STARTED) &&
	    (vd->rmi_state != RMI_VDEV_STATE_ERROR)) {
		smc_rc = RMI_ERROR_DEVICE;
		goto out_err_input;
	}

	if (vd->comm_state != DEV_COMM_IDLE) {
		ERROR("vd(%p)->comm_state(%u) != DEV_COMM_IDLE\n", (void *)vd, vd->comm_state);
		smc_rc = RMI_ERROR_DEVICE;
		goto out_err_input;
	}

	if (vd->num_map != 0U) {
		smc_rc = RMI_ERROR_DEVICE;
		goto out_err_input;
	}

	/* Set TDISP parameters */
	tdisp_params = &vd->op_params.tdisp_params;
	(void)memset(tdisp_params, 0, sizeof(struct dev_tdisp_params));
	tdisp_params->tdi_id = (uint32_t)(vd->tdi_id & 0xffffUL);

	vd->op = VDEV_OP_UNLOCK;
	vd->comm_state = DEV_COMM_PENDING;

	smc_rc = RMI_SUCCESS;

out_err_input:
	if (vd != NULL) {
		buffer_unmap(vd);
	}
	if (g_vdev != NULL) {
		granule_unlock(g_vdev);
	}

	if (g_pdev != NULL) {
		granule_unlock(g_pdev);
	}

	granule_unlock(g_rd);

	return smc_rc;
}
