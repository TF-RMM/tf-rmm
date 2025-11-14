/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <buffer.h>
#include <realm.h>
#include <rec.h>
#include <rsi-handler.h>
#include <smmuv3.h>

/*
 * TODO: Currently the pci_tdisp_get_version() call made during RMI_VDEV_LOCK in
 * the DA app mandates that the version in 0x10. It would be better if that
 * function returned the version and it could be saved in the vdev.
 */
#define PCI_TDISP_MESSAGE_VERSION_10 0x10

static void initiate_vdev_id_mapping(struct rec *rec,
				     unsigned long vdev_id,
				     struct rmi_rec_exit *rec_exit,
				     enum rsi_action *rsi_action)
{
	rec_set_pending_op(rec, REC_PENDING_VDEV_REQUEST);
	rec->vdev.vdev_id = vdev_id;
	rec_exit->exit_reason = RMI_EXIT_VDEV_REQUEST;
	rec_exit->vdev_id_1 = vdev_id;
	*rsi_action = EXIT_TO_HOST;
}

void handle_rsi_vdev_dma_enable(struct rec *rec,
				struct rmi_rec_exit *rec_exit,
				struct rsi_result *res)
{
	struct rec_plane *plane;
	struct rd *rd;
	enum rsi_action rsi_action;
	unsigned long rsi_rc;
	unsigned long vdev_id;
	unsigned long non_ats_plane;

	/* TODO_ALP17: check ats in flags */

	/* RSI calls can only be issued by Plane 0 */
	plane = rec_plane_0(rec);
	assert(rec_is_plane_0_active(rec));

	if ((!rec->da_enabled)) {
		rsi_action = UPDATE_REC_RETURN_TO_REALM;
		rsi_rc = RSI_ERROR_STATE;
		goto set_rsi_action;
	}

	/* TODO_ALP17: check that vdev_id is not free */

	vdev_id = plane->regs[1];
	non_ats_plane = plane->regs[3];

	granule_lock(rec->realm_info.g_rd, GRANULE_STATE_RD);
	rd = buffer_granule_map(rec->realm_info.g_rd, SLOT_RD);
	assert(rd != NULL);

	if ((rd->num_aux_planes > 0U) &&
	    ((non_ats_plane == 0U) || (non_ats_plane > rd->num_aux_planes))) {
		/* TODO_ALP17: Check the above condition in latest spec */
		rsi_action = UPDATE_REC_RETURN_TO_REALM;
		rsi_rc = RSI_ERROR_INPUT;
		goto rd_unmap;
	}

	initiate_vdev_id_mapping(rec, vdev_id, rec_exit, &rsi_action);

	assert(((unsigned int)rsi_action & FLAG_EXIT_TO_HOST) != 0U);
	rsi_rc = RSI_SUCCESS;

rd_unmap:
	buffer_unmap(rd);
	granule_unlock(rec->realm_info.g_rd);

set_rsi_action:
	if (rsi_action == UPDATE_REC_RETURN_TO_REALM) {
		res->smc_res.x[0] = rsi_rc;
	}
	res->action = rsi_action;
}

bool finish_rsi_vdev_dma_enable(struct rec *rec,
				bool *request_finished)
{
	struct rec_plane *plane;
	struct granule *g_vdev;
	struct vdev *vd;
	unsigned long rc;
	unsigned long lock_nonce;
	unsigned long meas_nonce;
	unsigned long report_nonce;
	unsigned long vdev_addr;

	/* RSI calls can only be issued by Plane 0 */
	plane = rec_plane_0(rec);
	assert(rec_is_plane_0_active(rec));

	lock_nonce = plane->regs[4];
	meas_nonce = plane->regs[5];
	report_nonce = plane->regs[6];

	/* At this point the mapping from virtual device ID to VDEV object had
	 * been successful, and the address of the VDEV is stored in the REC by
	 * RMM
	 */
	vdev_addr = rec->vdev.vdev_addr;

	/* Lock the vdev granule and map it */
	g_vdev = find_lock_granule(vdev_addr, GRANULE_STATE_VDEV);
	if (g_vdev == NULL) {
		plane->regs[0] = RSI_ERROR_INPUT;
		goto out;
	}

	vd = buffer_granule_map(g_vdev, SLOT_VDEV);
	assert(vd != NULL);

	if ((lock_nonce != vd->attest_info.lock_nonce) ||
	    (meas_nonce != vd->attest_info.meas_nonce) ||
	    (report_nonce != vd->attest_info.report_nonce)) {
		plane->regs[0] = RSI_ERROR_DEVICE;
		goto unmap_vd;
	}

	rc = RSI_SUCCESS;
	if (vd->dma_state != RMI_VDEV_DMA_ENABLED) {
		/* Only call the driver if not already enabled */
		/* TODO_ALP17: set non_ats_plane in vdev */

		if (smmuv3_enable_ste(SMMU_IDX, (unsigned int)vd->tdi_id) != 0) {
			rc = RSI_ERROR_DEVICE;
		} else {
			vd->dma_state = RMI_VDEV_DMA_ENABLED;
		}
	}
	plane->regs[0] = rc;

unmap_vd:
	buffer_unmap(vd);
	granule_unlock(g_vdev);

out:
	*request_finished = true;
	return true;
}

void handle_rsi_vdev_dma_disable(struct rec *rec,
				 struct rmi_rec_exit *rec_exit,
				 struct rsi_result *res)
{
	struct rec_plane *plane;
	enum rsi_action rsi_action;
	unsigned long rsi_rc;
	unsigned long vdev_id;

	/* RSI calls can only be issued by Plane 0 */
	plane = rec_plane_0(rec);
	assert(rec_is_plane_0_active(rec));

	if ((!rec->da_enabled)) {
		rsi_action = UPDATE_REC_RETURN_TO_REALM;
		rsi_rc = RSI_ERROR_STATE;
		goto set_rsi_action;
	}

	/* TODO_ALP17: check that vdev_id is not free */

	vdev_id = plane->regs[1];

	initiate_vdev_id_mapping(rec, vdev_id, rec_exit, &rsi_action);

	assert(((unsigned int)rsi_action & FLAG_EXIT_TO_HOST) != 0U);
	rsi_rc = RSI_SUCCESS;

set_rsi_action:
	if (rsi_action == UPDATE_REC_RETURN_TO_REALM) {
		res->smc_res.x[0] = rsi_rc;
	}
	res->action = rsi_action;
}

bool finish_rsi_vdev_dma_disable(struct rec *rec,
				 bool *request_finished)
{
	struct rec_plane *plane;
	struct granule *g_vdev;
	struct vdev *vd;
	unsigned long vdev_addr;
	unsigned long rc;

	/* RSI calls can only be issued by Plane 0 */
	plane = rec_plane_0(rec);
	assert(rec_is_plane_0_active(rec));

	/* At this point the mapping from virtual device ID to VDEV object had
	 * been successful, and the address of the VDEV is stored in the REC by
	 * RMM
	 */
	vdev_addr = rec->vdev.vdev_addr;

	/* Lock the vdev granule and map it */
	g_vdev = find_lock_granule(vdev_addr, GRANULE_STATE_VDEV);
	if (g_vdev == NULL) {
		plane->regs[0] = RSI_ERROR_INPUT;
		goto out;
	}

	vd = buffer_granule_map(g_vdev, SLOT_VDEV);
	assert(vd != NULL);

	rc = RSI_SUCCESS;
	if (vd->dma_state != RMI_VDEV_DMA_DISABLED) {
		/* Only call the driver if not already disabled */
		if (smmuv3_disable_ste(SMMU_IDX, (unsigned int)vd->tdi_id) != 0) {
			rc = RSI_ERROR_DEVICE;
		} else {
			vd->dma_state = RMI_VDEV_DMA_DISABLED;
		}
	}

	plane->regs[0] = rc;

	buffer_unmap(vd);
	granule_unlock(g_vdev);

out:
	*request_finished = true;
	return true;
}

void handle_rsi_vdev_get_info(struct rec *rec,
			      struct rmi_rec_exit *rec_exit,
			      struct rsi_result *res)
{
	unsigned long rsi_rc;
	enum rsi_action rsi_action;
	unsigned long info_addr;
	unsigned long vdev_id;
	struct rec_plane *plane;

	/* RSI calls can only be issued by Plane 0 */
	plane = rec_plane_0(rec);
	assert(rec_is_plane_0_active(rec));

	if ((!rec->da_enabled)) {
		rsi_action = UPDATE_REC_RETURN_TO_REALM;
		rsi_rc = RSI_ERROR_STATE;
		goto set_rsi_action;
	}

	vdev_id = plane->regs[1];
	info_addr = plane->regs[2];

	if (!ALIGNED(info_addr, 512U)) {
		rsi_action = UPDATE_REC_RETURN_TO_REALM;
		rsi_rc = RSI_ERROR_INPUT;
		goto set_rsi_action;
	}

	if (!addr_in_rec_par(rec, info_addr)) {
		res->smc_res.x[0] = RSI_ERROR_INPUT;
		return;
	}

	initiate_vdev_id_mapping(rec, vdev_id, rec_exit, &rsi_action);

	assert(((unsigned int)rsi_action & FLAG_EXIT_TO_HOST) != 0U);
	rsi_rc = RSI_SUCCESS;

set_rsi_action:
	if (rsi_action == UPDATE_REC_RETURN_TO_REALM) {
		res->smc_res.x[0] = rsi_rc;
	}
	res->action = rsi_action;
}

/*
 * Copy device info and attestation digest of certificate, public key, device
 * measurements to buffer 'vdev_info'
 */
static void vdev_get_info(struct pdev *pd, struct vdev *vd, struct rsi_vdev_info *vdev_info)
{
	/* Set P2P feature flag */
	if (EXTRACT(RMI_PDEV_FLAGS_P2P, pd->rmi_flags) == RMI_FEATURE_TRUE) {
		vdev_info->flags = INPLACE(RSI_VDEV_FLAGS_P2P_ENABLED, RSI_FEATURE_TRUE);
	} else {
		vdev_info->flags = INPLACE(RSI_VDEV_FLAGS_P2P_ENABLED, RSI_FEATURE_FALSE);
	}

	/*
	 * vdev.p2p_bound is always false by specification, so
	 * RSI_VDEV_FLAGS_P2P_BOUND flag is never set
	 */

	/*
	 * Set certificate slot id and RMI hash algorithm. RMI and RSI hash
	 * algorithm enumeration uses the same value.
	 */
	vdev_info->cert_id = pd->dev.cert_slot_id;
	vdev_info->hash_algo = pd->rmi_hash_algo;

	vdev_info->lock_nonce = vd->attest_info.lock_nonce;
	vdev_info->meas_nonce = vd->attest_info.meas_nonce;
	vdev_info->report_nonce = vd->attest_info.report_nonce;

	vdev_info->tdisp_version = PCI_TDISP_MESSAGE_VERSION_10;
	vdev_info->state = (unsigned char)vd->rmi_state;

	/* TODO_ALP17: Set proper vca_digest */
	memset(vdev_info->vca_digest, 0, RSI_VDEV_VCA_DIGEST_LEN);
	(void)memcpy(vdev_info->cert_digest, pd->cert_digest.value,
		     pd->cert_digest.len);
	/* TODO_ALP17: Set proper public_key */
	(void)memset(vdev_info->pubkey_digest, 0, RSI_VDEV_PUBKEY_DIGEST_LEN);
	(void)memcpy(vdev_info->meas_digest, vd->meas_digest.value,
		     vd->meas_digest.len);
	(void)memcpy(vdev_info->report_digest, vd->ifc_report_digest.value,
		     vd->ifc_report_digest.len);
}

/*
 * Return 'true' if execution should continue in the REC, otherwise return
 * 'false' to go back to the NS caller.
 */
bool finish_rsi_vdev_get_info(struct rec *rec,
			      struct rmi_rec_exit *rec_exit,
			      bool *request_finished)
{
	unsigned long vdev_addr;
	unsigned long info_granule_address;
	void *info_granule_va;
	unsigned long info_addr;
	struct rsi_vdev_info *vdev_info;
	struct rec_plane *plane;
	struct granule *llt;
	struct granule *g_pdev;
	struct granule *g_vdev;
	struct pdev *pd;
	struct vdev *vd;
	struct rsi_result res = {.action = UPDATE_REC_RETURN_TO_REALM};

	/* RSI calls can only be issued by Plane 0 */
	plane = rec_plane_0(rec);
	assert(rec_is_plane_0_active(rec));

	/* At this point the mapping from virtual device ID to VDEV object had
	 * been successful, and the address of the VDEV is stored in the REC by
	 * RMM
	 */
	vdev_addr = rec->vdev.vdev_addr;

	info_addr = plane->regs[2];
	info_granule_address = info_addr & GRANULE_MASK;

	/* Validated in RSI handler */
	assert(ALIGNED(info_addr, 512U));
	assert(addr_in_rec_par(rec, info_addr));

	if (!realm_mem_lock_map(rec, info_granule_address, &info_granule_va, &llt, &res)) {
		/* Failed to map the address. Check res to decide what to do */
		if (((unsigned int)res.action & FLAG_STAGE_2_ABORT) != 0U) {
			/*
			 * The RSI call cannot progress because the IPA that
			 * was provided by the Realm has invalid mapping.
			 * Emulate the data abort against that IPA so that the
			 * host can bring the page in.
			 */
			/* coverity[uninit_use_in_call:SUPPRESS] */
			emulate_stage2_data_abort(rec_exit, res.rtt_level, info_granule_address);

			*request_finished = false;
			return false;
		}
		assert(((unsigned int)res.action & FLAG_UPDATE_REC) != 0U);
		/* coverity[uninit_use:SUPPRESS] */
		plane->regs[0] = res.smc_res.x[0];
		goto unmap_llt;
	}

	/* coverity[uninit_use:SUPPRESS] */
	assert((info_granule_va != NULL) && (llt != NULL));

	vdev_info = (struct rsi_vdev_info *)
		((uintptr_t)info_granule_va + (info_addr - info_granule_address));

	/* Lock the vdev granule and map it, to get the pdev granule address. */
	g_vdev = find_lock_granule(vdev_addr, GRANULE_STATE_VDEV);
	if (g_vdev == NULL) {
		plane->regs[0] = RMI_ERROR_INPUT;
		goto unmap_llt;
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

	vdev_get_info(pd, vd, vdev_info);

	/* Update return value */
	plane->regs[0] = RSI_SUCCESS;

	buffer_unmap(vd);
	granule_unlock(g_vdev);
	buffer_unmap(pd);
	granule_unlock(g_pdev);

unmap_llt:
	assert(((unsigned int)res.action & FLAG_EXIT_TO_HOST) == 0U);

	/* coverity[uninit_use_in_call:SUPPRESS] */
	buffer_unmap(info_granule_va);

	/* Unlock last level RTT */
	/* coverity[uninit_use_in_call:SUPPRESS] */
	granule_unlock(llt);

	*request_finished = true;
	return true;
}

void handle_rsi_vdev_validate_mapping(struct rec *rec,
				      struct rmi_rec_exit *rec_exit,
				      struct rsi_result *res)
{
	unsigned long rsi_rc;
	enum rsi_action rsi_action;
	struct rec_plane *plane;
	unsigned long vdev_id;
	unsigned long ipa_base;
	unsigned long ipa_top;
	unsigned long pa_base;

	/* RSI calls can only be issued by Plane 0 */
	plane = rec_plane_0(rec);
	assert(rec_is_plane_0_active(rec));

	if ((!rec->da_enabled)) {
		rsi_action = UPDATE_REC_RETURN_TO_REALM;
		rsi_rc = RSI_ERROR_STATE;
		goto set_rsi_action;
	}

	vdev_id = plane->regs[1];
	ipa_base = plane->regs[2];
	ipa_top = plane->regs[3];
	pa_base = plane->regs[4];

	/* TODO_ALP17: Check vdev_id is not free */

	if (!GRANULE_ALIGNED(ipa_base) ||
	    !GRANULE_ALIGNED(ipa_top) ||
	    !GRANULE_ALIGNED(pa_base) ||
	    (ipa_top <= ipa_base) ||
	    !region_in_rec_par(rec, ipa_base, ipa_top)) {
		rsi_action = UPDATE_REC_RETURN_TO_REALM;
		rsi_rc = RSI_ERROR_INPUT;
		goto set_rsi_action;
	}

	initiate_vdev_id_mapping(rec, vdev_id, rec_exit, &rsi_action);

	assert(((unsigned int)rsi_action & FLAG_EXIT_TO_HOST) != 0U);
	rsi_rc = RSI_SUCCESS;

set_rsi_action:
	if (rsi_action == UPDATE_REC_RETURN_TO_REALM) {
		res->smc_res.x[0] = rsi_rc;
	}
	res->action = rsi_action;
}

/*
 * Return 'true' if execution should continue in the REC, otherwise return
 * 'false' to go back to the NS caller.
 */
bool finish_rsi_vdev_validate_mapping(struct rec *rec,
				      struct rmi_rec_exit *rec_exit,
				      bool *request_finished)
{
	unsigned long vdev_addr;
	struct rec_plane *plane;
	struct granule *g_vdev;
	struct vdev *vd = NULL;
	unsigned long ipa_base;
	unsigned long ipa_top;
	unsigned long pa_base;
	unsigned long flags;
	unsigned long vdev_id;
	unsigned long lock_nonce;
	unsigned long meas_nonce;
	unsigned long report_nonce;
	bool retval;

	/* RSI calls can only be issued by Plane 0 */
	plane = rec_plane_0(rec);

	/*
	 * X1: Realm device identifier
	 * X2: Base of target IPA region
	 * X3: Top of target IPA region
	 * X4: Base of target PA region
	 * X5: Flags of type RsiDevMemFlagsFlags
	 * X6: Nonce generated on most recent
	 * X7: GET_MEASUREMENT request sequence number
	 * X8: GET_INTERFACE_REPORT request sequence number
	 */
	vdev_id = plane->regs[1];
	ipa_base = plane->regs[2];
	ipa_top = plane->regs[3];
	pa_base = plane->regs[4];
	flags = plane->regs[5];
	lock_nonce = plane->regs[6];
	meas_nonce = plane->regs[7];
	report_nonce = plane->regs[8];

	/* At this point the mapping from virtual device ID to VDEV object had
	 * been successful, and the address of the VDEV is stored in the REC by
	 * RMM
	 */
	vdev_addr = rec->vdev.vdev_addr;

	/* Lock the vdev granule and map it */
	g_vdev = find_lock_granule(vdev_addr, GRANULE_STATE_VDEV);
	if (g_vdev == NULL) {
		plane->regs[0] = RSI_ERROR_INPUT;
		retval = true;
		goto out;
	}

	vd = buffer_granule_map(g_vdev, SLOT_VDEV);
	assert(vd != NULL);

	if ((vd->rmi_state != RMI_VDEV_STATE_LOCKED) &&
	    (vd->rmi_state != RMI_VDEV_STATE_STARTED)) {
		plane->regs[0] = RSI_ERROR_INPUT;
		retval = true;
		goto out;
	}

	if ((lock_nonce != vd->attest_info.lock_nonce) ||
	    (meas_nonce != vd->attest_info.meas_nonce) ||
	    (report_nonce != vd->attest_info.report_nonce)) {
		plane->regs[0] = RSI_ERROR_DEVICE;
		retval = true;
		goto out;
	}

	/* Update REC dev_mem */
	rec->dev_mem.base = ipa_base;
	rec->dev_mem.top = ipa_top;
	rec->dev_mem.addr = ipa_base;
	rec->dev_mem.pa = pa_base;
	rec->dev_mem.flags = flags;

	/* Update REC exit dev_mem */
	rec_exit->exit_reason = RMI_EXIT_DEV_MEM_MAP;
	rec_exit->dev_mem_base = ipa_base;
	rec_exit->dev_mem_top = ipa_top;
	rec_exit->dev_mem_pa = pa_base;
	rec_exit->vdev_id_1 = vdev_id;

	/* Update return value */
	plane->regs[0] = RSI_SUCCESS;

	/* Exit to host to process DEV mem mapping */
	retval = false;
out:
	if (vd != NULL) {
		buffer_unmap(vd);
	}
	granule_unlock(g_vdev);

	*request_finished = true;
	return retval;
}
