/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <buffer.h>
#include <debug.h>
#include <dev.h>
#include <dev_assign_app.h>
#include <granule.h>
#include <limits.h>
#include <realm.h>
#include <rsi-handler.h>
#include <rsi_rdev_call.h>
#include <smc-rsi.h>
#include <utils_def.h>

/*
 * Map Realm IPA
 */
static unsigned long realm_mem_map(struct rec *rec, unsigned long ipa,
				   struct s2_walk_result *walk_res)
{
	enum s2_walk_status walk_status;
	struct granule *g_ipa;
	unsigned long ipa_aligned;
	unsigned int offset;
	void *va;

	if (!GRANULE_ALIGNED(ipa)) {
		ipa_aligned = round_down(ipa, GRANULE_SIZE);
		offset = (unsigned int)(ipa & ~GRANULE_MASK);
	} else {
		ipa_aligned = ipa;
		offset = 0U;
	}

	if (!addr_in_rec_par(rec, ipa_aligned)) {
		return 0UL;
	}

	walk_status = realm_ipa_to_pa(rec, ipa_aligned, walk_res);
	if (walk_status == WALK_FAIL) {
		if (walk_res->ripas_val == RIPAS_EMPTY) {
			return 0UL;
		} else {
			/* coverity[misra_c_2012_rule_12_1_violation:SUPPRESS] */
			/* coverity[misra_c_2012_rule_10_4_violation:SUPPRESS] */
			return ULONG_MAX;
		}
	} else if (walk_status == WALK_INVALID_PARAMS) {
		return 0UL;
	}

	/* Map Realm buffer */
	g_ipa = find_granule(walk_res->pa);
	assert(g_ipa != NULL);

	va = buffer_granule_mecid_map(g_ipa, SLOT_REALM,
		rec->realm_info.primary_s2_ctx.mecid);
	assert(va != NULL);

	return (unsigned long)(&((uint8_t *)va)[offset]);
}

static void realm_mem_unmap_unlock(unsigned long va, struct s2_walk_result *walk_res)
{
	buffer_unmap((void *)round_down(va, GRANULE_SIZE));
	granule_unlock(walk_res->llt);
}

/*
 * Check VDEV state and transistion to COMMUNICATING and check PDEV comm state
 * and set to PENDING.
 *
 * Spec A9.4.3.2 State transitions:
 * VDEV_READY to VDEV_COMMUNICATING
 *     REC exit due to VDEV communication
 *
 */
static unsigned long set_dev_state(struct vdev *vd)
{
	struct pdev *pd;

	pd = buffer_granule_map(vd->g_pdev, SLOT_PDEV);
	assert(pd != NULL);

	if ((vd->rmi_state != RMI_VDEV_STATE_READY) ||
	    (pd->dev_comm_state != DEV_COMM_IDLE)) {
		buffer_unmap(pd);
		return RSI_ERROR_DEVICE;
	}

	pd->dev_comm_state = DEV_COMM_PENDING;
	buffer_unmap(pd);

	return RSI_SUCCESS;
}

/*
 * Copy device info and attestation digest of certificate, public key, device
 * measurements to buffer 'rdev_info'
 *
 * todo: move this function to vdev.c
 */
static int vdev_get_info(struct granule *g_vdev, struct rsi_dev_info *rdev_info)
{
	struct pdev *pd;
	struct vdev *vd;
	struct granule *g_pdev;
	int rc;

	if (g_vdev == NULL) {
		return -1;
	}

	/*
	 * Lock and map the VDEV granule and extract the PDEV granule address.
	 * Due to the strict locking order we cannot lock the PDEV granule
	 * immediately after this, first the vdev granule must be unlocked.
	 */
	granule_lock(g_vdev, GRANULE_STATE_VDEV);
	vd = buffer_granule_map(g_vdev, SLOT_VDEV);
	assert(vd != NULL);

	g_pdev = vd->g_pdev;

	buffer_unmap(vd);
	granule_unlock(g_vdev);

	granule_lock(g_pdev, GRANULE_STATE_PDEV);
	granule_lock(g_vdev, GRANULE_STATE_VDEV);

	pd = buffer_granule_map(g_pdev, SLOT_PDEV);
	assert(pd != NULL);
	vd = buffer_granule_map(g_vdev, SLOT_VDEV);
	assert(vd != NULL);

	/* Set P2P feature flag */
	if (EXTRACT(RMI_PDEV_FLAGS_P2P, pd->rmi_flags) == RMI_FEATURE_TRUE) {
		rdev_info->flags = INPLACE(RSI_DEV_FLAGS_P2P, RSI_FEATURE_TRUE);
	} else {
		rdev_info->flags = INPLACE(RSI_DEV_FLAGS_P2P, RSI_FEATURE_FALSE);
	}

	/* If IDE is enabled then its independently attested device */
	if (EXTRACT(RMI_PDEV_FLAGS_IDE, pd->rmi_flags) == RMI_PDEV_IDE_TRUE) {
		rdev_info->attest_type =
			RSI_DEV_ATTEST_TYPE_INDEPENDENTLY_ATTESTED;
	} else {
		rdev_info->attest_type = RSI_DEV_ATTEST_TYPE_PLATFORM_ATTESTED;
	}

	/*
	 * Set certificate slot id and RMI hash algorithm. RMI and RSI hash
	 * algorithm enumeration uses the same value.
	 */
	rdev_info->cert_id = pd->dev.cert_slot_id;
	rdev_info->hash_algo = pd->rmi_hash_algo;
	(void)memcpy(rdev_info->cert_digest, pd->cert_digest.value,
		     pd->cert_digest.len);
	(void)memcpy(rdev_info->meas_digest, vd->meas_digest.value,
		     vd->meas_digest.len);
	(void)memcpy(rdev_info->report_digest, vd->ifc_report_digest.value,
		     vd->ifc_report_digest.len);

	rc = 0;
	buffer_unmap(pd);
	buffer_unmap(vd);
	granule_unlock(g_vdev);
	granule_unlock(g_pdev);

	return rc;
}

void handle_rsi_rdev_get_info(struct rec *rec, struct rsi_result *res)
{
	struct s2_walk_result walk_res;
	struct rsi_dev_info *rdev_info;
	struct rec_plane *plane;
	struct rd *rd;
	uint64_t vdev_id;
	uint64_t vdev_inst_id;
	unsigned long buf_ipa;
	unsigned long buf_va;
	unsigned long rsi_rc;
	int rc;

	assert(rec != NULL);

	/* RSI calls can only be issued by Plane 0 */
	plane = rec_plane_0(rec);

	res->action = UPDATE_REC_RETURN_TO_REALM;

	if (!rec->da_enabled) {
		rsi_rc = RSI_ERROR_STATE;
		goto out;
	}

	/*
	 * X1: Realm device identifier
	 * X2: Device instance identifier
	 * X3: IPA of the RSI dev info
	 */
	vdev_id = plane->regs[1];
	vdev_inst_id = plane->regs[2];
	buf_ipa = plane->regs[3];

	/* rd granule mapped but not locked */
	rd = buffer_granule_map(rec->realm_info.g_rd, SLOT_RD);
	assert(rd != NULL);

	/* Check if IPA is sizeof rsi_dev_info (512) bytes aligned */
	if (!ALIGNED(buf_ipa, sizeof(struct rsi_dev_info))) {
		rsi_rc = RSI_ERROR_INPUT;
		goto out_rd_unmap;
	}

	/*
	 * TODO: RMM assumes only the VDEV last retrieved via GET_INSTANCE will
	 * be queried by REC.
	 */
	if ((!rec->vdev.inst_id_valid) ||
	    (vdev_id != rec->vdev.id) ||
	    (vdev_inst_id != rec->vdev.inst_id)) {
		rsi_rc = RSI_ERROR_STATE;
		goto out_rd_unmap;
	}

	if (rd->g_vdev == NULL) {
		rsi_rc = RSI_ERROR_STATE;
		goto out_rd_unmap;
	}

	buf_va = realm_mem_map(rec, buf_ipa, &walk_res);
	if (buf_va == 0UL) {
		rsi_rc = RSI_ERROR_INPUT;
		goto out_rd_unmap;
	/* cppcheck-suppress misra-c2012-10.4 */
	/* coverity[misra_c_2012_rule_12_1_violation:SUPPRESS] */
	/* coverity[misra_c_2012_rule_10_4_violation:SUPPRESS] */
	} else if (buf_va == ULONG_MAX) {
		res->action = STAGE_2_TRANSLATION_FAULT;
		res->rtt_level = walk_res.rtt_level;
		rsi_rc = RSI_SUCCESS;
		goto out_rd_unmap;
	}

	rdev_info = (struct rsi_dev_info *)buf_va;
	(void)memset(rdev_info, 0, sizeof(struct rsi_dev_info));

	rc = vdev_get_info(rd->g_vdev, rdev_info);
	if (rc == 0) {
		rsi_rc = RSI_SUCCESS;
	} else {
		rsi_rc = RSI_ERROR_STATE;
	}

	realm_mem_unmap_unlock(buf_va, &walk_res);
out_rd_unmap:
	buffer_unmap(rd);
out:
	res->smc_res.x[0] = rsi_rc;
}

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

void handle_rsi_rdev_get_state(struct rec *rec, struct rsi_result *res)
{
	struct vdev *vd;
	struct rec_plane *plane;
	struct rd *rd;
	unsigned long rsi_rc;
	unsigned long vdev_id;
	unsigned long vdev_inst_id;
	enum rsi_action rsi_action;

	/* Set default action to return to Realm */
	rsi_action = UPDATE_REC_RETURN_TO_REALM;

	if (!rec->da_enabled) {
		rsi_action = UPDATE_REC_RETURN_TO_REALM;
		rsi_rc = RSI_ERROR_STATE;
		goto out;
	}

	/* RSI calls can only be issued by Plane 0 */
	plane = rec_plane_0(rec);

	/*
	 * X1: Virtual device identifier
	 * X2: Device instance identifier
	 *
	 * Only one vdev is supported
	 * todo: implement rdev_lookup(vdev_id, vdev_inst_id)
	 */
	vdev_id = plane->regs[1];
	vdev_inst_id = plane->regs[2];

	/* rd granule mapped but not locked */
	rd = buffer_granule_map(rec->realm_info.g_rd, SLOT_RD);
	assert(rd != NULL);

	/*
	 * For now, assume that g_vdev cached by smc_vdev_create() will be used
	 * here. Return error if g_vdev is not cached. Will be corrected in
	 * alp14+ implementation
	 */
	if (rd->g_vdev == NULL) {
		rsi_rc = RSI_ERROR_INPUT;
		goto out_unmap_rd;
	}

	granule_lock(rd->g_vdev, GRANULE_STATE_VDEV);
	vd = buffer_granule_map(rd->g_vdev, SLOT_VDEV);
	assert(vd != NULL);

	if ((vd->id == vdev_id) && (vd->inst_id == vdev_inst_id)) {
		res->smc_res.x[1] = vd->rdev.rsi_state;
		rsi_rc = RSI_SUCCESS;
	} else {
		rsi_rc = RSI_ERROR_INPUT;
	}

	buffer_unmap(vd);

	granule_unlock(rd->g_vdev);
out_unmap_rd:
	buffer_unmap(rd);
out:
	res->smc_res.x[0] = rsi_rc;
	res->action = rsi_action;
}

static bool validate_rsi_meas_params(struct rsi_dev_measure_params *rsi_meas_params,
				     bool flags_all)
{
	/*
	 * If measurements are not required for all indices, the `indices` array
	 * is used as a bitmap. Each bit specifies whether measurements should
	 * be returned for the corresponding index. As mandated by the RMM
	 * specification, the bits for the lowest and highest indices must be 0.
	 */
	if ((!flags_all) &&
		(((rsi_meas_params->indices[0] & 0x01U) != 0U) ||
		 ((rsi_meas_params->indices[RDEV_MEAS_PARAM_NONCE_LEN - 1U] & 0x80U) != 0U))) {
		return false;
	}
	return true;
}

void handle_rsi_rdev_get_measurements(struct rec *rec,
				      struct rmi_rec_exit *rec_exit,
				      struct rsi_result *res)
{
	unsigned long rsi_rc;
	enum rsi_action rsi_action;
	unsigned long vdev_id;
	unsigned long vdev_inst_id;
	unsigned long params_ipa;
	unsigned long params_va;
	struct dev_meas_params *spdm_meas_params;
	struct rsi_dev_measure_params *rsi_meas_params;
	struct s2_walk_result walk_res;
	struct realm_device *rdev;
	struct vdev *vd;
	struct rec_plane *plane;
	struct rd *rd;
	bool flags_all;

	/* Set default action to return to Realm */
	rsi_action = UPDATE_REC_RETURN_TO_REALM;

	/* RSI calls can only be issued by Plane 0 */
	plane = rec_plane_0(rec);

	/*
	 * X1: Virtual device identifier
	 * X2: Device instance identifier
	 * X3: IPA of the Granule to which the configuration data will be written
	 *
	 * Only one vdev is supported
	 * todo: implement rdev_lookup(vdev_id, vdev_inst_id)
	 */
	vdev_id = plane->regs[1];
	vdev_inst_id = plane->regs[2];
	params_ipa = plane->regs[3];

	if (!rec->da_enabled) {
		rsi_rc = RSI_ERROR_STATE;
		goto out;
	}

	/* rd granule mapped but not locked */
	rd = buffer_granule_map(rec->realm_info.g_rd, SLOT_RD);
	assert(rd != NULL);

	/*
	 * For now, assume that g_vdev cached by smc_vdev_create() will be used
	 * here. Return error if g_vdev is not cached. Will be corrected in
	 * alp14+ implementation
	 */
	if (rd->g_vdev == NULL) {
		rsi_rc = RSI_ERROR_INPUT;
		goto out_rd_unmap;
	}
	granule_lock(rd->g_vdev, GRANULE_STATE_VDEV);
	vd = buffer_granule_map(rd->g_vdev, SLOT_VDEV);
	assert(vd != NULL);

	if ((vd->id != vdev_id) || (vd->inst_id != vdev_inst_id)) {
		rsi_rc = RSI_ERROR_INPUT;
		goto out_vd_unmap;
	}

	rdev = &vd->rdev;

	/*
	 * Device measurements can be fetched if the TDI is in unlocked or
	 * locked or started state
	 */
	if ((rdev->rsi_state != RSI_RDEV_STATE_UNLOCKED) &&
	    (rdev->rsi_state != RSI_RDEV_STATE_LOCKED) &&
	    (rdev->rsi_state != RSI_RDEV_STATE_STARTED)) {
		rsi_rc = RSI_ERROR_DEVICE;
		goto out_vd_unmap;
	}

	params_va = realm_mem_map(rec, params_ipa, &walk_res);
	if (params_va == 0UL) {
		rsi_rc = RSI_ERROR_INPUT;
		goto out_vd_unmap;
	/* cppcheck-suppress misra-c2012-10.4 */
	/* coverity[misra_c_2012_rule_12_1_violation:SUPPRESS] */
	/* coverity[misra_c_2012_rule_10_4_violation:SUPPRESS] */
	} else if (params_va == ULONG_MAX) {
		res->action = STAGE_2_TRANSLATION_FAULT;
		res->rtt_level = walk_res.rtt_level;
		rsi_rc = RSI_SUCCESS;
		goto out_vd_unmap;
	}

	/*
	 * Set RDEV op and Copy the measurement parameters to RDEV op_params.
	 * This will used by RMI VDEV communicate call to pass it to SPDM layer.
	 */
	rsi_meas_params = (struct rsi_dev_measure_params *)params_va;

	flags_all = EXTRACT(RSI_DEV_MEASURE_FLAGS_ALL, rsi_meas_params->flags) ==
		RSI_DEV_MEASURE_ALL;

	if (!validate_rsi_meas_params(rsi_meas_params, flags_all)) {
		rsi_rc = RSI_ERROR_INPUT;
		goto out_vd_unmap;
	}

	rdev->op = RDEV_OP_GET_MEASUREMENTS;
	spdm_meas_params = &rdev->op_params.meas_params;
	(void)memset(spdm_meas_params, 0, sizeof(struct dev_meas_params));

	if (flags_all) {
		spdm_meas_params->all = true;
	} else {
		spdm_meas_params->all = false;
		(void)memcpy(spdm_meas_params->indices, rsi_meas_params->indices,
			     sizeof(spdm_meas_params->indices));
	}

	if (EXTRACT(RSI_DEV_MEASURE_FLAGS_SIGNED, rsi_meas_params->flags) ==
	    RSI_DEV_MEASURE_SIGNED) {
		spdm_meas_params->sign = true;
		(void)memcpy(spdm_meas_params->nonce, rsi_meas_params->nonce,
			     sizeof(spdm_meas_params->nonce));
	} else {
		spdm_meas_params->sign = false;
	}

	if (EXTRACT(RSI_DEV_MEASURE_FLAGS_RAW, rsi_meas_params->flags) ==
	    RSI_DEV_MEASURE_RAW) {
		spdm_meas_params->raw = true;
	} else {
		spdm_meas_params->raw = false;
	}

	realm_mem_unmap_unlock(params_va, &walk_res);

	rsi_rc = set_dev_state(vd);
	if (rsi_rc != RSI_SUCCESS) {
		goto out_vd_unmap;
	}

	/* Change the RDEV state to busy. And exit to host with VDEV request */
	if (rdev->rsi_state == RSI_RDEV_STATE_UNLOCKED) {
		rdev->rsi_state = RSI_RDEV_STATE_UNLOCKED_BUSY;
	} else if (rdev->rsi_state == RSI_RDEV_STATE_LOCKED) {
		rdev->rsi_state = RSI_RDEV_STATE_LOCKED_BUSY;
	} else {
		rdev->rsi_state = RSI_RDEV_STATE_STARTED_BUSY;
	}

	/*
	 * Exit to host to compare vdev_id and inst_id and provide the PA of
	 * VDEV
	 */
	/*
	 * TODO: The implementation of VDEV_COMPLETE sequence in RMM is not
	 * correct. The rec already have g_vdev cached above and it is a bit
	 * pointless trying to get PA from host as g_vdev can be converted to a
	 * unique PA. However this is OK for now, since currently only single
	 * vdev supported for a realm.
	 * This will be fixed when RMM will be updated to comply with spec
	 * Alp14+ implementation.
	 */
	rec->vdev.id = vdev_id;
	rec->vdev.inst_id = vdev_inst_id;
	rec->vdev.inst_id_valid = true;
	rec_set_pending_op(rec, REC_PENDING_VDEV_COMPLETE);

	rec_exit->vdev_id = vdev_id;
	rec_exit->exit_reason = RMI_EXIT_VDEV_REQUEST;
	rsi_action = UPDATE_REC_EXIT_TO_HOST;

out_vd_unmap:
	buffer_unmap(vd);
	granule_unlock(rd->g_vdev);
out_rd_unmap:
	buffer_unmap(rd);
out:
	if (rsi_action == UPDATE_REC_RETURN_TO_REALM) {
		res->smc_res.x[0] = rsi_rc;
	}
	res->action = rsi_action;
}

void handle_rsi_rdev_lock(struct rec *rec, struct rmi_rec_exit *rec_exit,
			  struct rsi_result *res)
{
	unsigned long rsi_rc;
	enum rsi_action rsi_action;
	unsigned long vdev_id;
	unsigned long vdev_inst_id;
	struct realm_device *rdev;
	struct dev_tdisp_params *tdisp_params;
	struct vdev *vd;
	struct rec_plane *plane;
	struct rd *rd;

	/* Set default action to return to Realm */
	rsi_action = UPDATE_REC_RETURN_TO_REALM;

	/* RSI calls can only be issued by Plane 0 */
	plane = rec_plane_0(rec);

	/*
	 * X1: Virtual device identifier
	 * X2: Device instance identifier
	 */
	vdev_id = plane->regs[1];
	vdev_inst_id = plane->regs[2];

	if (!rec->da_enabled) {
		rsi_rc = RSI_ERROR_STATE;
		goto out;
	}

	/* rd granule mapped but not locked */
	rd = buffer_granule_map(rec->realm_info.g_rd, SLOT_RD);
	assert(rd != NULL);

	/*
	 * For now, assume that g_vdev cached by smc_vdev_create() will be used
	 * here. Return error if g_vdev is not cached. Will be corrected in
	 * alp14+ implementation
	 */
	if (rd->g_vdev == NULL) {
		rsi_rc = RSI_ERROR_INPUT;
		goto out_rd_unmap;
	}
	granule_lock(rd->g_vdev, GRANULE_STATE_VDEV);
	vd = buffer_granule_map(rd->g_vdev, SLOT_VDEV);
	assert(vd != NULL);

	if ((vd->id != vdev_id) || (vd->inst_id != vdev_inst_id)) {
		rsi_rc = RSI_ERROR_INPUT;
		goto out_vd_unmap;
	}

	rdev = &vd->rdev;

	if (rdev->rsi_state != RSI_RDEV_STATE_UNLOCKED) {
		rsi_rc = RSI_ERROR_DEVICE;
		goto out_vd_unmap;
	}

	rsi_rc = set_dev_state(vd);
	if (rsi_rc != RSI_SUCCESS) {
		goto out_vd_unmap;
	}

	/* Set TDISP parameters */
	tdisp_params = &rdev->op_params.tdisp_params;
	(void)memset(tdisp_params, 0, sizeof(struct dev_tdisp_params));
	(void)memset(rdev->start_interface_nonce, 0,
		     sizeof(rdev->start_interface_nonce));

	tdisp_params->tdi_id = (uint32_t)(vd->tdi_id & 0xffffUL);
	tdisp_params->start_interface_nonce = rdev->start_interface_nonce;

	rdev->rsi_state = RSI_RDEV_STATE_UNLOCKED_BUSY;
	rdev->op = RDEV_OP_LOCK;

	/*
	 * Exit to host to compare vdev_id and inst_id and provide the PA of
	 * VDEV
	 */
	rec->vdev.id = vdev_id;
	rec->vdev.inst_id = vdev_inst_id;
	rec->vdev.inst_id_valid = true;
	rec_set_pending_op(rec, REC_PENDING_VDEV_COMPLETE);

	rec_exit->vdev_id = vdev_id;
	rec_exit->exit_reason = RMI_EXIT_VDEV_REQUEST;
	rsi_action = UPDATE_REC_EXIT_TO_HOST;

out_vd_unmap:
	buffer_unmap(vd);
	granule_unlock(rd->g_vdev);
out_rd_unmap:
	buffer_unmap(rd);
out:
	if (rsi_action == UPDATE_REC_RETURN_TO_REALM) {
		res->smc_res.x[0] = rsi_rc;
	}
	res->action = rsi_action;
}

void handle_rsi_rdev_start(struct rec *rec, struct rmi_rec_exit *rec_exit,
			   struct rsi_result *res)
{
	unsigned long rsi_rc;
	enum rsi_action rsi_action;
	unsigned long vdev_id;
	unsigned long vdev_inst_id;
	struct realm_device *rdev;
	struct dev_tdisp_params *tdisp_params;
	struct vdev *vd;
	struct rec_plane *plane;
	struct rd *rd;

	/* Set default action to return to Realm */
	rsi_action = UPDATE_REC_RETURN_TO_REALM;

	/* RSI calls can only be issued by Plane 0 */
	plane = rec_plane_0(rec);

	/*
	 * X1: Virtual device identifier
	 * X2: Device instance identifier
	 * X3: RsiDevStartFlags (not used)
	 * X4: non_ats_plane (not used)
	 *
	 * Only one vdev is supported
	 * todo: implement rdev_lookup(vdev_id, vdev_inst_id)
	 */
	vdev_id = plane->regs[1];
	vdev_inst_id = plane->regs[2];

	if (!rec->da_enabled) {
		rsi_rc = RSI_ERROR_STATE;
		goto out;
	}

	/* rd granule mapped but not locked */
	rd = buffer_granule_map(rec->realm_info.g_rd, SLOT_RD);
	assert(rd != NULL);

	/*
	 * For now, assume that g_vdev cached by smc_vdev_create() will be used
	 * here. Return error if g_vdev is not cached. Will be corrected in
	 * alp14+ implementation
	 */
	if (rd->g_vdev == NULL) {
		rsi_rc = RSI_ERROR_INPUT;
		goto out_rd_unmap;
	}

	granule_lock(rd->g_vdev, GRANULE_STATE_VDEV);
	vd = buffer_granule_map(rd->g_vdev, SLOT_VDEV);
	assert(vd != NULL);

	if ((vd->id != vdev_id) || (vd->inst_id != vdev_inst_id)) {
		rsi_rc = RSI_ERROR_INPUT;
		goto out_vd_unmap;
	}

	rdev = &vd->rdev;

	if (rdev->rsi_state != RSI_RDEV_STATE_LOCKED) {
		rsi_rc = RSI_ERROR_DEVICE;
		goto out_vd_unmap;
	}

	rsi_rc = set_dev_state(vd);
	if (rsi_rc != RSI_SUCCESS) {
		goto out_vd_unmap;
	}

	/* Set TDISP parameters */
	tdisp_params = &rdev->op_params.tdisp_params;
	(void)memset(tdisp_params, 0, sizeof(struct dev_tdisp_params));

	tdisp_params->tdi_id = (uint32_t)(vd->tdi_id & 0xffffUL);
	tdisp_params->start_interface_nonce = rdev->start_interface_nonce;

	rdev->rsi_state = RSI_RDEV_STATE_LOCKED_BUSY;
	rdev->op = RDEV_OP_START;

	/*
	 * Exit to host to compare vdev_id and inst_id and provide the PA of
	 * VDEV
	 */
	rec->vdev.id = vdev_id;
	rec->vdev.inst_id = vdev_inst_id;
	rec->vdev.inst_id_valid = true;
	rec_set_pending_op(rec, REC_PENDING_VDEV_COMPLETE);

	rec_exit->vdev_id = vdev_id;
	rec_exit->exit_reason = RMI_EXIT_VDEV_REQUEST;
	rsi_action = UPDATE_REC_EXIT_TO_HOST;

out_vd_unmap:
	buffer_unmap(vd);
	granule_unlock(rd->g_vdev);
out_rd_unmap:
	buffer_unmap(rd);
out:
	if (rsi_action == UPDATE_REC_RETURN_TO_REALM) {
		res->smc_res.x[0] = rsi_rc;
	}
	res->action = rsi_action;
}

void handle_rsi_rdev_stop(struct rec *rec, struct rmi_rec_exit *rec_exit,
			  struct rsi_result *res)
{
	unsigned long rsi_rc;
	enum rsi_action rsi_action;
	unsigned long vdev_id;
	unsigned long vdev_inst_id;
	struct realm_device *rdev;
	struct dev_tdisp_params *tdisp_params;
	struct vdev *vd;
	struct rec_plane *plane;
	struct rd *rd;

	/* Set default action to return to Realm */
	rsi_action = UPDATE_REC_RETURN_TO_REALM;

	/* RSI calls can only be issued by Plane 0 */
	plane = rec_plane_0(rec);

	/*
	 * X1: Virtual device identifier
	 * X2: Device instance identifier
	 */
	vdev_id = plane->regs[1];
	vdev_inst_id = plane->regs[2];

	if (!rec->da_enabled) {
		rsi_rc = RSI_ERROR_STATE;
		goto out;
	}

	/* rd granule mapped but not locked */
	rd = buffer_granule_map(rec->realm_info.g_rd, SLOT_RD);
	assert(rd != NULL);

	/*
	 * For now, assume that g_vdev cached by smc_vdev_create() will be used
	 * here. Return error if g_vdev is not cached. Will be corrected in
	 * alp14+ implementation
	 */
	if (rd->g_vdev == NULL) {
		rsi_rc = RSI_ERROR_INPUT;
		goto out_rd_unmap;
	}
	granule_lock(rd->g_vdev, GRANULE_STATE_VDEV);
	vd = buffer_granule_map(rd->g_vdev, SLOT_VDEV);
	assert(vd != NULL);

	if ((vd->id != vdev_id) || (vd->inst_id != vdev_inst_id)) {
		rsi_rc = RSI_ERROR_INPUT;
		goto out_vd_unmap;
	}

	rdev = &vd->rdev;

	if ((rdev->rsi_state != RSI_RDEV_STATE_UNLOCKED) &&
	    (rdev->rsi_state != RSI_RDEV_STATE_LOCKED) &&
	    (rdev->rsi_state != RSI_RDEV_STATE_STARTED) &&
	    (rdev->rsi_state != RSI_RDEV_STATE_ERROR)) {
		rsi_rc = RSI_ERROR_DEVICE;
		goto out_vd_unmap;
	}

	rsi_rc = set_dev_state(vd);
	if (rsi_rc != RSI_SUCCESS) {
		goto out_vd_unmap;
	}

	/* Set TDISP parameters */
	tdisp_params = &rdev->op_params.tdisp_params;
	(void)memset(tdisp_params, 0, sizeof(struct dev_tdisp_params));
	tdisp_params->tdi_id = (uint32_t)(vd->tdi_id & 0xffffUL);

	rdev->rsi_state = RSI_RDEV_STATE_STOPPING;
	rdev->op = RDEV_OP_STOP;

	/*
	 * Exit to host to compare vdev_id and inst_id and provide the PA of
	 * VDEV
	 */
	rec->vdev.id = vdev_id;
	rec->vdev.inst_id = vdev_inst_id;
	rec->vdev.inst_id_valid = true;
	rec_set_pending_op(rec, REC_PENDING_VDEV_COMPLETE);

	rec_exit->vdev_id = vdev_id;
	rec_exit->exit_reason = RMI_EXIT_VDEV_REQUEST;
	rsi_action = UPDATE_REC_EXIT_TO_HOST;

out_vd_unmap:
	buffer_unmap(vd);
	granule_unlock(rd->g_vdev);
out_rd_unmap:
	buffer_unmap(rd);
out:
	if (rsi_action == UPDATE_REC_RETURN_TO_REALM) {
		res->smc_res.x[0] = rsi_rc;
	}
	res->action = rsi_action;
}

void handle_rsi_rdev_get_interface_report(struct rec *rec,
					  struct rmi_rec_exit *rec_exit,
					  struct rsi_result *res)
{
	unsigned long rsi_rc;
	enum rsi_action rsi_action;
	unsigned long vdev_id;
	unsigned long vdev_inst_id;
	unsigned long tdisp_version_max;
	struct realm_device *rdev;
	struct dev_tdisp_params *tdisp_params;
	struct vdev *vd;
	struct rec_plane *plane;
	struct rd *rd;

	/* Set default action to return to Realm */
	rsi_action = UPDATE_REC_RETURN_TO_REALM;

	/* RSI calls can only be issued by Plane 0 */
	plane = rec_plane_0(rec);

	/*
	 * X1: Virtual device identifier
	 * X2: Device instance identifier
	 * X3: Max TDISP version accepted by the Realm
	 */
	vdev_id = plane->regs[1];
	vdev_inst_id = plane->regs[2];
	tdisp_version_max = plane->regs[3];

	if (!rec->da_enabled) {
		rsi_rc = RSI_ERROR_STATE;
		goto out;
	}

	/* rd granule mapped but not locked */
	rd = buffer_granule_map(rec->realm_info.g_rd, SLOT_RD);
	assert(rd != NULL);

	/*
	 * For now, assume that g_vdev cached by smc_vdev_create() will be used
	 * here. Return error if g_vdev is not cached. Will be corrected in
	 * alp14+ implementation
	 */
	if (rd->g_vdev == NULL) {
		rsi_rc = RSI_ERROR_INPUT;
		goto out_rd_unmap;
	}
	granule_lock(rd->g_vdev, GRANULE_STATE_VDEV);
	vd = buffer_granule_map(rd->g_vdev, SLOT_VDEV);
	assert(vd != NULL);

	if ((vd->id != vdev_id) || (vd->inst_id != vdev_inst_id)) {
		rsi_rc = RSI_ERROR_INPUT;
		goto out_vd_unmap;
	}

	rdev = &vd->rdev;

	if ((rdev->rsi_state != RSI_RDEV_STATE_LOCKED) &&
	    (rdev->rsi_state != RSI_RDEV_STATE_STARTED)) {
		rsi_rc = RSI_ERROR_DEVICE;
		goto out_vd_unmap;
	}

	rsi_rc = set_dev_state(vd);
	if (rsi_rc != RSI_SUCCESS) {
		goto out_vd_unmap;
	}

	if (rdev->rsi_state == RSI_RDEV_STATE_LOCKED) {
		rdev->rsi_state = RSI_RDEV_STATE_LOCKED_BUSY;
	} else {
		rdev->rsi_state = RSI_RDEV_STATE_STARTED_BUSY;
	}
	rdev->op = RDEV_OP_GET_INTERFACE_REPORT;

	/* Set TDISP parameters */
	tdisp_params = &rdev->op_params.tdisp_params;
	(void)memset(tdisp_params, 0, sizeof(struct dev_tdisp_params));
	tdisp_params->tdi_id = (uint32_t)(vd->tdi_id & 0xffffUL);

	/* todo: add interface_report_params in RDEV */
	(void)tdisp_version_max;

	/*
	 * Exit to host to compare vdev_id and inst_id and provide the PA of
	 * VDEV
	 */
	rec->vdev.id = vdev_id;
	rec->vdev.inst_id = vdev_inst_id;
	rec->vdev.inst_id_valid = true;
	rec_set_pending_op(rec, REC_PENDING_VDEV_COMPLETE);

	rec_exit->vdev_id = vdev_id;
	rec_exit->exit_reason = RMI_EXIT_VDEV_REQUEST;
	rsi_action = UPDATE_REC_EXIT_TO_HOST;

out_vd_unmap:
	buffer_unmap(vd);
	granule_unlock(rd->g_vdev);
out_rd_unmap:
	buffer_unmap(rd);
out:
	if (rsi_action == UPDATE_REC_RETURN_TO_REALM) {
		res->smc_res.x[0] = rsi_rc;
	}
	res->action = rsi_action;

	/*
	 * Set tdisp_version to PCI_TDISP_MESSAGE_VERSION_10 (0x10). This will be
	 * changed in alp13 to get from DEV_GET_INFO
	 */
	res->smc_res.x[1] = 0x10; /* PCI_TDISP_MESSAGE_VERSION_10 */
}

/* Validate Realm device memory mappings */
void handle_rsi_rdev_validate_mapping(struct rec *rec,
				      struct rmi_rec_exit *rec_exit,
				      struct rsi_result *res)
{
	struct rd *rd;
	unsigned long rsi_rc;
	enum rsi_action rsi_action;
	unsigned long vdev_id;
	unsigned long vdev_inst_id;
	struct realm_device *rdev;
	struct vdev *vd;
	struct rec_plane *plane;
	unsigned long target_ipa_base;
	unsigned long target_ipa_top;
	unsigned long target_pa_base;
	unsigned long mmio_flags;

	/* Set default action to return to Realm */
	rsi_action = UPDATE_REC_RETURN_TO_REALM;

	/* RSI calls can only be issued by Plane 0 */
	plane = rec_plane_0(rec);

	/*
	 * X1: Virtual device identifier
	 * X2: Device instance identifier
	 * X3: Base of target IPA region
	 * X4: Top of target IPA region
	 * X5: Base of target PA region
	 * X6: Flags of type RsiDevMemFlags
	 */
	vdev_id = plane->regs[1];
	vdev_inst_id = plane->regs[2];
	target_ipa_base = plane->regs[3];
	target_ipa_top = plane->regs[4];
	target_pa_base = plane->regs[5];
	mmio_flags = plane->regs[6];

	(void)vdev_id;
	(void)vdev_inst_id;

	if (!GRANULE_ALIGNED(target_ipa_base) ||
	    !GRANULE_ALIGNED(target_ipa_top) ||
	    !GRANULE_ALIGNED(target_pa_base) ||
	    (target_ipa_top <= target_ipa_base)) {
		rsi_rc = RSI_ERROR_INPUT;
		goto out;
	}

	/* rd granule mapped but not locked */
	rd = buffer_granule_map(rec->realm_info.g_rd, SLOT_RD);
	assert(rd != NULL);

	if (!rd->da_enabled) {
		rsi_rc = RSI_ERROR_STATE;
		goto out_rd_unmap;
	}

	/* This will be replaced by rdev_from_inst_id() */
	if (rd->g_vdev == NULL) {
		rsi_rc = RSI_ERROR_INPUT;
		goto out_rd_unmap;
	}
	vd = buffer_granule_map(rd->g_vdev, SLOT_VDEV);
	if (vd == NULL) {
		rsi_rc = RSI_ERROR_INPUT;
		goto out_rd_unmap;
	}

	rdev = &vd->rdev;

	if ((rdev->rsi_state != RSI_RDEV_STATE_LOCKED) &&
	    (rdev->rsi_state != RSI_RDEV_STATE_STARTED)) {
		rsi_rc = RSI_ERROR_DEVICE;
		goto out_vd_unmap;
	}

	/* Update REC dev_mem */
	rec->dev_mem.base = target_ipa_base;
	rec->dev_mem.top = target_ipa_top;
	rec->dev_mem.addr = target_ipa_base;
	rec->dev_mem.pa = target_pa_base;
	rec->dev_mem.flags = mmio_flags;

	/* Update REC exit dev_mem */
	rec_exit->exit_reason = RMI_EXIT_DEV_MEM_MAP;
	rec_exit->dev_mem_base = target_ipa_base;
	rec_exit->dev_mem_top = target_ipa_top;
	rec_exit->dev_mem_pa = target_pa_base;

	/* Exit to host to process DEV mem mapping */
	rsi_action = UPDATE_REC_EXIT_TO_HOST;

out_vd_unmap:
	buffer_unmap(vd);
out_rd_unmap:
	buffer_unmap(rd);
out:
	if (rsi_action == UPDATE_REC_RETURN_TO_REALM) {
		res->smc_res.x[0] = rsi_rc;
	}
	res->action = rsi_action;
}

void handle_rsi_rdev_continue(struct rec *rec, struct rmi_rec_exit *rec_exit,
			      struct rsi_result *res)
{
	unsigned long rsi_rc;
	enum rsi_action rsi_action;
	unsigned long vdev_id;
	unsigned long vdev_inst_id;
	struct realm_device *rdev;
	struct vdev *vd;
	struct rec_plane *plane;
	struct rd *rd;

	/* Set default action to return to Realm */
	rsi_action = UPDATE_REC_RETURN_TO_REALM;

	/* RSI calls can only be issued by Plane 0 */
	plane = rec_plane_0(rec);

	/*
	 * X1: Virtual device identifier
	 * X2: Device instance identifier
	 */
	vdev_id = plane->regs[1];
	vdev_inst_id = plane->regs[2];

	if (!rec->da_enabled) {
		rsi_rc = RSI_ERROR_STATE;
		goto out;
	}

	/* todo: check RdevIdsAreValid */
	(void)vdev_id;
	(void)vdev_inst_id;

	/* rd granule mapped but not locked */
	rd = buffer_granule_map(rec->realm_info.g_rd, SLOT_RD);
	assert(rd != NULL);

	/*
	 * For now, assume that g_vdev cached by smc_vdev_create() will be used
	 * here. Return error if g_vdev is not cached. Will be corrected in
	 * alp14+ implementation
	 */
	if (rd->g_vdev == NULL) {
		rsi_rc = RSI_ERROR_INPUT;
		goto out_rd_unmap;
	}
	granule_lock(rd->g_vdev, GRANULE_STATE_VDEV);
	vd = buffer_granule_map(rd->g_vdev, SLOT_VDEV);
	assert(vd != NULL);

	if ((vd->id != vdev_id) || (vd->inst_id != vdev_inst_id)) {
		rsi_rc = RSI_ERROR_INPUT;
		goto out_vd_unmap;
	}

	rdev = &vd->rdev;

	if ((rdev->rsi_state != RSI_RDEV_STATE_UNLOCKED_BUSY) &&
	    (rdev->rsi_state != RSI_RDEV_STATE_LOCKED_BUSY) &&
	    (rdev->rsi_state != RSI_RDEV_STATE_STARTED_BUSY) &&
	    (rdev->rsi_state != RSI_RDEV_STATE_STOPPING)) {
		rsi_rc = RSI_ERROR_DEVICE;
		goto out_vd_unmap;
	}

	switch (rdev->op) {
	case RDEV_OP_GET_MEASUREMENTS:
		rsi_action = UPDATE_REC_EXIT_TO_HOST;
		rec_exit->vdev_action = (unsigned char)RMI_VDEV_ACTION_GET_MEASUREMENTS;
		break;
	case RDEV_OP_GET_INTERFACE_REPORT:
		rsi_action = UPDATE_REC_EXIT_TO_HOST;
		rec_exit->vdev_action = (unsigned char)RMI_VDEV_ACTION_GET_INTERFACE_REPORT;
		break;
	case RDEV_OP_LOCK:
		rsi_action = UPDATE_REC_EXIT_TO_HOST;
		rec_exit->vdev_action = (unsigned char)RMI_VDEV_ACTION_LOCK;
		break;
	case RDEV_OP_START:
		rsi_action = UPDATE_REC_EXIT_TO_HOST;
		rec_exit->vdev_action = (unsigned char)RMI_VDEV_ACTION_START;
		break;
	case RDEV_OP_STOP:
		rsi_action = UPDATE_REC_EXIT_TO_HOST;
		rec_exit->vdev_action = (unsigned char)RMI_VDEV_ACTION_STOP;
		break;
	case RDEV_OP_NONE:
		rsi_rc = RSI_SUCCESS;
		break;
	default:
		rsi_rc = RSI_ERROR_INPUT;
		break;
	}

	/* Exit to host to do VDEV COMM */
	if (rsi_action == UPDATE_REC_EXIT_TO_HOST) {
		/*
		 * Update REC exit fields to NS host to get the VDEV ptr
		 * todo: RMM must get this vdev_addr using VDEV request?
		 */
		rec_exit->exit_reason = RMI_EXIT_VDEV_COMM;
		rec_exit->vdev = rdev->vdev_addr;

		/*
		 * Spec A9.4.3.2 State transitions:
		 * VDEV_READY to VDEV_COMMUNICATING
		 *     REC exit due to VDEV communication
		 */
		if (vd->rmi_state == RMI_VDEV_STATE_READY) {
			vd->rmi_state = RMI_VDEV_STATE_COMMUNICATING;
		}

		/*
		 * todo: not in spec. update REC vdev fields. When REC re-enters
		 * this flag will be checked for completion of RDEV request.
		 */
		rec->vdev.is_comm = true;
		rec->vdev.vdev_addr = rdev->vdev_addr;
	}
	res->action = rsi_action;

out_vd_unmap:
	buffer_unmap(vd);
	granule_unlock(rd->g_vdev);
out_rd_unmap:
	buffer_unmap(rd);
out:
	if (rsi_action == UPDATE_REC_RETURN_TO_REALM) {
		res->smc_res.x[0] = rsi_rc;
	}
}

static void rdev_state_transition_on_success(struct realm_device *rdev)
{
	switch (rdev->op) {
	case RDEV_OP_GET_MEASUREMENTS:
		if (rdev->rsi_state == RSI_RDEV_STATE_UNLOCKED_BUSY) {
			rdev->rsi_state = RSI_RDEV_STATE_UNLOCKED;
		} else if (rdev->rsi_state == RSI_RDEV_STATE_LOCKED_BUSY) {
			rdev->rsi_state = RSI_RDEV_STATE_LOCKED;
		} else if (rdev->rsi_state == RSI_RDEV_STATE_STARTED_BUSY) {
			rdev->rsi_state = RSI_RDEV_STATE_STARTED;
		} else {
			goto invalid_transition;
		}
		break;
	case RDEV_OP_GET_INTERFACE_REPORT:
		if (rdev->rsi_state == RSI_RDEV_STATE_LOCKED_BUSY) {
			rdev->rsi_state = RSI_RDEV_STATE_LOCKED;
		} else if (rdev->rsi_state == RSI_RDEV_STATE_STARTED_BUSY) {
			rdev->rsi_state = RSI_RDEV_STATE_STARTED;
		} else {
			goto invalid_transition;
		}
		break;
	case RDEV_OP_LOCK:
		if (rdev->rsi_state == RSI_RDEV_STATE_UNLOCKED_BUSY) {
			rdev->rsi_state = RSI_RDEV_STATE_LOCKED;
		} else {
			goto invalid_transition;
		}
		break;
	case RDEV_OP_START:
		if (rdev->rsi_state == RSI_RDEV_STATE_LOCKED_BUSY) {
			rdev->rsi_state = RSI_RDEV_STATE_STARTED;
		} else {
			goto invalid_transition;
		}
		break;
	case RDEV_OP_STOP:
		if (rdev->rsi_state == RSI_RDEV_STATE_STOPPING) {
			/* todo: not STOPPED. Set to UNLOCKED? */
			rdev->rsi_state = RSI_RDEV_STATE_UNLOCKED;
		} else {
			goto invalid_transition;
		}
		break;
	default:
		goto invalid_transition;
	}

	rdev->op = RDEV_OP_NONE;
	return;

invalid_transition:
	ERROR("Invalid RDEV state transition: state=%lu, op=%lu\n", rdev->rsi_state, rdev->op);
}

static void rdev_state_transition_on_error(struct realm_device *rdev)
{
	if (rdev->rsi_state == RSI_RDEV_STATE_STOPPING) {
		/* todo: not STOPPED. Set to UNLOCKED? */
		rdev->rsi_state = RSI_RDEV_STATE_UNLOCKED;
	} else {
		rdev->rsi_state = RSI_RDEV_STATE_ERROR;
	}

	rdev->op = RDEV_OP_NONE;
}

void rdev_state_transition(struct realm_device *rdev,
			   unsigned long dev_comm_state)
{
	if ((rdev == NULL) || (rdev->op == RDEV_OP_NONE)) {
		return;
	}

	switch (dev_comm_state) {
	case DEV_COMM_IDLE:
		rdev_state_transition_on_success(rdev);
		break;
	case DEV_COMM_ERROR:
		rdev_state_transition_on_error(rdev);
		break;
	case DEV_COMM_ACTIVE:
		/* No state change required */
		break;
	case DEV_COMM_PENDING:
		rdev_state_transition_on_error(rdev);
		break;
	default:
		ERROR("Rdev State transition: Invalid Comm state: %lu\n", dev_comm_state);
	}
}

/*
 * Called from REC enter to check if RDEV communication request is completed by
 * the VDEV
 */
void handle_rsi_rdev_complete(struct rec *rec)
{
	struct granule *g_vdev;
	unsigned long rsi_rc;
	unsigned long vdev_addr;
	struct vdev *vd;
	struct rec_plane *plane;

	assert(rec->vdev.is_comm == true);

	vdev_addr = rec->vdev.vdev_addr;
	/* Lock VDEV granule and map it */
	g_vdev = find_lock_granule(vdev_addr, GRANULE_STATE_VDEV);
	if (g_vdev == NULL) {
		rsi_rc = RSI_ERROR_STATE;
		goto out_err_unlock;
	}
	vd = buffer_granule_map(g_vdev, SLOT_VDEV);
	assert(vd != NULL);

	if (vd->rmi_state == RMI_VDEV_STATE_READY) {
		rec->vdev.is_comm = false;
		rsi_rc = RSI_SUCCESS;
	} else if (vd->rmi_state == RMI_VDEV_STATE_COMMUNICATING) {
		rsi_rc = RSI_INCOMPLETE;
	} else {
		ERROR("RDEV comm request resulted in device error\n");
		rec->vdev.is_comm = false;
		rsi_rc = RSI_ERROR_DEVICE;
	}

	buffer_unmap(vd);

out_err_unlock:
	granule_unlock(g_vdev);

	/* RSI calls can only be issued by Plane 0 */
	plane = rec_plane_0(rec);

	plane->regs[0] = rsi_rc;
}
