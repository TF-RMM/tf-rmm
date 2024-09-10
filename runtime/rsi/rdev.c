/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <buffer.h>
#include <dev.h>
#include <dev_assign_app.h>
#include <granule.h>
#include <limits.h>
#include <realm.h>
#include <rsi-handler.h>
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
	/* granule_unlock(rec->realm_info.g_rd); */

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
