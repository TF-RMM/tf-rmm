/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <buffer.h>
#include <realm.h>
#include <rec.h>
#include <rsi-handler.h>
#include <smmuv3.h>
#include <string.h>

/*
 * TODO: Currently the pci_tdisp_get_version() call made during RMI_VDEV_LOCK in
 * the DA app mandates that the version is 0x10. It would be better if that
 * function returned the version and it could be saved in the vdev.
 */
#define PCI_TDISP_MESSAGE_VERSION_10			UL(0x10)
#define PCI_TDISP_MESSAGE_VERSION PCI_TDISP_MESSAGE_VERSION_10

#define PCI_TDISP_MESSAGE_VERSION_MINOR_SHIFT		U(0)
#define PCI_TDISP_MESSAGE_VERSION_MINOR_WIDTH		U(4)
#define PCI_TDISP_MESSAGE_VERSION_MAJOR_SHIFT		U(4)
#define PCI_TDISP_MESSAGE_VERSION_MAJOR_WIDTH		U(4)

#define VDEV_INFO_FORMAT_VERSION_MINOR_SHIFT		U(0)
#define VDEV_INFO_FORMAT_VERSION_MINOR_WIDTH		U(16)
#define VDEV_INFO_FORMAT_VERSION_MAJOR_SHIFT		U(16)
#define VDEV_INFO_FORMAT_VERSION_MAJOR_WIDTH		U(16)
#define VDEV_INFO_FORMAT_VERSION(major, minor) \
	(COMPOSE(VDEV_INFO_FORMAT_VERSION_MAJOR, major) | \
	 COMPOSE(VDEV_INFO_FORMAT_VERSION_MINOR, minor))

struct rsi_vdev_obj {
	struct granule *g_rd;
	struct granule *g_pdev;
	struct granule *g_vdev;
	struct rd *rd;
	struct pdev *pd;
	struct vdev *vd;
};

static unsigned long rsi_vdev_claim_objects(unsigned long vdev_id, struct rec *rec,
					    struct rsi_vdev_obj *lock_set, bool claim_pdev);

static void rsi_vdev_release_objects(struct rsi_vdev_obj *lock_set);

void handle_rsi_vdev_dma_enable(struct rec *rec,
				struct rmi_rec_exit *rec_exit,
				struct rsi_result *res)
{
	struct rec_plane *plane;
	struct rsi_vdev_obj lock_set = {0};
	unsigned long rc;
	unsigned long vdev_id;
	unsigned long non_ats_plane;
	unsigned long lock_nonce;
	unsigned long meas_nonce;
	unsigned long report_nonce;

	(void)rec_exit;

	/* TODO: check ats in flags */

	/* RSI calls can only be issued by Plane 0 */
	plane = rec_plane_0(rec);
	assert(rec_is_plane_0_active(rec));

	res->action = UPDATE_REC_RETURN_TO_REALM;

	if ((!rec->da_enabled)) {
		res->smc_res.x[0] = RSI_ERROR_STATE;
		return;
	}

	vdev_id = plane->regs[1];
	non_ats_plane = plane->regs[3];
	lock_nonce = plane->regs[4];
	meas_nonce = plane->regs[5];
	report_nonce = plane->regs[6];

	/* claim the external objects internally */
	rc = rsi_vdev_claim_objects(vdev_id, rec, &lock_set, false);
	if (rc != RSI_SUCCESS) {
		res->smc_res.x[0] = rc;
		goto out;
	}
	assert(lock_set.vd != NULL);
	assert(lock_set.rd != NULL);

	if ((lock_set.rd->num_aux_planes > 0U) &&
	    ((non_ats_plane == 0U) || (non_ats_plane > lock_set.rd->num_aux_planes))) {
		/* TODO_ALP17: Check the above condition in latest spec */
		res->smc_res.x[0] = RSI_ERROR_INPUT;
		goto out;
	}

	if ((lock_set.vd->rmi_state != RMI_VDEV_STATE_STARTED) ||
	    (lock_nonce != lock_set.vd->attest_info.lock_nonce) ||
	    (meas_nonce != lock_set.vd->attest_info.meas_nonce) ||
	    (report_nonce != lock_set.vd->attest_info.report_nonce)) {
		res->smc_res.x[0] = RSI_ERROR_DEVICE;
		goto out;
	}

	rc = RSI_SUCCESS;
	if (lock_set.vd->dma_state != RMI_VDEV_DMA_ENABLED) {
		/* Only call the driver if not already enabled */
		/* TODO_ALP17: set non_ats_plane in vdev */

		if (smmuv3_enable_ste(lock_set.vd->smmu_idx, lock_set.vd->sid) != 0) {
			rc = RSI_ERROR_DEVICE;
		} else {
			lock_set.vd->dma_state = RMI_VDEV_DMA_ENABLED;
		}
	}

	res->smc_res.x[0] = rc;

out:
	rsi_vdev_release_objects(&lock_set);
}

void handle_rsi_vdev_dma_disable(struct rec *rec,
				 struct rmi_rec_exit *rec_exit,
				 struct rsi_result *res)
{
	struct rec_plane *plane;
	struct rsi_vdev_obj lock_set = {0};
	unsigned long rc;
	unsigned long vdev_id;

	(void)rec_exit;

	/* RSI calls can only be issued by Plane 0 */
	plane = rec_plane_0(rec);
	assert(rec_is_plane_0_active(rec));

	res->action = UPDATE_REC_RETURN_TO_REALM;

	if ((!rec->da_enabled)) {
		res->smc_res.x[0] = RSI_ERROR_STATE;
		return;
	}

	vdev_id = plane->regs[1];

	/* claim the external objects internally */
	rc = rsi_vdev_claim_objects(vdev_id, rec, &lock_set, false);
	if (rc != RSI_SUCCESS) {
		res->smc_res.x[0] = rc;
		goto out;
	}
	assert(lock_set.vd != NULL);

	rc = RSI_SUCCESS;
	if (lock_set.vd->dma_state != RMI_VDEV_DMA_DISABLED) {
		/* Only call the driver if not already disabled */
		if (smmuv3_disable_ste(lock_set.vd->smmu_idx, lock_set.vd->sid) != 0) {
			rc = RSI_ERROR_DEVICE;
		} else {
			lock_set.vd->dma_state = RMI_VDEV_DMA_DISABLED;
		}
	}

	res->smc_res.x[0] = rc;

out:
	rsi_vdev_release_objects(&lock_set);
}

static void vdev_get_info(struct pdev *pd, struct vdev *vd, struct rsi_vdev_info *vdev_info);

void handle_rsi_vdev_get_info(struct rec *rec,
			      struct rmi_rec_exit *rec_exit,
			      struct rsi_result *res)
{
	void *info_granule_va = NULL;
	struct rsi_vdev_info *vdev_info;
	struct rec_plane *plane;
	struct granule *llt = NULL;
	struct rsi_vdev_obj lock_set = {0};
	unsigned long info_granule_address;
	unsigned long info_addr;
	unsigned long rsi_rc;
	unsigned long vdev_id;

	(void)rec_exit;

	/* RSI calls can only be issued by Plane 0 */
	plane = rec_plane_0(rec);
	assert(rec_is_plane_0_active(rec));

	res->action = UPDATE_REC_RETURN_TO_REALM;

	if ((!rec->da_enabled)) {
		res->smc_res.x[0] = RSI_ERROR_STATE;
		return;
	}

	vdev_id = plane->regs[1];
	info_addr = plane->regs[2];
	info_granule_address = info_addr & GRANULE_MASK;

	if (!ALIGNED(info_addr, 512U)) {
		res->smc_res.x[0] = RSI_ERROR_INPUT;
		return;
	}

	if (!addr_in_rec_par(rec, info_addr)) {
		res->smc_res.x[0] = RSI_ERROR_INPUT;
		return;
	}

	if (!realm_mem_lock_map(rec, info_granule_address, &info_granule_va, &llt, res)) {
		return;
	}

	assert((info_granule_va != NULL) && (llt != NULL));

	/* we know have a valid ipa with assigned and DATA */
	vdev_info = (struct rsi_vdev_info *)
		((uintptr_t)info_granule_va + (info_addr - info_granule_address));

	/* claim the external objects internally */
	rsi_rc = rsi_vdev_claim_objects(vdev_id, rec, &lock_set, true);
	if (rsi_rc != RSI_SUCCESS) {
		res->smc_res.x[0] = rsi_rc;
		goto out;
	}
	assert(lock_set.vd != NULL);
	assert(lock_set.pd != NULL);

	vdev_get_info(lock_set.pd, lock_set.vd, vdev_info);
	res->smc_res.x[0] = RSI_SUCCESS;

out:
	rsi_vdev_release_objects(&lock_set);
	buffer_unmap(info_granule_va);
	granule_unlock(llt);
}

static unsigned char vdev_state_to_rsi(uint32_t vdev_rmi_state)
{
	switch (vdev_rmi_state) {
	case RMI_VDEV_STATE_NEW: return RSI_VDEV_STATE_UNLOCKED;
	case RMI_VDEV_STATE_UNLOCKED: return RSI_VDEV_STATE_UNLOCKED;
	case RMI_VDEV_STATE_LOCKED: return RSI_VDEV_STATE_LOCKED;
	case RMI_VDEV_STATE_STARTED: return RSI_VDEV_STATE_STARTED;
	case RMI_VDEV_STATE_ERROR: return RSI_VDEV_STATE_ERROR;
	case RMI_VDEV_STATE_KEY_REFRESH: return RSI_VDEV_STATE_STARTED;
	case RMI_VDEV_STATE_KEY_PURGE: return RSI_VDEV_STATE_STARTED;
	default:
		assert(false);
		return RSI_VDEV_STATE_ERROR;
	}
}

/*
 * Copy device info and attestation digest of VCA, certificate, public key,
 * device measurements to buffer 'vdev_info'
 */
static void vdev_get_info(struct pdev *pd, struct vdev *vd, struct rsi_vdev_info *vdev_info)
{
	(void)memset(vdev_info, 0, sizeof(*vdev_info));

	/*
	 * Set certificate slot id and RMI hash algorithm. RMI and RSI hash
	 * algorithm enumeration uses the same value.
	 */
	vdev_info->cert_id = pd->dev.cert_slot_id;
	vdev_info->hash_algo = pd->rmi_hash_algo;

	vdev_info->lock_nonce = vd->attest_info.lock_nonce;
	vdev_info->meas_nonce = vd->attest_info.meas_nonce;
	vdev_info->report_nonce = vd->attest_info.report_nonce;

	/* Return hardcoded format type */
	vdev_info->format_type = (unsigned char)RSI_VDEV_REPORT_FORMAT_TDISP;
	vdev_info->format_version = VDEV_INFO_FORMAT_VERSION(
		EXTRACT(PCI_TDISP_MESSAGE_VERSION_MAJOR, PCI_TDISP_MESSAGE_VERSION),
		EXTRACT(PCI_TDISP_MESSAGE_VERSION_MINOR, PCI_TDISP_MESSAGE_VERSION));
	vdev_info->state = vdev_state_to_rsi(vd->rmi_state);

	(void)memcpy(vdev_info->vca_digest, pd->vca_digest.value,
		     pd->vca_digest.len);
	(void)memcpy(vdev_info->cert_digest, pd->cert_digest.value,
		     pd->cert_digest.len);
	/* TODO_ALP17: Set proper public_key */
	(void)memcpy(vdev_info->meas_digest, vd->meas_digest.value,
		     vd->meas_digest.len);
	(void)memcpy(vdev_info->report_digest, vd->ifc_report_digest.value,
		     vd->ifc_report_digest.len);
}

void handle_rsi_vdev_validate_mapping(struct rec *rec,
				      struct rmi_rec_exit *rec_exit,
				      struct rsi_result *res)
{
	unsigned long rsi_rc;
	struct rec_plane *plane;
	struct rsi_vdev_obj lock_set = {0};
	unsigned long vdev_id;
	unsigned long ipa_base;
	unsigned long ipa_top;
	unsigned long pa_base;
	unsigned long flags;
	unsigned long lock_nonce;
	unsigned long meas_nonce;
	unsigned long report_nonce;

	/* RSI calls can only be issued by Plane 0 */
	plane = rec_plane_0(rec);
	assert(rec_is_plane_0_active(rec));

	res->action = UPDATE_REC_RETURN_TO_REALM;

	if ((!rec->da_enabled)) {
		res->smc_res.x[0] = RSI_ERROR_STATE;
		return;
	}

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

	if (!GRANULE_ALIGNED(ipa_base) ||
	    !GRANULE_ALIGNED(ipa_top) ||
	    !GRANULE_ALIGNED(pa_base) ||
	    (ipa_top <= ipa_base) ||
	    !region_in_rec_par(rec, ipa_base, ipa_top)) {
		res->smc_res.x[0] = RSI_ERROR_INPUT;
		return;
	}

	/* claim the external objects internally */
	rsi_rc = rsi_vdev_claim_objects(vdev_id, rec, &lock_set, false);
	if (rsi_rc != RSI_SUCCESS) {
		res->smc_res.x[0] = rsi_rc;
		return;
	}
	assert(lock_set.vd != NULL);

	if ((lock_set.vd->rmi_state != RMI_VDEV_STATE_LOCKED) &&
	    (lock_set.vd->rmi_state != RMI_VDEV_STATE_STARTED)) {
		res->smc_res.x[0] = RSI_ERROR_INPUT;
		goto out_unlock;
	}

	if ((lock_nonce != lock_set.vd->attest_info.lock_nonce) ||
	    (meas_nonce != lock_set.vd->attest_info.meas_nonce) ||
	    (report_nonce != lock_set.vd->attest_info.report_nonce)) {
		res->smc_res.x[0] = RSI_ERROR_DEVICE;
		goto out_unlock;
	}

	/* Update REC dev_mem */
	rec->dev_mem.base = ipa_base;
	rec->dev_mem.top = ipa_top;
	rec->dev_mem.addr = ipa_base;
	rec->dev_mem.pa = pa_base;
	rec->dev_mem.flags = flags;

	/* Update REC exit dev_mem */
	rec_exit->exit_reason = RMI_EXIT_VDEV_VALIDATE_MAPPING;
	rec_exit->dev_mem_base = ipa_base;
	rec_exit->dev_mem_top = ipa_top;
	rec_exit->dev_mem_pa = pa_base;
	rec_exit->vdev_id_1 = vdev_id;

	/* Update return value */
	res->smc_res.x[0] = RSI_SUCCESS;

	/* Exit to host to process DEV mem mapping */
	res->action = UPDATE_REC_EXIT_TO_HOST;

out_unlock:
	rsi_vdev_release_objects(&lock_set);
}

static void rsi_vdev_release_objects(struct rsi_vdev_obj *lock_set)
{
	if (lock_set->vd != NULL) {
		buffer_unmap(lock_set->vd);
	}
	if (lock_set->pd != NULL) {
		buffer_unmap(lock_set->pd);
	}
	if (lock_set->rd != NULL) {
		buffer_unmap(lock_set->rd);
	}
	if (lock_set->g_vdev != NULL) {
		granule_unlock(lock_set->g_vdev);
	}
	if (lock_set->g_pdev != NULL) {
		granule_unlock(lock_set->g_pdev);
	}
	if (lock_set->g_rd != NULL) {
		granule_unlock(lock_set->g_rd);
	}

	*lock_set = (struct rsi_vdev_obj){0};
}

static bool __unused rsi_vdev_matches_map(struct rd *rd, unsigned long vdev_id,
				 struct granule *g_vdev)
{
	const struct vdev_map *vdev_map;
	struct rd_aux *rd_aux;
	bool matches;

	rd_aux = buffer_rd_aux_granules_map(&rd->aux_granules[0], rd->num_rd_aux);
	assert(rd_aux != NULL);
	vdev_map = sarray_lookup_vdev_map(&rd_aux->vdev_map_hnd, vdev_id);
	matches = (vdev_map != NULL) &&
	       ((unsigned long)vdev_map->vdev == granule_addr(g_vdev));
	buffer_rd_aux_granules_unmap(rd_aux, rd->num_rd_aux);

	return matches;
}

/*
 * Given a vdev_id and rec, lock and map objects: rd, pdev and vdev
 * inside an rsi handler
 *
 * Note: This routine acquires the lock of a cached external object.
 * This is a deviation from the general model where all the external object
 * addresses are provided by the caller and RMM locks them in the required
 * locking order.
 *
 * In the case of a vdev rsi call, the vdev is an external object and its
 * address is not available directly. The rd vdev_map, caches the vdev address
 * in an sarray map and this vdev addr is locked safely without violating the
 * locking discipline.
 */
static unsigned long rsi_vdev_claim_objects(unsigned long vdev_id, struct rec *rec,
					    struct rsi_vdev_obj *lock_set, bool claim_pdev)
{
	const struct vdev_map *vdev_map;
	struct granule *g_rd;
	struct granule *g_vdev;
	struct rd *rd;
	struct rd_aux *rd_aux;
	struct vdev *vd;
	unsigned long rd_addr;
	unsigned long vdev_addr;
	unsigned long pdev_addr = 0UL;
	uint64_t epoch;

	*lock_set = (struct rsi_vdev_obj){0};

	/*
	 * rec object has a positive refcount due to REC_ENTER, rec cannot be destroyed
	 * rec+: REC_ENTER
	 *
	 * rec takes reference on RD object, i.e., rec increments rd's refcount
	 * rec => rd
	 *
	 * rd has a positive ref-count due to rec
	 * rd+: REC
	 *
	 * rd cannot be destroyed (but still subject to modifications)
	 *
	 */
	g_rd = rec->realm_info.g_rd;
	rd_addr = granule_addr(g_rd);

	/* take rd lock to safely access the vdev_id map */
	granule_lock(g_rd, GRANULE_STATE_RD);
	rd = buffer_granule_map(g_rd, SLOT_RD);
	assert(rd != NULL);

	rd_aux = buffer_rd_aux_granules_map(&rd->aux_granules[0], rd->num_rd_aux);
	assert(rd_aux != NULL);
	vdev_map = sarray_lookup_vdev_map(&rd_aux->vdev_map_hnd, vdev_id);
	if (vdev_map == NULL) {
		buffer_rd_aux_granules_unmap(rd_aux, rd->num_rd_aux);
		buffer_unmap(rd);
		granule_unlock(g_rd);
		/* either the host removed the vdev or the realm gave invalid id */
		return RSI_ERROR_INPUT;
	}
	/* record current epoch to track any changes to vdev map */
	epoch = get_rd_obj_map_epoch_locked(rd);
	vdev_addr = (unsigned long)vdev_map->vdev;
	buffer_rd_aux_granules_unmap(rd_aux, rd->num_rd_aux);

	if (claim_pdev) {
		/* Lock VDEV before caching its PDEV address. */
		g_vdev = find_lock_granule(vdev_addr, GRANULE_STATE_VDEV);
		if (g_vdev == NULL) {
			buffer_unmap(rd);
			granule_unlock(g_rd);
			return RSI_INCOMPLETE;
		}

		vd = buffer_granule_map(g_vdev, SLOT_VDEV);
		assert(vd != NULL);
		pdev_addr = granule_addr(vd->g_pdev);
		buffer_unmap(vd);
		granule_unlock(g_vdev);
	}

	buffer_unmap(rd);
	granule_unlock(g_rd);

	/* No locks held; acquire all requested objects in lock order. */
	if (claim_pdev) {
		if (!find_lock_three_granules(
				rd_addr, GRANULE_STATE_RD, &lock_set->g_rd,
				pdev_addr, GRANULE_STATE_PDEV, &lock_set->g_pdev,
				vdev_addr, GRANULE_STATE_VDEV, &lock_set->g_vdev)) {
			rsi_vdev_release_objects(lock_set);
			return RSI_INCOMPLETE;
		}
	} else if (!find_lock_two_granules(
			rd_addr, GRANULE_STATE_RD, &lock_set->g_rd,
			vdev_addr, GRANULE_STATE_VDEV, &lock_set->g_vdev)) {
		rsi_vdev_release_objects(lock_set);
		return RSI_INCOMPLETE;
	}

	/*
	 * rec+: REC_ENTER
	 * rd+ : REC
	 *
	 * Between the unlock-lock sequence:
	 *
	 * 1. g_rd cannot be destroyed
	 * 2. g_vdev can become a different type of granule
	 * 3. vdev can be destroyed
	 * 4. vdev can change rd ownership
	 * 5. vdev can change parent pdev
	 * 6. vdev_id can map to a different vdev
	 * 7. vdev_id maps to same vdev_addr, but the vdev is created with
	 *    different params from the 'original' vdev
	 * 8. a new <vdev_id, vdev> can be added to the realm (spurious)
	 * 9. an unrelated <vdev_id, vdev> can be removed from the realm (spurious)
	 *
	 * (1) as noted earlier this is due to positive refcount
	 * (2) is protected by granule state match for a successful lock
	 * (3,4,5,6,7) must go through rmi_vdev_destroy(), which would increment the epoch
	 * (8,9) are spurious events but updates the epoch counter
	 *
	 * Note: The epoch counter implemented here is coarse grained (tracks
	 * any and all modifications to the rd vdev map) and cannot easily
	 * distinguish between an attack (7) and spurious event (8,9).
	 * By having a more fine-grained per-mapping epoch counter, we could
	 * track changes to a particular <vdev_id, vdev> mapping.
	 *
	 * Also a vdev_id from realm is inherently racy because the host can
	 * remove/replace the device at its will without realm involvmement.
	 * But when the realm has attested and validated the device
	 * (rsi_validate_mapping and rsi_enable_dma) and the host removes or
	 * replaces the device, the device consent is removed i.e., device-memory
	 * gets unmapped and device dma/p2p consents are removed. By comparing
	 * the lock_nonce, the realm can also detect the replacement scenario.
	 */
	lock_set->rd = buffer_granule_map(lock_set->g_rd, SLOT_RD);
	if (claim_pdev) {
		lock_set->pd = buffer_granule_map(lock_set->g_pdev, SLOT_PDEV);
		assert(lock_set->pd != NULL);
	}
	lock_set->vd = buffer_granule_map(lock_set->g_vdev, SLOT_VDEV);
	assert((lock_set->rd != NULL) && (lock_set->vd != NULL));

	if (get_rd_obj_map_epoch_locked(lock_set->rd) != epoch) {
		rsi_vdev_release_objects(lock_set);
		/*
		 * Any of above cases (3-9) could have happened. Returning
		 * ERROR_INPUT here for the spurious cases is wrong. Hence
		 * safer option is to retry the lock. If the vdev_id was removed,
		 * a subsequent lookup would fail returning ERROR_INPUT.
		 */
		return RSI_INCOMPLETE;
	}

	/*
	 * vdev and rd are locked, and the objects haven't changed in reacquire
	 */

	/* redundant safety checks */
	assert(rsi_vdev_matches_map(lock_set->rd, vdev_id, lock_set->g_vdev));
	assert(lock_set->vd->g_rd == lock_set->g_rd);
	assert(lock_set->vd->id == vdev_id);
	assert(!claim_pdev || (lock_set->vd->g_pdev == lock_set->g_pdev));

	return RSI_SUCCESS;
}
