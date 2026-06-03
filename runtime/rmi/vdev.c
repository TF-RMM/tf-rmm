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
#include <dev_granule.h>
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

static bool rmi_addr_ranges_valid(struct rmi_address_range *addr_range,
				  unsigned long addr_range_cnt)
{
	unsigned long last_top = 0U;
	unsigned long i;

	for (i = 0; i < addr_range_cnt; ++i) {

		if ((addr_range[i].base >= addr_range[i].top) ||
		    (addr_range[i].base < last_top)) {
			return false;
		}
		last_top = addr_range[i].top;
	}
	return true;
}

static bool rmi_addr_ranges_overlap(const struct rmi_address_range *range1,
				    unsigned long range1_cnt,
				    const struct rmi_address_range *range2,
				    unsigned long range2_cnt)
{
	unsigned long range1_idx = 0U;
	unsigned long range2_idx = 0U;

	/*
	 * We can assume that the ranges are sorted, because that is already
	 * checked by rmi_addr_ranges_valid which is called early in
	 * smc_vdev_create.
	 */
	while ((range1_idx < range1_cnt) && (range2_idx < range2_cnt)) {
		if ((range1[range1_idx].base < range2[range2_idx].top) &&
		    (range2[range2_idx].base < range1[range1_idx].top)) {
			return true;
		}

		if (range1[range1_idx].top <= range2[range2_idx].base) {
			range1_idx++;
		} else {
			range2_idx++;
		}
	}

	return false;
}

/*
 * Return the number of aux pages allocated to cover this PDEV's VDEV slot
 * capacity.
 */
static size_t pdev_vdev_ranges_allocated_page_count(const struct pdev *pd)
{
	return (size_t)PDEV_VDEV_RANGE_AUX_COUNT_FROM_SLOT_COUNT(pd->max_num_vdevs);
}

static size_t pdev_vdev_ranges_count_on_page(const struct pdev *pd, size_t page_idx)
{
	size_t slot_base;
	size_t slot_count;

	slot_base = page_idx * VDEV_RANGE_SLOTS_PER_GRANULE;
	assert(slot_base < (size_t)pd->max_num_vdevs);

	slot_count = (size_t)pd->max_num_vdevs - slot_base;

	return min(slot_count, (size_t)VDEV_RANGE_SLOTS_PER_GRANULE);
}

static struct pdev_vdev_range_slot *pdev_vdev_ranges_map_page(const struct pdev *pd,
							      size_t page_idx)
{
	assert(page_idx < pdev_vdev_ranges_allocated_page_count(pd));
	assert(page_idx < ARRAY_SIZE(pd->g_vdevs_ranges_aux));
	assert(pd->g_vdevs_ranges_aux[page_idx] != NULL);

	return buffer_granule_map(pd->g_vdevs_ranges_aux[page_idx],
				  SLOT_PDEV_VDEV_RANGE);
}

static struct pdev_vdev_range_slot *pdev_vdev_range_slot_map(const struct pdev *pd,
							     uint32_t slot_idx,
							     struct pdev_vdev_range_slot **slots)
{
	const size_t page_idx = slot_idx / VDEV_RANGE_SLOTS_PER_GRANULE;
	const size_t page_slot_idx = slot_idx % VDEV_RANGE_SLOTS_PER_GRANULE;

	assert(slot_idx < pd->max_num_vdevs);
	assert(slots != NULL);

	*slots = pdev_vdev_ranges_map_page(pd, page_idx);
	assert(*slots != NULL);

	return &(*slots)[page_slot_idx];
}

static bool pdev_vdev_ranges_on_a_page_overlap(const struct pdev *pd,
					       size_t page_idx,
					       const struct rmi_address_range *addr_range,
					       unsigned long addr_range_cnt)
{
	struct pdev_vdev_range_slot *slots;
	const size_t slot_count = pdev_vdev_ranges_count_on_page(pd, page_idx);
	bool overlap = false;

	slots = pdev_vdev_ranges_map_page(pd, page_idx);
	assert(slots != NULL);

	for (size_t i = 0U; i < slot_count; ++i) {
		const struct pdev_vdev_range_slot *slot = &slots[i];

		if (!slot->active) {
			continue;
		}

		if (rmi_addr_ranges_overlap(slot->addr_range, slot->num_addr_range,
					    addr_range, addr_range_cnt)) {
			overlap = true;
			break;
		}
	}

	buffer_unmap(slots);

	return overlap;
}

/*
 * Check whether the address range specified by a VDEV_CREATE overlaps the
 * address range of any existing VDEV of this PDEV.
 * Note that the VDEV state is not considered when checking overlap, which means
 * VDEVs in error state are checked as well. The ranges of a VDEV are only
 * cleared from PDEV in case of VDEV_DESTROY.
 */
static bool pdev_vdev_ranges_overlap(const struct pdev *pd,
				     const struct rmi_address_range *addr_range,
				     unsigned long addr_range_cnt)
{
	const size_t page_count = pdev_vdev_ranges_allocated_page_count(pd);

	assert(page_count <= ARRAY_SIZE(pd->g_vdevs_ranges_aux));
	for (size_t page_idx = 0U; page_idx < page_count; ++page_idx) {
		if (pdev_vdev_ranges_on_a_page_overlap(pd, page_idx,
						       addr_range,
						       addr_range_cnt)) {
			return true;
		}
	}

	return false;
}

static uint32_t pdev_find_free_vdev_slot(const struct pdev *pd)
{
	const size_t page_count = pdev_vdev_ranges_allocated_page_count(pd);

	assert(page_count <= ARRAY_SIZE(pd->g_vdevs_ranges_aux));
	for (size_t page_idx = 0U; page_idx < page_count; ++page_idx) {
		struct pdev_vdev_range_slot *slots;
		const size_t slot_count = pdev_vdev_ranges_count_on_page(pd, page_idx);

		slots = pdev_vdev_ranges_map_page(pd, page_idx);
		assert(slots != NULL);

		for (size_t i = 0U; i < slot_count; ++i) {
			if (!slots[i].active) {
				buffer_unmap(slots);
				return (uint32_t)((page_idx * VDEV_RANGE_SLOTS_PER_GRANULE) + i);
			}
		}

		buffer_unmap(slots);
	}

	return PDEV_VDEV_SLOT_INVALID;
}

static void pdev_set_vdev_ranges(struct pdev *pd, uint32_t slot_idx,
				 const struct rmi_address_range *addr_range,
				 unsigned long addr_range_cnt)
{
	struct pdev_vdev_range_slot *slots;
	struct pdev_vdev_range_slot *slot;

	assert(slot_idx < pd->max_num_vdevs);
	assert(addr_range_cnt <= RMI_VDEV_PARAMS_ADDR_RANGE_MAX);

	slot = pdev_vdev_range_slot_map(pd, slot_idx, &slots);
	slot->num_addr_range = addr_range_cnt;
	slot->active = true;
	(void)memcpy(slot->addr_range, addr_range,
		     addr_range_cnt * sizeof(addr_range[0]));
	buffer_unmap(slots);
}

static void pdev_clear_vdev_ranges(struct pdev *pd, uint32_t slot_idx)
{
	struct pdev_vdev_range_slot *slots;
	struct pdev_vdev_range_slot *slot;

	assert(slot_idx < pd->max_num_vdevs);

	slot = pdev_vdev_range_slot_map(pd, slot_idx, &slots);
	slot->active = false;
	slot->num_addr_range = 0U;
	(void)memset(slot->addr_range, 0, sizeof(slot->addr_range));
	buffer_unmap(slots);
}

static bool pdev_vdev_range_slot_is_active(const struct pdev *pd, uint32_t slot_idx)
{
	struct pdev_vdev_range_slot *slots;
	struct pdev_vdev_range_slot *slot;
	bool active;

	assert(slot_idx < pd->max_num_vdevs);

	slot = pdev_vdev_range_slot_map(pd, slot_idx, &slots);
	active = slot->active;
	buffer_unmap(slots);

	return active;
}

/*
 * ONLY FOR TESTING PURPOSES
 * Expose the PDEV VDEV-range slot helpers so runtime unit tests can exercise
 * multi-page slot storage without going through the full DA object flows.
 */
/* coverity[misra_c_2012_rule_8_4_violation:SUPPRESS] */
void vdev_test_pdev_set_vdev_ranges(struct pdev *pd, uint32_t slot_idx,
				    const struct rmi_address_range *addr_range,
				    unsigned long addr_range_cnt)
{
	pdev_set_vdev_ranges(pd, slot_idx, addr_range, addr_range_cnt);
}

/* coverity[misra_c_2012_rule_8_4_violation:SUPPRESS] */
void vdev_test_pdev_clear_vdev_ranges(struct pdev *pd, uint32_t slot_idx)
{
	pdev_clear_vdev_ranges(pd, slot_idx);
}

/* coverity[misra_c_2012_rule_8_4_violation:SUPPRESS] */
bool vdev_test_pdev_vdev_range_slot_is_active(const struct pdev *pd,
					      uint32_t slot_idx)
{
	return pdev_vdev_range_slot_is_active(pd, slot_idx);
}

/* coverity[misra_c_2012_rule_8_4_violation:SUPPRESS] */
uint32_t vdev_test_pdev_find_free_vdev_slot(const struct pdev *pd)
{
	return pdev_find_free_vdev_slot(pd);
}

/* coverity[misra_c_2012_rule_8_4_violation:SUPPRESS] */
bool vdev_test_pdev_vdev_ranges_overlap(
	const struct pdev *pd,
	const struct rmi_address_range *addr_range,
	unsigned long addr_range_cnt)
{
	return pdev_vdev_ranges_overlap(pd, addr_range, addr_range_cnt);
}

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

	if ((vdev_params->flags != 0U) ||
	    (vdev_params->num_addr_range > RMI_VDEV_PARAMS_ADDR_RANGE_MAX) ||
	    !rmi_addr_ranges_valid(vdev_params->addr_range, vdev_params->num_addr_range)) {
		return RMI_ERROR_INPUT;
	}

	/* TODO: Verify VSMMU related parameters */

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
	struct granule *g_vdev = NULL;
	struct rd *rd;
	struct pdev *pd;
	struct vdev *vd;
	struct s2tt_context *plane_0_s2_context;
	struct smmu_stg2_config s2_cfg;
	unsigned int sid, smmu_idx;
	unsigned long rc;
	struct pdev_stream *stream;
	uint32_t vdev_slot;

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

	rd = buffer_granule_map(g_rd, SLOT_RD);
	assert(rd != NULL);

	if (!rd->da_enabled) {
		rc = RMI_ERROR_REALM;
		goto out_unmap_rd;
	}

	pd = buffer_granule_map(g_pdev, SLOT_PDEV);
	assert(pd != NULL);

	if ((PDEV_CATEGORY(pd) != RMI_PDEV_ENDPOINT_ACCEL_OFF_CHIP) &&
	    (PDEV_CATEGORY(pd) != RMI_PDEV_ENDPOINT_ACCEL_ON_CHIP)) {
		rc = RMI_ERROR_DEVICE;
		goto out_unmap_pd;
	}

	if ((pd->rmi_state != RMI_PDEV_STATE_READY) ||
	    (pd->max_num_vdevs == pd->num_vdevs)) {
		rc = RMI_ERROR_DEVICE;
		goto out_unmap_pd;
	}

	if (pdev_vdev_ranges_overlap(pd, vdev_params.addr_range,
				     vdev_params.num_addr_range)) {
		rc = RMI_ERROR_INPUT;
		goto out_unmap_pd;
	}

	vdev_slot = pdev_find_free_vdev_slot(pd);
	if (vdev_slot == PDEV_VDEV_SLOT_INVALID) {
		rc = RMI_ERROR_DEVICE;
		goto out_unmap_pd;
	}

	stream = pdev_stream_granules_lock_map(pd->g_stream_aux, RMI_PDEV_STREAM_NCOH);
	assert(stream != NULL);

	if (!stream->taken ||
	    (stream->state != PDEV_STREAM_CONNECTED)) {
		rc = RMI_ERROR_DEVICE;
		goto out_unmap_stream;
	}

	/* Lock vdev granule and map it */
	g_vdev = find_lock_granule(vdev_addr, GRANULE_STATE_DELEGATED);
	if (g_vdev == NULL) {
		rc = RMI_ERROR_INPUT;
		goto out_unmap_stream;
	}

	vd = buffer_granule_map_zeroed(g_vdev, SLOT_VDEV);
	assert(vd != NULL);

	plane_0_s2_context = plane_to_s2_context(rd, PLANE_0_ID);

	s2_cfg.s2ttb = granule_addr(plane_0_s2_context->g_rtt) & MASK(TTBRx_EL2_BADDR);
	s2_cfg.vtcr = realm_vtcr(rd);
	s2_cfg.vmid = plane_0_s2_context->vmid;
	s2_cfg.mecid = plane_0_s2_context->mecid;

	if (smmuv3_configure_stream(pd->dev.ecam_addr,
				   (unsigned int)vdev_params.tdi_id,
				   &s2_cfg, &sid, &smmu_idx) != 0) {
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

	vd->sid = sid;
	vd->smmu_idx = smmu_idx;

	vd->num_addr_range = vdev_params.num_addr_range;
	(void)memcpy(vd->addr_range,
		     vdev_params.addr_range,
		     vdev_params.num_addr_range * sizeof(vdev_params.addr_range[0]));
	vd->pdev_slot = vdev_slot;

	/* Update Realm */
	rd_vdev_refcount_inc(rd);

	/* Update PDEV */
	pdev_set_vdev_ranges(pd, vdev_slot, vdev_params.addr_range,
			     vdev_params.num_addr_range);
	pd->num_vdevs++;

out_unmap_vd:
	buffer_unmap(vd);
out_unmap_stream:
	pdev_stream_granules_unmap_unlock(pd->g_stream_aux, stream, RMI_PDEV_STREAM_NCOH);
out_unmap_pd:
	buffer_unmap(pd);
out_unmap_rd:
	buffer_unmap(rd);

	if (rc == RMI_SUCCESS) {
		assert(g_vdev != NULL);
		granule_unlock_transition(g_vdev, GRANULE_STATE_VDEV);
	} else if (g_vdev != NULL) {
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
	if ((rec->pending_op != REC_PENDING_VDEV_REQUEST)) {
		rmi_rc = RMI_ERROR_INPUT;
		goto out_unmap_vdev;
	}

	/* Check the Realm owner and the Device ID of the REC and VDEV */
	if ((rec->realm_info.g_rd != vd->g_rd) || (rec->vdev.vdev_id != vd->id)) {
		rmi_rc = RMI_ERROR_INPUT;
		goto out_unmap_vdev;
	}

	if (vd->comm_state != DEV_COMM_IDLE) {
		rmi_rc = RMI_ERROR_DEVICE;
		goto out_unmap_vdev;
	}

	rec_update_pending_op(rec, REC_PENDING_VDEV_COMPLETE);
	rec->vdev.vdev_addr = vdev_addr;
	rmi_rc = RMI_SUCCESS;

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
		case VDEV_OP_KEY_REFRESH:
			vd->rmi_state = RMI_VDEV_STATE_KEY_PURGE;
			break;
		case VDEV_OP_KEY_PURGE:
			vd->rmi_state = RMI_VDEV_STATE_UNLOCKED;
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
 * rd_addr	- PA of RD
 * pdev_addr	- PA of the PDEV
 * vdev_addr	- PA of the VDEV
 */
unsigned long smc_vdev_abort(unsigned long rd_addr,
			     unsigned long pdev_addr,
			     unsigned long vdev_addr)
{
	int rc __unused;
	struct granule *g_rd;
	struct granule *g_pdev;
	struct granule *g_vdev;
	void *aux_mapped_addr;
	unsigned long smc_rc;
	struct pdev *pd;
	struct vdev *vd;

	if (!is_rmi_feat_da_enabled()) {
		return SMC_NOT_SUPPORTED;
	}

	if ((!GRANULE_ALIGNED(rd_addr)) ||
	    (!GRANULE_ALIGNED(pdev_addr)) ||
	    (!GRANULE_ALIGNED(vdev_addr))) {
		return RMI_ERROR_INPUT;
	}

	/*
	 * RD is not used by the current implementation, but still check
	 * according to spec
	 */
	g_rd = find_granule(rd_addr);
	if ((g_rd == NULL) ||
	    (granule_unlocked_state(g_rd) != GRANULE_STATE_RD)) {
		return RMI_ERROR_INPUT;
	}

	g_pdev = find_lock_granule(pdev_addr, GRANULE_STATE_PDEV);
	if (g_pdev == NULL) {
		return RMI_ERROR_INPUT;
	}

	pd = buffer_granule_map(g_pdev, SLOT_PDEV);
	assert(pd != NULL);

	g_vdev = find_lock_granule(vdev_addr, GRANULE_STATE_VDEV);
	if (g_vdev == NULL) {
		smc_rc = RMI_ERROR_INPUT;
		goto out_pdev_buf_unmap;
	}

	vd = buffer_granule_map(g_vdev, SLOT_VDEV);
	assert(vd != NULL);

	if (vd->comm_state == DEV_COMM_IDLE) {
		smc_rc = RMI_ERROR_DEVICE;
		goto out_vdev_buf_unmap;
	}

	if ((vd->g_rd != g_rd) || (vd->g_pdev != g_pdev)) {
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
	aux_mapped_addr = buffer_pdev_app_aux_map(pd->g_app_aux, pd->num_app_aux);
	assert(aux_mapped_addr != NULL);

	/*
	 * This will resume the blocked CMA SPDM command and the recv callback
	 * handler will return error and abort the command.
	 */
	rc = dev_assign_abort_app_operation(&pd->da_app_data);
	assert(rc == 0);

	/* Unmap all PDEV aux granules */
	buffer_pdev_app_aux_unmap(aux_mapped_addr, pd->num_app_aux);

vdev_reset_state:
	vd->rmi_state = RMI_VDEV_STATE_ERROR;
	vd->comm_state = DEV_COMM_IDLE;
	smc_rc = RMI_SUCCESS;

out_vdev_buf_unmap:
	buffer_unmap(vd);
	granule_unlock(g_vdev);
out_pdev_buf_unmap:
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
	uint32_t vdev_slot;

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
		smc_rc = RMI_ERROR_DEVICE;
		goto out_err_input;
	}

	if ((vd->rmi_state != RMI_VDEV_STATE_NEW) &&
	    (vd->rmi_state != RMI_VDEV_STATE_UNLOCKED)) {
		smc_rc = RMI_ERROR_DEVICE;
		goto out_err_input;
	}

	/*
	 * The VDEV state machine enforces DMA-off before reaching a destroyable
	 * state. In particular, smc_vdev_unlock() disables the STE before the
	 * VDEV can transition to RMI_VDEV_STATE_UNLOCKED.
	 */
	assert(vd->dma_state == RMI_VDEV_DMA_DISABLED);

	vdev_slot = vd->pdev_slot;
	assert((vdev_slot < pd->max_num_vdevs) &&
	       (pdev_vdev_range_slot_is_active(pd, vdev_slot)));

	if (smmuv3_release_ste(vd->smmu_idx, vd->sid) != 0) {
		smc_rc = RMI_ERROR_DEVICE;
		goto out_err_input;
	}

	/* Update Realm */
	rd_vdev_refcount_dec(rd);

	/* Update PDEV. */
	/*
	 * The ranges of a VDEV are only cleared from a pdev on VDEV_DESTROY.
	 * This is true for VDEVS that are in error state, regardless whether
	 * they got into error state because of a failed VDEV_COMMUNICATE or a
	 * VDEV_ABORT. To destroy a VDEV in error state, VDEV_UNLOCK must be
	 * called on it before VDEV_DESTROY.
	 */
	pdev_clear_vdev_ranges(pd, vdev_slot);
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
	struct rmi_vdev_measure_params *measurement_params)
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

	smc_rc = validate_vdev_get_measurements_params(params_addr, &measurement_params);
	if (smc_rc != RMI_SUCCESS) {
		goto out_err_input;
	}

	spdm_meas_params = &vd->op_params.meas_params;

	(void)memset(spdm_meas_params, 0, sizeof(struct dev_meas_params));

	if (EXTRACT(RMI_VDEV_MEASURE_FLAGS_RAW, measurement_params.flags) != 0U) {
		spdm_meas_params->raw = true;
	} else {
		spdm_meas_params->raw = false;
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

void smc_vdev_unlock(unsigned long rd_addr, unsigned long pdev_addr,
		     unsigned long vdev_addr, struct smc_result *res)
{
	struct granule *g_rd = NULL;
	struct granule *g_pdev = NULL;
	struct granule *g_vdev = NULL;
	struct dev_tdisp_params *tdisp_params;
	struct vdev *vd = NULL;

	if (!is_rmi_feat_da_enabled()) {
		res->x[0] = SMC_NOT_SUPPORTED;
		res->x[1] = 0U;
		return;
	}

	if (!GRANULE_ALIGNED(rd_addr) || !GRANULE_ALIGNED(pdev_addr) ||
	    !GRANULE_ALIGNED(vdev_addr)) {
		res->x[0] = RMI_ERROR_INPUT;
		res->x[1] = 0U;
		return;
	}

	if (!find_lock_two_granules(rd_addr, GRANULE_STATE_RD, &g_rd,
				    pdev_addr, GRANULE_STATE_PDEV, &g_pdev)) {
		res->x[0] = RMI_ERROR_INPUT;
		res->x[1] = 0U;
		return;
	}

	g_vdev = find_lock_granule(vdev_addr, GRANULE_STATE_VDEV);
	if (g_vdev == NULL) {
		res->x[0] = RMI_ERROR_INPUT;
		res->x[1] = 0U;
		goto out_unlock;
	}

	vd = buffer_granule_map(g_vdev, SLOT_VDEV);
	assert(vd != NULL);

	if ((vd->g_rd != g_rd) ||
	    (vd->g_pdev != g_pdev)) {
		res->x[0] = RMI_ERROR_DEVICE;
		res->x[1] = 0U;
		goto out_unlock;
	}

	if ((vd->rmi_state != RMI_VDEV_STATE_LOCKED) &&
	    (vd->rmi_state != RMI_VDEV_STATE_STARTED) &&
	    (vd->rmi_state != RMI_VDEV_STATE_ERROR)) {
		res->x[0] = RMI_ERROR_DEVICE;
		res->x[1] = 0U;
		goto out_unlock;
	}

	if (vd->comm_state != DEV_COMM_IDLE) {
		ERROR("vd(%p)->comm_state(%u) != DEV_COMM_IDLE\n", (void *)vd, vd->comm_state);
		res->x[0] = RMI_ERROR_DEVICE;
		res->x[1] = 0U;
		goto out_unlock;
	}

	/*
	 * Make sure that no dev granules are mapped in the address ranges of
	 * this VDEV
	 */
	for (unsigned long i = 0U; i < vd->num_addr_range; ++i) {
		unsigned long base = vd->addr_range[i].base;
		unsigned long top = vd->addr_range[i].top;

		for (unsigned long addr = base; addr < top; addr += GRANULE_SIZE) {
			enum dev_coh_type type;
			struct dev_granule *g =
				find_lock_dev_granule(addr, DEV_GRANULE_STATE_MAPPED, &type);

			/*
			 * If the granule is in DEV_GRANULE_STATE_MAPPED state,
			 * then the unlocking of the VDEV cannot be continued
			 */
			if (g != NULL) {
				dev_granule_unlock(g);
				res->x[0] = RMI_ERROR_GRANULE;
				res->x[1] = addr;
				goto out_unlock;
			}
		}
	}

	/*
	 * Disable the STE (CFGI_STE and CMD_SYNC) early on to stop device from
	 * DMAing to realm memory. This is especially important when we
	 * implement the forced-refresh as part of the UNLOCK().
	 */
	if (vd->dma_state == RMI_VDEV_DMA_ENABLED) {
		if (smmuv3_disable_ste(vd->smmu_idx, vd->sid) != 0) {
			res->x[0] = RMI_ERROR_DEVICE;
			res->x[1] = 0U;
			goto out_unlock;
		}
		vd->dma_state = RMI_VDEV_DMA_DISABLED;
	}

	/* Set TDISP parameters */
	tdisp_params = &vd->op_params.tdisp_params;
	(void)memset(tdisp_params, 0, sizeof(struct dev_tdisp_params));
	tdisp_params->tdi_id = (uint32_t)(vd->tdi_id & 0xffffUL);

	vd->op = VDEV_OP_UNLOCK;
	vd->comm_state = DEV_COMM_PENDING;

	res->x[0] = RMI_SUCCESS;
	res->x[1] = 0U;

out_unlock:
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
}
