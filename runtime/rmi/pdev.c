/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <app.h>
#include <arch.h>
#include <arch_features.h>
#include <buffer.h>
#include <debug.h>
#include <dev.h>
#include <dev_assign_app.h>
#include <feature.h>
#include <granule.h>
#include <pcpu_data.h>
#include <rmm_el3_ifc.h>
#include <sizes.h>
#include <smc-handler.h>
#include <smc-rmi.h>
#include <sro_context.h>
#include <string.h>
#include <utils_def.h>

#define RMI_PDEV_FLAGS_VALID_MASK  (MASK(RMI_PDEV_FLAGS_SPDM) | MASK(RMI_PDEV_FLAGS_CATEGORY))
#define PCIE_BDF_VALID_MASK		((unsigned long)UINT16_MAX)

struct pdev_stream_aux {
	struct pdev_stream streams[RMI_PDEV_STREAM_TYPE_COUNT];
};

static inline unsigned long pack_stream_handle(unsigned long pd1_addr,
					       unsigned char stream_type) {
	assert(GRANULE_ALIGNED(pd1_addr));
	assert(stream_type < RMI_PDEV_STREAM_TYPE_COUNT);
	return pd1_addr + stream_type;
}

/* Returns false on unpack failure. Returns true on success. */
static inline bool unpack_stream_handle(unsigned long handle,
					unsigned long *pd1_addr,
					unsigned char *stream_type) {
	unsigned long st;

	st = handle & (~GRANULE_MASK);

	if (st >= RMI_PDEV_STREAM_TYPE_COUNT) {
		return false;
	}

	*pd1_addr = handle & GRANULE_MASK;
	*stream_type = (unsigned char)st;

	return true;
}

struct pdev_stream *pdev_stream_granules_lock_map(struct granule *g_streams,
						  unsigned char stream_type)
{
	struct pdev_stream_aux *stream_aux;

	assert(g_streams != NULL);
	granule_lock(g_streams, GRANULE_STATE_PDEV_AUX);

	stream_aux = buffer_granule_map(g_streams, SLOT_PDEV_STREAM);
	if (stream_aux == NULL) {
		granule_unlock(g_streams);
		return NULL;
	}

	assert(stream_type < RMI_PDEV_STREAM_TYPE_COUNT);

	return &(stream_aux->streams[stream_type]);
}

void pdev_stream_granules_unmap_unlock(struct granule *g_streams,
				       struct pdev_stream *stream,
				       unsigned char stream_type)
{
	struct pdev_stream_aux *stream_aux;
	uintptr_t pdev_streams_addr;

	assert(stream_type < RMI_PDEV_STREAM_TYPE_COUNT);
	assert(stream != NULL);

	pdev_streams_addr = (uintptr_t)stream - (stream_type * sizeof(struct pdev_stream));

	stream_aux = (struct pdev_stream_aux *)(
		pdev_streams_addr - offsetof(struct pdev_stream_aux, streams));

	assert(GRANULE_ALIGNED(stream_aux));

	buffer_unmap(stream_aux);
	granule_unlock(g_streams);
}

static bool pdev_hb_base_is_valid(unsigned long hb_base)
{
	return rmm_el3_ifc_is_ecam_base_valid(hb_base);
}

static bool pdev_pci_id_is_valid(unsigned long hb_base, unsigned long bdf,
				 unsigned long flags)
{
	if ((bdf & ~PCIE_BDF_VALID_MASK) != 0UL) {
		return false;
	}

	if (PDEV_CATEGORY_FROM_FLAGS(flags) == RMI_PDEV_ROOTPORT) {
		return rmm_el3_ifc_is_root_port_id_valid(hb_base, (unsigned int)bdf);
	}

	return rmm_el3_ifc_is_bdf_valid(hb_base, (unsigned int)bdf);
}

static unsigned int pdev_get_max_num_vdevs(unsigned int rid_base,
					   unsigned int rid_top)
{
	return rid_top - rid_base;
}

/*
 * TODO:
 * Check that the device identifier is not equal to the device identifier of
 * another PDEV.
 */
static unsigned long validate_rmi_pdev_params(struct rmi_pdev_params *pd_params)
{
	if ((PDEV_CATEGORY_FROM_FLAGS(pd_params->flags) != RMI_PDEV_ROOTPORT)) {
		if (pd_params->rid_base >= pd_params->rid_top) {
			return RMI_ERROR_INPUT;
		}
		unsigned int max_num_vdevs =
			pdev_get_max_num_vdevs(pd_params->rid_base, pd_params->rid_top);

		if (max_num_vdevs > PDEV_MAX_VDEVS(MAX_VDEVS_ORDER)) {
			return RMI_ERROR_INPUT;
		}

		/* Validate hash algorithm */
		/* coverity[uninit_use:SUPPRESS] */
		if ((pd_params->hash_algo != RMI_HASH_SHA_256) &&
		    (pd_params->hash_algo != RMI_HASH_SHA_512) &&
		    (pd_params->hash_algo != RMI_HASH_SHA_384)) {
			return RMI_ERROR_INPUT;
		}
	}

	if ((pd_params->flags & ~RMI_PDEV_FLAGS_VALID_MASK) != 0U) {
		return RMI_ERROR_INPUT;
	}

	/*
	 * Validate RmiPdevFlags. RMM supports PCIE off-chip device represented
	 */
	/* TODO_ALP17: Check whether [n]coh_addr is checked during mem validate */
	/* TODO_ALP17: Add address range checking if RMI_PDEV_FLAGS_NCOH_ADDR
	 * is set.
	 */
	/*
	 * Only off-chip end point devices are supported for now.
	 * They are expect to be selective trust devices supporting SPDM.
	 * For Rootports we don't have any flag requirements.
	 */
	/* coverity[uninit_use:SUPPRESS] */
	if ((PDEV_CATEGORY_FROM_FLAGS(pd_params->flags) == RMI_PDEV_ENDPOINT_ACCEL_OFF_CHIP)) {
		if ((EXTRACT(RMI_PDEV_FLAGS_SPDM, pd_params->flags) != RMI_PDEV_SPDM_TRUE)) {
			return RMI_ERROR_NOT_SUPPORTED;
		}
	} else if (PDEV_CATEGORY_FROM_FLAGS(pd_params->flags) != RMI_PDEV_ROOTPORT) {
		return RMI_ERROR_NOT_SUPPORTED;
	}

	if (pd_params->routing_id > (unsigned long)(UINT16_MAX)) {
		return RMI_ERROR_INPUT;
	}

	if (!pdev_hb_base_is_valid(pd_params->hb_base) ||
	    !pdev_pci_id_is_valid(pd_params->hb_base, pd_params->pdev_id,
				  pd_params->flags)) {
		return RMI_ERROR_INPUT;
	}

	return RMI_SUCCESS;
}

static unsigned long pdev_get_app_aux_count_from_flags(unsigned long pdev_flags)
{
	(void)pdev_flags;

	/*
	 * The current implementation requires that RMI_PDEV_SPDM_TRUE
	 * is set in the flags.
	 */
	assert(EXTRACT(RMI_PDEV_FLAGS_SPDM, pdev_flags) == RMI_PDEV_SPDM_TRUE);

	/*
	 * Currently, the number of pages required to instantiate an app is
	 * hardcoded in the app header. In this implementation, aux_count
	 * does not depend on the flags set in pdev_flags. The worst case
	 * (i.e., the most granules) is assumed.
	 */
	return app_get_required_granule_count(RMM_DEV_ASSIGN_APP_ID);
}

static unsigned int pdev_get_vdev_range_aux_count(unsigned int max_num_vdevs)
{
	assert(max_num_vdevs <= PDEV_MAX_VDEVS(MAX_VDEVS_ORDER));

	return (unsigned int)PDEV_VDEV_RANGE_AUX_COUNT_FROM_SLOT_COUNT(max_num_vdevs);
}

static unsigned long
pdev_create_continue_rp(unsigned long pdev_addr, struct rmi_pdev_params *pdev_params);

static void pdev_create_continue_ep(unsigned long fid, struct smc_result *res);

/*
 * smc_pdev_create
 *
 * pdev_addr		- PA of the PDEV
 * pdev_params_addr	- PA of PDEV parameters
 */
void smc_pdev_create(unsigned long pdev_addr,
		     unsigned long pdev_params_addr,
		     struct smc_result *res)
{
	struct sro_context *sro;
	struct granule *g_pdev_params;
	struct granule *gr;
	struct rmi_pdev_params pdev_params; /* this consumes 4k of stack */
	bool ns_access_ok;
	unsigned long ret;
	unsigned int max_num_vdevs;

	if (!is_rmi_feat_da_enabled()) {
		res->x[0] = SMC_NOT_SUPPORTED;
		return;
	}

	if (!GRANULE_ALIGNED(pdev_addr) ||
	    !GRANULE_ALIGNED(pdev_params_addr)) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	/* Map and copy PDEV parameters */
	g_pdev_params = find_granule(pdev_params_addr);
	if ((g_pdev_params == NULL) ||
	    (granule_unlocked_state(g_pdev_params) != GRANULE_STATE_NS)) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	ns_access_ok = ns_buffer_read(SLOT_NS, g_pdev_params, 0U,
				      sizeof(struct rmi_pdev_params),
				      &pdev_params);
	if (!ns_access_ok) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	/* cppcheck-suppress knownConditionTrueFalse */
	/* coverity[uninit_use_in_call:SUPPRESS] */
	ret = validate_rmi_pdev_params(&pdev_params);
	if (ret != RMI_SUCCESS) {
		res->x[0] = ret;
		return;
	}

	/* No SRO is needed in case of rootport */
	if ((PDEV_CATEGORY_FROM_FLAGS(pdev_params.flags) == RMI_PDEV_ROOTPORT)) {
		res->x[0] = pdev_create_continue_rp(pdev_addr, &pdev_params);
		return;
	}

	/*
	 * Granules for the app, one page for stream objects associated with
	 * this EP PDEV, and enough pages to store cached VDEV ranges for the
	 * RID span associated with this PDEV. Initiate SRO to get that memory.
	 */
	max_num_vdevs = pdev_get_max_num_vdevs(pdev_params.rid_base,
						 pdev_params.rid_top);
	const size_t aux_count = pdev_get_app_aux_count_from_flags(pdev_params.flags) +
		MAX_PDEV_STREAM_AUX_COUNT +
		pdev_get_vdev_range_aux_count(max_num_vdevs);
	if (aux_count > MAX_PDEV_PARAM_AUX_GRANULES) {
		/*
		 * The PDEV cannot hold enough granules for this configuration.
		 * Increase MAX_PDEV_PARAM_AUX_GRANULES
		 */
		ERROR("PDEV object can hold at most %u aux granules (%lu required)\n",
			MAX_PDEV_PARAM_AUX_GRANULES, aux_count);
		res->x[0] = RMI_ERROR_NOT_SUPPORTED;
		return;
	}

	gr = find_lock_granule(pdev_addr, GRANULE_STATE_DELEGATED);
	if (gr == NULL) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	ret = sro_ctx_reserve(SMC_RMI_PDEV_CREATE, aux_count * GRANULE_SIZE,
			      false, false, SMC_RMI_OP_MEM_DONATE);
	if (ret != RMI_SUCCESS) {
		granule_unlock(gr);
		res->x[0] = ret;
		return;
	}

	sro = my_sro_ctx();
	assert(sro != NULL);


	/*
	 * The first step of PDEV_CREATE will be to request memory for
	 * the aux granules.
	 */
	/* Initialize the sro context for the command */
	sro->pdev_ctx.flags = pdev_params.flags;
	sro->pdev_ctx.hb_base = pdev_params.hb_base;
	sro->pdev_ctx.pdev_id = pdev_params.pdev_id;
	sro->pdev_ctx.routing_id = (uint16_t)pdev_params.routing_id;
	sro->pdev_ctx.id_index = pdev_params.id_index;
	sro->pdev_ctx.rid_base = pdev_params.rid_base;
	sro->pdev_ctx.rid_top = pdev_params.rid_top;
	sro->pdev_ctx.hash_algo = pdev_params.hash_algo;

	granule_unlock_transition(gr, GRANULE_STATE_PARTIAL);

	sro_aux_op_init_donate(sro, res, pdev_addr,
			       aux_count,
			       GRANULE_STATE_PDEV_AUX);
}

static void pdev_create_continue_ep(unsigned long fid, struct smc_result *res)
{
	struct granule *g_pdev;
	struct granule *all_aux_granules[MAX_PDEV_PARAM_AUX_GRANULES];
	uintptr_t *all_aux_granule_pas;
	struct pdev *pd;
	struct sro_pdev_ctx *sro_ctx;
	unsigned long ecam_addr;
	unsigned long bdf;
	struct dev_assign_params dparams;
	unsigned long smc_rc;
	int rc;
	unsigned int num_aux_granules;
	void *aux_mapped_addr;
	struct sro_context *sro = my_sro_ctx();
	unsigned int num_app_aux_granules;
	unsigned int num_vdev_range_aux_granules;
	unsigned int app_aux_start_idx;
	unsigned int max_num_vdevs;

	assert(sro != NULL);
	assert(fid == SMC_RMI_OP_CONTINUE);

	(void)fid;

	/* Ensure all requested aux granules have been transferred */
	assert(sro->aux_op_ctx.total_transferred ==
		sro->aux_op_ctx.requested_aux_granules);

	sro_ctx = &sro->pdev_ctx;
	num_aux_granules = (unsigned int)sro->aux_op_ctx.requested_aux_granules;
	all_aux_granule_pas = sro->aux_op_ctx.aux_granules_pa;
	max_num_vdevs = pdev_get_max_num_vdevs(sro_ctx->rid_base,
						 sro_ctx->rid_top);
	num_vdev_range_aux_granules = pdev_get_vdev_range_aux_count(max_num_vdevs);
	app_aux_start_idx = PDEV_VDEV_RANGES_AUX_GRANULE_IDX +
		num_vdev_range_aux_granules;

	if (num_aux_granules < app_aux_start_idx) {
		smc_rc = RMI_ERROR_INPUT;
		goto out_restore_pdev_aux_granule_state;
	}

	num_app_aux_granules = num_aux_granules - app_aux_start_idx;
	assert(num_app_aux_granules <= ARRAY_SIZE(pd->g_app_aux));

	for (unsigned int i = 0U; i < num_aux_granules; i++) {
		unsigned long addr = all_aux_granule_pas[i];

		all_aux_granules[i] = find_granule(addr);

		/* The granules should have been transitioned during donation */
		assert(all_aux_granules[i] != NULL);
		assert(granule_unlocked_state(all_aux_granules[i]) == GRANULE_STATE_PDEV_AUX);
	}

	/* Lock pdev granule and map it */
	g_pdev = find_lock_granule(sro->aux_op_ctx.obj_addr, GRANULE_STATE_PARTIAL);
	if (g_pdev == NULL) {
		smc_rc = RMI_ERROR_INPUT;
		goto out_restore_pdev_aux_granule_state;
	}

	pd = buffer_granule_map_zeroed(g_pdev, SLOT_PDEV);
	assert(pd != NULL);

	ecam_addr = sro_ctx->hb_base;
	bdf = sro_ctx->pdev_id;

	/* Call init routine to initialize device class specific state */
	dparams.dev_handle = (void *)pd;
	dparams.rmi_hash_algo = sro_ctx->hash_algo;
	dparams.cert_slot_id = (uint8_t)sro_ctx->id_index;
	dparams.bdf = bdf;

	if (PDEV_CATEGORY_FROM_FLAGS(sro_ctx->flags) == RMI_PDEV_ENDPOINT_ACCEL_OFF_CHIP) {
		dparams.has_ide = true;
		dparams.ecam_addr = ecam_addr;
	} else {
		dparams.has_ide = false;
	}

	/* Map and initialise the stream granule */
	/* NOLINTNEXTLINE(clang-analyzer-core.CallAndMessage) */
	aux_mapped_addr = buffer_granule_map_zeroed(
				all_aux_granules[PDEV_STREAM_AUX_GRANULE_IDX],
				SLOT_PDEV_STREAM);
	assert(aux_mapped_addr != NULL);

	buffer_unmap(aux_mapped_addr);

	for (unsigned int i = 0U; i < num_vdev_range_aux_granules; i++) {
		/* NOLINTNEXTLINE(clang-analyzer-core.CallAndMessage) */
		aux_mapped_addr = buffer_granule_map_zeroed(
			all_aux_granules[PDEV_VDEV_RANGES_AUX_GRANULE_IDX + i],
			SLOT_PDEV_VDEV_RANGE);
		assert(aux_mapped_addr != NULL);

		buffer_unmap(aux_mapped_addr);
	}

	/*
	 * Map app aux granules separately from the reserved aux granules so
	 * they occupy SLOT_PDEV_APP_AUX0 and above, matching the VA layout used
	 * during app execution.
	 */
	/* coverity[overrun-buffer-val:SUPPRESS] */
	aux_mapped_addr = buffer_pdev_app_aux_map_zeroed(
				&all_aux_granules[app_aux_start_idx],
				num_app_aux_granules);
	assert(aux_mapped_addr != NULL);

	rc = dev_assign_app_init(&pd->da_app_data,
		&all_aux_granule_pas[app_aux_start_idx],
		num_app_aux_granules,
		aux_mapped_addr,
		&dparams);

	if (rc == DEV_ASSIGN_STATUS_SUCCESS) {
		/* Initialize PDEV */
		pd->da_app_yielded = false;
		pd->op.stream_op_state = STREAM_OP_STATE_NONE;
		pd->g_pdev = g_pdev;
		pd->rmi_state = RMI_PDEV_STATE_NEW;
		pd->op.curr = PDEV_OP_NONE;
		pd->rmi_flags = sro_ctx->flags;
		pd->num_vdevs = 0;
		pd->max_num_vdevs = (uint32_t)max_num_vdevs;
		pd->rmi_hash_algo = sro_ctx->hash_algo;
		pd->num_app_aux = num_app_aux_granules;
		pd->g_stream_aux = all_aux_granules[PDEV_STREAM_AUX_GRANULE_IDX];
		(void)memcpy((void *)pd->g_vdevs_ranges_aux,
			     (void *)(&all_aux_granules[PDEV_VDEV_RANGES_AUX_GRANULE_IDX]),
			     num_vdev_range_aux_granules * sizeof(struct granule *));
		(void)memcpy((void *)pd->g_app_aux,
			     (void *)(&all_aux_granules[app_aux_start_idx]),
			     pd->num_app_aux * sizeof(struct granule *));

		/* Initialize PDEV communication state */
		pd->dev_comm_state = DEV_COMM_PENDING;

		/* Initialize PDEV pcie device */
		pd->dev.bdf = bdf;
		pd->dev.segment_id = sro_ctx->routing_id;
		pd->dev.ecam_addr = ecam_addr;
		pd->dev.cert_slot_id = sro_ctx->id_index;
		pd->dev.rid_base = sro_ctx->rid_base;
		pd->dev.rid_top = sro_ctx->rid_top;

		smc_rc = RMI_SUCCESS;
	} else {
		smc_rc = RMI_ERROR_INPUT;
	}

	buffer_pdev_app_aux_unmap(aux_mapped_addr, num_app_aux_granules);

	/*
	 * Unlock and transit the PDEV granule state to GRANULE_STATE_PARTIAL.
	 */
	buffer_unmap(pd);

	if (smc_rc == RMI_SUCCESS) {
		granule_unlock_transition(g_pdev, GRANULE_STATE_PDEV);
	} else {
		granule_unlock(g_pdev);
	}

out_restore_pdev_aux_granule_state:
	if (smc_rc != RMI_SUCCESS) {
		/*
		 * The command failed, so request the host to reclaim the
		 * donated memory and return.
		 */
		sro_aux_op_start_reclaim(sro, res,
					 sro->aux_op_ctx.obj_addr,
					 false,
					 smc_rc,
					 sro->aux_op_ctx.total_transferred,
					 GRANULE_STATE_PDEV_AUX);
	} else {
		/* Finish the command with SUCCESS */
		res->x[0] = smc_rc;
		assert(res->x[2] == 0UL);
		assert(res->x[1] == 0UL);
	}
}

static unsigned long pdev_create_continue_rp(unsigned long pdev_addr,
					     struct rmi_pdev_params *pdev_params)
{
	struct granule *g_pdev;
	struct pdev *pd;
	unsigned long ecam_addr;
	unsigned long bdf;

	/* Lock pdev granule and map it */
	g_pdev = find_lock_granule(pdev_addr, GRANULE_STATE_DELEGATED);
	if (g_pdev == NULL) {
		return RMI_ERROR_INPUT;
	}

	pd = buffer_granule_map_zeroed(g_pdev, SLOT_PDEV);
	assert(pd != NULL);

	ecam_addr = pdev_params->hb_base;
	bdf = pdev_params->pdev_id;

	/* Initialize PDEV */
	pd->da_app_yielded = false;
	pd->op.stream_op_state = STREAM_OP_STATE_NONE;
	pd->g_pdev = g_pdev;
	pd->rmi_state = RMI_PDEV_STATE_NEW;
	pd->op.curr = PDEV_OP_NONE;
	pd->rmi_flags = pdev_params->flags;
	pd->num_vdevs = 0U;
	pd->max_num_vdevs = 0U;
	pd->rmi_hash_algo = RMI_HASH_SHA_256; /* Not used */

	/* Initialize PDEV communication state */
	pd->dev_comm_state = DEV_COMM_PENDING;

	/* Initialize PDEV pcie device */
	pd->dev.bdf = bdf;
	pd->dev.segment_id = (uint16_t)pdev_params->routing_id;
	pd->dev.ecam_addr = ecam_addr;
	pd->dev.cert_slot_id = pdev_params->id_index;
	pd->dev.rid_base = pdev_params->rid_base;
	pd->dev.rid_top = pdev_params->rid_top;

	/*
	 * Unlock and transit the PDEV granule state to GRANULE_STATE_PDEV.
	 */
	buffer_unmap(pd);
	granule_unlock_transition(g_pdev, GRANULE_STATE_PDEV);

	return RMI_SUCCESS;
}

void pdev_continue_handler(unsigned long fid, struct smc_result *res)
{
	/* List of handlers that can be invoked from here */
	const sro_handle_cb sro_callbacks[] = {
		[SRO_OBJ_MEM_RECLAIM] = sro_obj_memory_reclaim,
		[SRO_OBJ_MEM_DONATE] = sro_obj_memory_donate,
		[SRO_OBJ_CREATE_CONTINUE] = pdev_create_continue_ep,
		[SRO_OBJ_DESTROY_FINISH] = sro_aux_op_reclaim_finish
	};
	struct sro_context *sro = my_sro_ctx();

	assert(sro != NULL);
	assert((size_t)(sro->aux_op_ctx.cb_id) < ARRAY_SIZE(sro_callbacks));

	sro_callbacks[sro->aux_op_ctx.cb_id](fid, res);
}

/* Validate RmiDevCommData.RmiDevCommEnter argument passed by Host */
static unsigned long copyin_and_validate_dev_comm_enter(
				  struct granule *g_dev_comm_data,
				  struct rmi_dev_comm_enter *enter_args,
				  unsigned int dev_comm_state)
{
	struct granule *g_buf;
	bool ns_access_ok;

	assert(g_dev_comm_data != NULL);

	ns_access_ok = ns_buffer_read(SLOT_NS, g_dev_comm_data,
				      RMI_DEV_COMM_ENTER_OFFSET,
				      sizeof(struct rmi_dev_comm_enter),
				      enter_args);
	if (!ns_access_ok) {
		return RMI_ERROR_INPUT;
	}

	if (!GRANULE_ALIGNED(enter_args->req_addr) ||
	    !GRANULE_ALIGNED(enter_args->resp_addr) ||
	    (enter_args->resp_len > GRANULE_SIZE)) {
		return RMI_ERROR_INPUT;
	}

	if ((enter_args->status == RMI_DEV_COMM_ENTER_STATUS_RESPONSE) &&
		(enter_args->resp_len == 0U)) {
		return RMI_ERROR_INPUT;
	}

	/* Check if request and response buffers are in NS PAS */
	g_buf = find_granule(enter_args->req_addr);
	if ((g_buf == NULL) ||
	    (granule_unlocked_state(g_buf) != GRANULE_STATE_NS)) {
		return RMI_ERROR_INPUT;
	}

	g_buf = find_granule(enter_args->resp_addr);
	if ((g_buf == NULL) ||
	    (granule_unlocked_state(g_buf) != GRANULE_STATE_NS)) {
		return RMI_ERROR_INPUT;
	}

	if ((dev_comm_state == DEV_COMM_PENDING) &&
	    (enter_args->status != RMI_DEV_COMM_ENTER_STATUS_NONE)) {
		return RMI_ERROR_DEVICE;
	}
	return RMI_SUCCESS;
}

/*
 * copyout DevCommExitArgs
 */
static unsigned long copyout_dev_comm_exit(struct granule *g_dev_comm_data,
					   struct rmi_dev_comm_exit *exit_args)
{
	bool ns_access_ok;

	assert(g_dev_comm_data != NULL);

	ns_access_ok = ns_buffer_write(SLOT_NS, g_dev_comm_data,
				       RMI_DEV_COMM_EXIT_OFFSET,
				       sizeof(struct rmi_dev_comm_exit),
				       exit_args);
	if (!ns_access_ok) {
		return RMI_ERROR_INPUT;
	}

	return RMI_SUCCESS;
}

static int copy_cached_digest(struct dev_comm_exit_shared *shared_ret,
			      struct dev_obj_digest *comm_digest_ptr)
{
	size_t digest_len = shared_ret->cached_digest.len;

	if ((digest_len == 0U) || (comm_digest_ptr == NULL) ||
	    (digest_len > sizeof(comm_digest_ptr->value))) {
		return DEV_ASSIGN_STATUS_ERROR;
	}

	(void)memcpy(comm_digest_ptr->value, shared_ret->cached_digest.value,
		     digest_len);
	comm_digest_ptr->len = digest_len;

	return DEV_ASSIGN_STATUS_SUCCESS;
}

static int copy_pdev_cached_digest(struct pdev *pdev, struct app_data_cfg *app_data)
{
	struct dev_comm_exit_shared *shared_ret;

	assert(app_data->el2_shared_page != NULL);
	shared_ret = app_data->el2_shared_page;

	if (shared_ret->cached_digest_type == CACHE_TYPE_VCA) {
		return copy_cached_digest(shared_ret, &(pdev->vca_digest));
	} else if (shared_ret->cached_digest_type == CACHE_TYPE_CERT) {
		return copy_cached_digest(shared_ret, &(pdev->cert_digest));
	}
	assert(shared_ret->cached_digest_type == CACHE_TYPE_NONE);
	return DEV_ASSIGN_STATUS_SUCCESS;
}

static int copy_vdev_cached_digest(struct vdev *vdev, struct app_data_cfg *app_data)
{
	struct dev_comm_exit_shared *shared_ret;

	assert(app_data->el2_shared_page != NULL);
	shared_ret = app_data->el2_shared_page;

	if (shared_ret->cached_digest_type == CACHE_TYPE_MEAS) {
		return copy_cached_digest(shared_ret, &(vdev->meas_digest));
	} else if (shared_ret->cached_digest_type == CACHE_TYPE_INTERFACE_REPORT) {
		return copy_cached_digest(shared_ret, &(vdev->ifc_report_digest));
	}
	assert(shared_ret->cached_digest_type == CACHE_TYPE_NONE);
	return DEV_ASSIGN_STATUS_SUCCESS;
}


static int pdev_dispatch_cmd_ready_rp(struct pdev *pd,
	struct rmi_dev_comm_enter *enter_args, struct rmi_dev_comm_exit *exit_args)
{
	(void)enter_args;

	/*
	 * Assert that we have an active stream operation in progress (not NONE
	 * or already RP_CONNECTED).
	 */
	assert((pd->op.stream_op_state != STREAM_OP_STATE_NONE) &&
	       (pd->op.stream_op_state != STREAM_OP_STATE_RP_CONNECTED));

	if (pd->op.stream_op_state == STREAM_OP_STATE_START) {
		/*
		 * RP_PDEV is first, but nothing to do so set ready, and wait
		 * for EP_PDEV.
		 */
		pd->op.stream_op_state = STREAM_OP_STATE_RP_READY;
		exit_args->flags |= RMI_DEV_COMM_EXIT_FLAGS_STREAM_WAIT_BIT;
		return DEV_ASSIGN_STATUS_COMM_BLOCKED_NO_APP_YIELD;
	} else if (pd->op.stream_op_state == STREAM_OP_STATE_RP_READY) {
		/* If RP_PDEV is ready, wait for EP_PDEV. */
		exit_args->flags |= RMI_DEV_COMM_EXIT_FLAGS_STREAM_WAIT_BIT;
		return DEV_ASSIGN_STATUS_COMM_BLOCKED_NO_APP_YIELD;
	} else if (pd->op.stream_op_state == STREAM_OP_STATE_EP_READY) {
		/*
		 * If EP_PDEV is ready, return success to allow the RP_PDEV op
		 * change to PDEV_OP_STREAM_COMPLETE.
		 */
		pd->op.stream_op_state = STREAM_OP_STATE_RP_CONNECTED;
		return DEV_ASSIGN_STATUS_SUCCESS;
	}

	assert(false);
	return DEV_ASSIGN_STATUS_ERROR;
}

static int pdev_dispatch_cmd_ready_ep(struct pdev *pd, struct rmi_dev_comm_enter *enter_args,
		struct rmi_dev_comm_exit *exit_args)
{
	/* Following are not possible EP_PDEV comm_state should be idle */
	assert((pd->op.stream_op_state != STREAM_OP_STATE_NONE));

	if ((pd->op.stream_op_state == STREAM_OP_STATE_START) ||
	    (pd->op.stream_op_state == STREAM_OP_STATE_EP_READY)) {
		/* wait for RP_PDEV to be ready/complete. */
		(void)memset(exit_args, 0, sizeof(*exit_args));
		exit_args->flags |= RMI_DEV_COMM_EXIT_FLAGS_STREAM_WAIT_BIT;
		return DEV_ASSIGN_STATUS_COMM_BLOCKED_NO_APP_YIELD;
	}

	if (pd->op.stream_op_state == STREAM_OP_STATE_RP_READY) {
		if (pd->op.curr == PDEV_OP_CONNECT) {
			return dev_assign_dev_communicate(&pd->da_app_data, enter_args,
				exit_args, NULL, NULL,
				DEVICE_ASSIGN_APP_FUNC_ID_IDE_SETUP);
		} else if (pd->op.curr == PDEV_OP_DISCONNECT) {
			return dev_assign_dev_communicate(&pd->da_app_data, enter_args,
				exit_args, NULL, NULL,
				DEVICE_ASSIGN_APP_FUNC_ID_IDE_DISCONNECT);
		} else if (pd->op.curr == PDEV_OP_KEY_REFRESH) {
			return dev_assign_dev_communicate(&pd->da_app_data, enter_args,
				exit_args, NULL, NULL,
				DEVICE_ASSIGN_APP_FUNC_ID_IDE_REFRESH);
		}
		assert(false);
	}

	if (pd->op.stream_op_state == STREAM_OP_STATE_RP_CONNECTED) {
		/*
		 * If RP_PDEV is complete, return success to allow the EP_PDEV
		 * op change to PDEV_OP_STREAM_COMPLETE.
		 */
		(void)memset(exit_args, 0, sizeof(*exit_args));
		return DEV_ASSIGN_STATUS_SUCCESS;
	}

	assert(false);
	return DEV_ASSIGN_STATUS_ERROR;
}

static int pdev_dispatch_cmd_ep(struct pdev *pd, struct rmi_dev_comm_enter *enter_args,
		struct rmi_dev_comm_exit *exit_args)
{
	int rc;
	bool copy_cached_digest_if_any = true;

	app_map_shared_page(&pd->da_app_data);

	if (pd->da_app_yielded) {
		rc = dev_assign_dev_communicate(&pd->da_app_data, enter_args,
			exit_args, NULL, NULL, DEVICE_ASSIGN_APP_FUNC_ID_RESUME);
		/* Make the pdev stream_op_state step to
		 * STREAM_OP_STATE_EP_READY once the app run is finished for
		 * EP_PDEV. (This code only runs for the EP PDEV for now, as the
		 * RP_PDEV doesn't call the DA app.)
		 */
		if ((rc == DEV_ASSIGN_STATUS_SUCCESS) &&
		    (pd->rmi_state == RMI_PDEV_STATE_READY) &&
		    (pd->op.curr != PDEV_OP_NONE) &&
		    (pd->op.stream_op_state == STREAM_OP_STATE_RP_READY)) {
			exit_args->flags |= RMI_DEV_COMM_EXIT_FLAGS_STREAM_WAIT_BIT;
			rc = DEV_ASSIGN_STATUS_COMM_BLOCKED_NO_APP_YIELD;
			pd->op.stream_op_state = STREAM_OP_STATE_EP_READY;
		}
		goto out_handle_app_ret;
	}

	if (pd->op.curr == PDEV_OP_STOP) {
		rc = dev_assign_dev_communicate(&pd->da_app_data, enter_args,
			exit_args, NULL, NULL,
			DEVICE_ASSIGN_APP_FUNC_ID_STOP_CONNECTION);
		goto out_handle_app_ret;

	}

	switch (pd->rmi_state) {
	case RMI_PDEV_STATE_NEW:
		rc = dev_assign_dev_communicate(&pd->da_app_data, enter_args,
			exit_args, NULL, NULL,
			DEVICE_ASSIGN_APP_FUNC_ID_CONNECT_INIT);
		break;
	case RMI_PDEV_STATE_HAS_KEY:
		rc = dev_assign_dev_communicate(&pd->da_app_data, enter_args,
			exit_args, NULL, NULL,
			DEVICE_ASSIGN_APP_FUNC_ID_SECURE_SESSION);
		break;
	case RMI_PDEV_STATE_READY:
		rc = pdev_dispatch_cmd_ready_ep(pd, enter_args, exit_args);
		copy_cached_digest_if_any = false;
		break;
	default:
		assert(false);
		rc = -1;
	}

out_handle_app_ret:
	if (rc == DEV_ASSIGN_STATUS_ERROR) {
		goto out;
	}

	pd->da_app_yielded = rc == DEV_ASSIGN_STATUS_COMM_BLOCKED_APP_YIELD;
	if (copy_cached_digest_if_any &&
	    (copy_pdev_cached_digest(pd, &pd->da_app_data) != DEV_ASSIGN_STATUS_SUCCESS)) {
		rc = DEV_ASSIGN_STATUS_ERROR;
	}

out:
	app_unmap_shared_page(&pd->da_app_data);
	return rc;
}

static int pdev_dispatch_cmd_rp(struct pdev *pd, struct rmi_dev_comm_enter *enter_args,
		struct rmi_dev_comm_exit *exit_args)
{
	(void)memset(exit_args, 0, sizeof(*exit_args));

	if (pd->op.curr == PDEV_OP_STOP) {
		/* Nothing to do in this case. */
		return DEV_ASSIGN_STATUS_SUCCESS;
	}

	if (pd->rmi_state == RMI_PDEV_STATE_READY) {
		return pdev_dispatch_cmd_ready_rp(pd, enter_args, exit_args);
	}

	assert(pd->rmi_state == RMI_PDEV_STATE_NEW);
	return DEV_ASSIGN_STATUS_SUCCESS;
}

static int pdev_dispatch_cmd(struct pdev *pd, struct rmi_dev_comm_enter *enter_args,
		struct rmi_dev_comm_exit *exit_args)
{
	if (PDEV_CATEGORY(pd) == RMI_PDEV_ROOTPORT) {
		return pdev_dispatch_cmd_rp(pd, enter_args, exit_args);
	}
	return pdev_dispatch_cmd_ep(pd, enter_args, exit_args);
}

/* Dispatch a command to VDEV based on the VDEV state */
static int vdev_dispatch_cmd(struct pdev *pd, struct vdev *vd,
	struct rmi_dev_comm_enter *enter_args,
	struct rmi_dev_comm_exit *exit_args)
{
	int rc;
	struct dev_meas_params *meas_params_ptr = NULL;
	struct dev_tdisp_params *tdisp_params_ptr;

	if (vd->op == VDEV_OP_GET_MEAS) {
		meas_params_ptr = &vd->op_params.meas_params;
	} else {
		meas_params_ptr = NULL;
	}

	if ((vd->op == VDEV_OP_LOCK) ||
	    (vd->op == VDEV_OP_GET_REPORT) ||
	    (vd->op == VDEV_OP_START) ||
	    (vd->op == VDEV_OP_UNLOCK)) {
		tdisp_params_ptr = &vd->op_params.tdisp_params;
	} else {
		tdisp_params_ptr = NULL;
	}

	app_map_shared_page(&pd->da_app_data);

	if (vd->comm_state == DEV_COMM_ACTIVE) {
		rc = dev_assign_dev_communicate(&pd->da_app_data, enter_args, exit_args,
			tdisp_params_ptr, meas_params_ptr,
			DEVICE_ASSIGN_APP_FUNC_ID_RESUME);
		if (rc == DEV_ASSIGN_STATUS_ERROR) {
			goto out;
		}
		if (copy_vdev_cached_digest(vd, &pd->da_app_data) != DEV_ASSIGN_STATUS_SUCCESS) {
			rc = DEV_ASSIGN_STATUS_ERROR;
		}
		goto out;
	}

	switch (vd->op) {
	case VDEV_OP_GET_MEAS:
		/*
		 * In this VDEV op, the device measurement is retrieved and its
		 * hash needs to be calculated during device communication
		 */
		rc = dev_assign_dev_communicate(&pd->da_app_data, enter_args, exit_args,
			tdisp_params_ptr, meas_params_ptr,
			DEVICE_ASSIGN_APP_FUNC_ID_GET_MEASUREMENTS);
		break;
	case VDEV_OP_LOCK:
		rc = dev_assign_dev_communicate(&pd->da_app_data, enter_args,
			exit_args, tdisp_params_ptr, meas_params_ptr,
			DEVICE_ASSIGN_APP_FUNC_ID_VDM_TDISP_LOCK);
		break;
	case VDEV_OP_UNLOCK:
		if (vd->rmi_state == RMI_VDEV_STATE_NEW) {
			/* no need to communicate to the device, return success */
			(void)memset(exit_args, 0, sizeof(*exit_args));
			rc = DEV_ASSIGN_STATUS_SUCCESS;
			goto out;
		} else {
			assert((vd->rmi_state == RMI_VDEV_STATE_STARTED) ||
			       (vd->rmi_state == RMI_VDEV_STATE_LOCKED) ||
			       (vd->rmi_state == RMI_VDEV_STATE_ERROR));
			rc = dev_assign_dev_communicate(&pd->da_app_data, enter_args,
				exit_args, tdisp_params_ptr, meas_params_ptr,
				DEVICE_ASSIGN_APP_FUNC_ID_VDM_TDISP_STOP);
		}
		break;
	case VDEV_OP_GET_REPORT:
		/*
		 * In this RDEV op, the device interface report is retrieved and
		 * its hash needs to be calculated during device communication
		 */
		rc = dev_assign_dev_communicate(&pd->da_app_data, enter_args,
			exit_args, tdisp_params_ptr, meas_params_ptr,
			DEVICE_ASSIGN_APP_FUNC_ID_VDM_TDISP_REPORT);
		break;
	case VDEV_OP_START:
		rc = dev_assign_dev_communicate(&pd->da_app_data, enter_args,
			exit_args, tdisp_params_ptr, meas_params_ptr,
			DEVICE_ASSIGN_APP_FUNC_ID_VDM_TDISP_START);
		break;
	default:
		assert(false);
		rc = -1;
	}

	if (rc == DEV_ASSIGN_STATUS_ERROR) {
		goto out;
	}

	if (copy_vdev_cached_digest(vd, &pd->da_app_data) != DEV_ASSIGN_STATUS_SUCCESS) {
		rc = DEV_ASSIGN_STATUS_ERROR;
	}

out:
	app_unmap_shared_page(&pd->da_app_data);
	return rc;
}

static void set_comm_state(int rc, uint32_t *comm_state)
{
	if (IS_DEV_ASSIGN_STATUS_COMM_BLOCKED(rc)) {
		*comm_state = DEV_COMM_ACTIVE;
	} else if (rc == DEV_ASSIGN_STATUS_ERROR) {
		*comm_state = DEV_COMM_ERROR;
	} else if (rc == DEV_ASSIGN_STATUS_SUCCESS) {
		*comm_state = DEV_COMM_IDLE;
	} else {
		assert(false);
	}
}

unsigned long dev_communicate(struct pdev *pd,
			      struct vdev *vd, struct granule *g_dev_comm_data)
{
	struct rmi_dev_comm_enter enter_args;
	struct rmi_dev_comm_exit exit_args;
	unsigned long comm_rc;
	int rc;
	void *aux_mapped_addr = NULL;

	assert(pd != NULL);

	if (vd == NULL) {
		if ((pd->dev_comm_state == DEV_COMM_IDLE) ||
		    (pd->dev_comm_state == DEV_COMM_ERROR)) {
			return RMI_ERROR_DEVICE;
		}
	} else {
		if ((vd->comm_state == DEV_COMM_IDLE) ||
		    (vd->comm_state == DEV_COMM_ERROR)) {
			return RMI_ERROR_DEVICE;
		}
	}

	/* Validate RmiDevCommEnter arguments in DevCommData */
	/* coverity[uninit_use_in_call:SUPPRESS] */
	comm_rc = copyin_and_validate_dev_comm_enter(g_dev_comm_data, &enter_args,
		pd->dev_comm_state);
	if (comm_rc != RMI_SUCCESS) {
		return comm_rc;
	}

	/* Map app PDEV aux granules to slot starting SLOT_PDEV_APP_AUX0 */
	/* coverity[overrun-buffer-val:SUPPRESS] */
	if (pd->num_app_aux > 0U) {
		aux_mapped_addr = buffer_pdev_app_aux_map(pd->g_app_aux, pd->num_app_aux);
	}

	if (vd == NULL) {
		rc = pdev_dispatch_cmd(pd, &enter_args, &exit_args);
	} else {
		rc = vdev_dispatch_cmd(pd, vd, &enter_args, &exit_args);
	}

	if (aux_mapped_addr != NULL) {
		buffer_pdev_app_aux_unmap(aux_mapped_addr, pd->num_app_aux);
	}

	comm_rc = copyout_dev_comm_exit(g_dev_comm_data,
				       &exit_args);
	if (comm_rc != RMI_SUCCESS) {
		/*
		 * Communication to device has happened, but failed to copy out
		 * to exit args. Don't return early so that Comm State to error
		 * below.
		 */
		rc = DEV_ASSIGN_STATUS_ERROR;
	}

	/*
	 * Based on the device communication results update the device comm state
	 */
	if (vd == NULL) {
		set_comm_state(rc, &pd->dev_comm_state);
	} else {
		set_comm_state(rc, &vd->comm_state);
	}

	return comm_rc;
}

/*
 * smc_pdev_communicate
 *
 * pdev_addr	- PA of the PDEV
 * data_addr	- PA of the communication data structure
 */
void smc_pdev_communicate(unsigned long pdev_addr,
			  unsigned long dev_comm_data_addr,
			  struct smc_result *res)
{
	struct granule *g_pdev;
	struct granule *g_dev_comm_data;
	struct pdev *pd;
	struct pdev_stream *stream = NULL;
	unsigned long rmi_rc;
	bool update_stream_op_state = false;

	if (!is_rmi_feat_da_enabled()) {
		res->x[0] = SMC_NOT_SUPPORTED;
		return;
	}

	if (!GRANULE_ALIGNED(pdev_addr) || !GRANULE_ALIGNED(dev_comm_data_addr)) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	/* TODO_ALP17: Ensure PdevIsBusy == False */

	/* Lock pdev granule and map it */
	g_pdev = find_lock_granule(pdev_addr, GRANULE_STATE_PDEV);
	if (g_pdev == NULL) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	pd = buffer_granule_map(g_pdev, SLOT_PDEV);
	assert(pd != NULL);

	g_dev_comm_data = find_granule(dev_comm_data_addr);
	if ((g_dev_comm_data == NULL) ||
		(granule_unlocked_state(g_dev_comm_data) != GRANULE_STATE_NS)) {
		rmi_rc = RMI_ERROR_INPUT;
		goto out_pdev_buf_unmap;
	}

	assert(pd->g_pdev == g_pdev);

	if ((pd->op.curr == PDEV_OP_CONNECT) ||
	    (pd->op.curr == PDEV_OP_DISCONNECT) ||
	    (pd->op.curr == PDEV_OP_STREAM_COMPLETE) ||
	    (pd->op.curr == PDEV_OP_KEY_PURGE) ||
	    (pd->op.curr == PDEV_OP_KEY_REFRESH)) {
		stream = pdev_stream_granules_lock_map(pd->g_stream_aux, pd->op.op_stream_type);
		assert(stream != NULL);
		pd->op.stream_op_state = stream->op_state;
		update_stream_op_state = true;
	}

	rmi_rc = dev_communicate(pd, NULL, g_dev_comm_data);

	/*
	 * Based on the device communication results update the device IO state
	 * and PDEV state.
	 */
	if (pd->dev_comm_state == DEV_COMM_ERROR) {
		pd->rmi_state =  RMI_PDEV_STATE_ERROR;
	} else if (pd->dev_comm_state == DEV_COMM_IDLE) {
		if (pd->op.curr == PDEV_OP_STOP) {
			pd->rmi_state = RMI_PDEV_STATE_STOPPED;
			pd->op.curr = PDEV_OP_NONE;
			pd->op.stream_op_state = STREAM_OP_STATE_NONE;
		} else {
			if (pd->rmi_state == RMI_PDEV_STATE_NEW) {
				if (PDEV_CATEGORY(pd) != RMI_PDEV_ROOTPORT) {
					pd->rmi_state = RMI_PDEV_STATE_NEEDS_KEY;
				} else {
					pd->rmi_state = RMI_PDEV_STATE_READY;
				}
			} else if (pd->rmi_state == RMI_PDEV_STATE_HAS_KEY) {
				pd->rmi_state = RMI_PDEV_STATE_READY;
			}

			if ((pd->op.curr == PDEV_OP_CONNECT) ||
			   (pd->op.curr == PDEV_OP_DISCONNECT) ||
			   (pd->op.curr == PDEV_OP_KEY_REFRESH)) {
				pd->op.curr = PDEV_OP_STREAM_COMPLETE;
			} else {
				pd->op.curr = PDEV_OP_NONE;
			}
		}
	}

	if (update_stream_op_state) {
		stream->op_state = pd->op.stream_op_state;
		pdev_stream_granules_unmap_unlock(pd->g_stream_aux, stream, pd->op.op_stream_type);
	}

out_pdev_buf_unmap:
	buffer_unmap(pd);
	granule_unlock(g_pdev);

	res->x[0] = rmi_rc;
}

/*
 * smc_pdev_get_state
 *
 * Get state of a PDEV.
 *
 * pdev_addr	- PA of the PDEV
 * res		- SMC result
 */
void smc_pdev_get_state(unsigned long pdev_addr, struct smc_result *res)
{
	struct granule *g_pdev;
	struct pdev *pd;

	if (!is_rmi_feat_da_enabled()) {
		res->x[0] = SMC_NOT_SUPPORTED;
		return;
	}

	if (!GRANULE_ALIGNED(pdev_addr)) {
		goto out_err_input;
	}

	/* Lock pdev granule and map it */
	g_pdev = find_lock_granule(pdev_addr, GRANULE_STATE_PDEV);
	if (g_pdev == NULL) {
		goto out_err_input;
	}

	pd = buffer_granule_map(g_pdev, SLOT_PDEV);
	if (pd == NULL) {
		granule_unlock(g_pdev);
		goto out_err_input;
	}

	assert(pd->g_pdev == g_pdev);
	assert(pd->rmi_state <= RMI_PDEV_STATE_ERROR);
	res->x[0] = RMI_SUCCESS;
	res->x[1] = pd->rmi_state;

	buffer_unmap(pd);
	granule_unlock(g_pdev);

	return;

out_err_input:
	res->x[0] = RMI_ERROR_INPUT;
}

static unsigned long get_expected_key_size(unsigned long rmi_key_algo)
{
	switch (rmi_key_algo) {
	case RMI_SIGNATURE_ALGORITHM_ECDSA_P256:
		return 65;
	case RMI_SIGNATURE_ALGORITHM_ECDSA_P384:
		return 97;
	case RMI_SIGNATURE_ALGORITHM_RSASSA_3072:
		return 384;
	default:
		return 0;
	}
}

static bool public_key_sig_algo_valid(unsigned long rmi_key_algo)
{
	return (rmi_key_algo == RMI_SIGNATURE_ALGORITHM_ECDSA_P256) ||
	       (rmi_key_algo == RMI_SIGNATURE_ALGORITHM_ECDSA_P384) ||
	       (rmi_key_algo == RMI_SIGNATURE_ALGORITHM_RSASSA_3072);
}

/*
 * Provide public key associated with a PDEV.
 *
 * pdev_addr		- PA of the PDEV
 * pubkey_params_addr	- PA of the pubkey parameters
 */
void smc_pdev_set_pubkey(unsigned long pdev_addr,
			 unsigned long pubkey_params_addr,
			 struct smc_result *res)
{
	struct granule *g_pdev;
	struct granule *g_pubkey_params;
	bool ns_access_ok;
	struct pdev *pd;
	struct rmi_public_key_params pubkey_params;
	unsigned long dev_assign_public_key_sig_algo;
	unsigned long dev_assign_public_key_expected_size;
	unsigned long smc_rc;
	int rc;

	if (!is_rmi_feat_da_enabled()) {
		res->x[0] = SMC_NOT_SUPPORTED;
		return;
	}

	if (!GRANULE_ALIGNED(pdev_addr) || !GRANULE_ALIGNED(pubkey_params_addr)) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	/* Map and copy public key parameter */
	g_pubkey_params = find_granule(pubkey_params_addr);
	if ((g_pubkey_params == NULL) ||
	    (granule_unlocked_state(g_pubkey_params) != GRANULE_STATE_NS)) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	ns_access_ok = ns_buffer_read(SLOT_NS, g_pubkey_params, 0U,
				      sizeof(struct rmi_public_key_params),
				      &pubkey_params);
	if (!ns_access_ok) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	/*
	 * Check key_len and metadata_len with max value.
	 */
	/* coverity[uninit_use:SUPPRESS] */
	if ((pubkey_params.key_len > PUBKEY_PARAM_KEY_LEN_MAX) ||
	    (pubkey_params.metadata_len > PUBKEY_PARAM_METADATA_LEN_MAX)) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	/* coverity[uninit_use:SUPPRESS] */
	dev_assign_public_key_sig_algo = pubkey_params.algo;
	if (!public_key_sig_algo_valid(dev_assign_public_key_sig_algo)) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	/*
	 * Validate 'key_len' against expected key length based on algorithm
	 */
	dev_assign_public_key_expected_size = get_expected_key_size(dev_assign_public_key_sig_algo);
	assert(dev_assign_public_key_expected_size != 0U);
	if (pubkey_params.key_len != dev_assign_public_key_expected_size) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	/* Lock pdev granule and map it */
	g_pdev = find_lock_granule(pdev_addr, GRANULE_STATE_PDEV);
	if (g_pdev == NULL) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	pd = buffer_granule_map(g_pdev, SLOT_PDEV);
	if (pd == NULL) {
		granule_unlock(g_pdev);
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	assert(pd->g_pdev == g_pdev);

	if (pd->rmi_state != RMI_PDEV_STATE_NEEDS_KEY) {
		smc_rc = RMI_ERROR_DEVICE;
		goto out_pdev_buf_unmap;
	}

	rc = dev_assign_set_public_key(&pd->da_app_data, &pubkey_params);
	if (rc == DEV_ASSIGN_STATUS_SUCCESS) {
		pd->dev_comm_state = DEV_COMM_PENDING;
		pd->rmi_state = RMI_PDEV_STATE_HAS_KEY;
		smc_rc = RMI_SUCCESS;
	} else {
		smc_rc = RMI_ERROR_DEVICE;
	}

out_pdev_buf_unmap:
	buffer_unmap(pd);

	granule_unlock(g_pdev);

	res->x[0] = smc_rc;
}

/*
 * Stop the PDEV. This sets the PDEV state to STOPPING, and a PDEV communicate
 * call can do device specific cleanup like terminating a secure session.
 *
 * pdev_addr	- PA of the PDEV
 */
void smc_pdev_stop(unsigned long pdev_addr, struct smc_result *res)
{
	struct granule *g_pdev;
	unsigned long smc_rc;
	struct pdev *pd;

	if (!is_rmi_feat_da_enabled()) {
		res->x[0] = SMC_NOT_SUPPORTED;
		return;
	}

	if (!GRANULE_ALIGNED(pdev_addr)) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	/* Lock pdev granule and map it */
	g_pdev = find_lock_granule(pdev_addr, GRANULE_STATE_PDEV);
	if (g_pdev == NULL) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	pd = buffer_granule_map(g_pdev, SLOT_PDEV);
	if (pd == NULL) {
		granule_unlock(g_pdev);
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	if ((pd->dev_comm_state != DEV_COMM_IDLE) ||
	    (pd->associated_stream_count > 0U) ||
	    (pd->num_vdevs != 0U)) {
		smc_rc = RMI_ERROR_DEVICE;
		goto out_pdev_buf_unmap;
	}

	pd->op.curr = PDEV_OP_STOP;
	pd->dev_comm_state = DEV_COMM_PENDING;
	smc_rc = RMI_SUCCESS;

out_pdev_buf_unmap:
	buffer_unmap(pd);

	granule_unlock(g_pdev);

	res->x[0] = smc_rc;
}

/*
 * Abort device communication associated with a PDEV.
 *
 * pdev_addr	- PA of the PDEV
 */
void smc_pdev_abort(unsigned long pdev_addr, struct smc_result *res)
{
	int rc __unused;
	struct granule *g_pdev;
	unsigned long smc_rc;
	struct pdev *pd;
	void *aux_mapped_addr;

	if (!is_rmi_feat_da_enabled()) {
		res->x[0] = SMC_NOT_SUPPORTED;
		return;
	}

	if (!GRANULE_ALIGNED(pdev_addr)) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	/* Lock pdev granule and map it */
	g_pdev = find_lock_granule(pdev_addr, GRANULE_STATE_PDEV);
	if (g_pdev == NULL) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	pd = buffer_granule_map(g_pdev, SLOT_PDEV);
	if (pd == NULL) {
		granule_unlock(g_pdev);
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	if (pd->dev_comm_state == DEV_COMM_IDLE) {
		smc_rc = RMI_ERROR_DEVICE;
		goto out_pdev_buf_unmap;
	}

	if (pd->num_app_aux > 0U) {
		/* Map app PDEV aux granules to slot starting SLOT_PDEV_APP_AUX0 */
		/* coverity[overrun-buffer-val:SUPPRESS] */
		aux_mapped_addr = buffer_pdev_app_aux_map(pd->g_app_aux, pd->num_app_aux);

		/*
		 * This will resume the blocked CMA SPDM command and the recv callback
		 * handler will return error and abort the command.
		 */
		rc = dev_assign_abort_app_operation(&pd->da_app_data);
		assert(rc == 0);

		buffer_pdev_app_aux_unmap(aux_mapped_addr, pd->num_app_aux);
	}

	pd->dev_comm_state = DEV_COMM_IDLE;

	smc_rc = RMI_SUCCESS;

out_pdev_buf_unmap:
	buffer_unmap(pd);

	granule_unlock(g_pdev);

	res->x[0] = smc_rc;
}

/*
 * Destroy a PDEV. Host can reclaim PDEV resources when the PDEV state is STOPPED
 * using RMI PDEV_DESTROY.
 *
 * pdev_addr	- PA of the PDEV
 */
void smc_pdev_destroy(unsigned long pdev_addr, struct smc_result *res)
{
	int rc __unused;
	struct granule *g_pdev;
	struct pdev *pd;
	struct sro_context *sro;
	unsigned long ret;
	size_t num_vdev_range_aux_granules;
	size_t app_aux_start_idx;

	if (!is_rmi_feat_da_enabled()) {
		res->x[0] = SMC_NOT_SUPPORTED;
		return;
	}

	if (!GRANULE_ALIGNED(pdev_addr)) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	/* Lock pdev granule and map it */
	g_pdev = find_lock_granule(pdev_addr, GRANULE_STATE_PDEV);
	if (g_pdev == NULL) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	pd = buffer_granule_map(g_pdev, SLOT_PDEV);
	assert(pd != NULL);

	if ((pd->rmi_state != RMI_PDEV_STATE_STOPPED)) {
		buffer_unmap(pd);
		granule_unlock(g_pdev);
		res->x[0] = RMI_ERROR_DEVICE;
		return;
	}

	/* No SRO is needed in case of rootport */
	if ((PDEV_CATEGORY(pd) == RMI_PDEV_ROOTPORT)) {
		buffer_unmap(pd);
		/* Move the PDEV granule from PDEV to delegated state */
		granule_unlock_transition_to_delegated(g_pdev);
		res->x[0] = RMI_SUCCESS;
		return;
	}

	ret = sro_ctx_reserve(SMC_RMI_PDEV_DESTROY, 0UL, false, false, SMC_RMI_OP_MEM_RECLAIM);
	if (ret != RMI_SUCCESS) {
		buffer_unmap(pd);
		granule_unlock(g_pdev);
		res->x[0] = ret;
		return;
	}

	/* Deinit the DSM context state */
	rc = (int)app_run(&pd->da_app_data, DEVICE_ASSIGN_APP_FUNC_ID_DEINIT,
				0, 0, 0, 0);
	assert(rc == DEV_ASSIGN_STATUS_SUCCESS);

	/* Clean up the device assignment app instance */
	(void)dev_assign_app_delete(&pd->da_app_data);

	/* Memory to reclaim */
	sro = my_sro_ctx();
	assert(sro != NULL);
	num_vdev_range_aux_granules = PDEV_VDEV_RANGE_AUX_COUNT_FROM_SLOT_COUNT(pd->max_num_vdevs);
	app_aux_start_idx = PDEV_VDEV_RANGES_AUX_GRANULE_IDX +
		num_vdev_range_aux_granules;

	sro->aux_op_ctx.aux_granules_pa[PDEV_STREAM_AUX_GRANULE_IDX] =
		granule_addr(pd->g_stream_aux);
	for (unsigned int i = 0U; i < num_vdev_range_aux_granules; i++) {
		sro->aux_op_ctx.aux_granules_pa[PDEV_VDEV_RANGES_AUX_GRANULE_IDX + i] =
			granule_addr(pd->g_vdevs_ranges_aux[i]);
	}
	for (unsigned int i = 0U; i < pd->num_app_aux; i++) {
		sro->aux_op_ctx.aux_granules_pa[app_aux_start_idx + i] =
			granule_addr(pd->g_app_aux[i]);
	}
	sro->aux_op_ctx.requested_aux_granules = app_aux_start_idx + pd->num_app_aux;

	buffer_unmap(pd);

	granule_unlock_transition(g_pdev, GRANULE_STATE_PARTIAL);

	/* Inform the host that can request a memory reclaim for the aux granules */
	sro_aux_op_start_reclaim(sro, res,
				 pdev_addr,
				 true,
				 RMI_SUCCESS,
				 sro->aux_op_ctx.requested_aux_granules,
				 GRANULE_STATE_PDEV_AUX);
}

/*
 * Initiate key refresh of a PDEV stream.
 *
 * pdev1_addr		- PA of the first PDEV object
 * pdev2_addr		- PA of the second PDEV object
 * stream_handle	- Stream handle
 */
void smc_pdev_stream_key_refresh(unsigned long pdev1_addr,
				 unsigned long pdev2_addr,
				 unsigned long stream_handle,
				 struct smc_result *res)
{
	struct granule *g_pdev1;
	struct granule *g_pdev2;
	struct pdev_stream *stream;
	struct pdev *pd1;
	struct pdev *pd2;
	unsigned long rmi_rc;
	unsigned char stream_type = RMI_PDEV_STREAM_TYPE_COUNT;
	unsigned long handle_pdev1_addr;

	if (!is_rmi_feat_da_enabled()) {
		res->x[0] = SMC_NOT_SUPPORTED;
		return;
	}

	if (!GRANULE_ALIGNED(pdev1_addr) ||
	    !GRANULE_ALIGNED(pdev2_addr)) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	if (!find_lock_two_granules(pdev1_addr,
				GRANULE_STATE_PDEV,
				&g_pdev1,
				pdev2_addr,
				GRANULE_STATE_PDEV,
				&g_pdev2)) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	pd1 = buffer_granule_map(g_pdev1, SLOT_PDEV);
	if (pd1 == NULL) {
		rmi_rc = RMI_ERROR_INPUT;
		goto unlock_pdevs;
	}

	if ((!unpack_stream_handle(stream_handle, &handle_pdev1_addr, &stream_type)) ||
	    (handle_pdev1_addr != pdev1_addr)) {
		rmi_rc = RMI_ERROR_INPUT;
		goto unmap_pdev1;
	}

	stream = pdev_stream_granules_lock_map(pd1->g_stream_aux, stream_type);
	assert(stream != NULL);

	if (!stream->taken) {
		rmi_rc = RMI_ERROR_INPUT;
		goto unmap_pd1_aux;
	}

	if (stream->pd2_addr != pdev2_addr) {
		rmi_rc = RMI_ERROR_INPUT;
		goto unmap_pd1_aux;
	}

	pd2 = buffer_granule_map(g_pdev2, SLOT_PDEV2);
	if (pd2 == NULL) {
		rmi_rc = RMI_ERROR_INPUT;
		goto unmap_pd1_aux;
	}

	if ((pd1->rmi_state != RMI_PDEV_STATE_READY) ||
	    (pd1->op.curr != PDEV_OP_NONE) ||
	    (pd1->dev_comm_state != DEV_COMM_IDLE) ||
	    (pd2->rmi_state != RMI_PDEV_STATE_READY) ||
	    (pd2->op.curr != PDEV_OP_NONE) ||
	    (pd2->dev_comm_state != DEV_COMM_IDLE)) {
		rmi_rc = RMI_ERROR_INPUT;
		goto unmap_pdev2;
	}

	if ((stream_type == RMI_PDEV_STREAM_NCOH_SYS) ||
	    (stream_type == RMI_PDEV_STREAM_COH_SYS) ||
	    (stream->state != PDEV_STREAM_CONNECTED)) {
		rmi_rc = RMI_ERROR_DEVICE;
		goto unmap_pdev2;
	}

	stream->state = PDEV_STREAM_KEY_REFRESHING;
	stream->op_state = STREAM_OP_STATE_START;
	pd1->op.curr = PDEV_OP_KEY_REFRESH;
	pd1->dev_comm_state = DEV_COMM_PENDING;
	pd1->op.op_stream_type = stream_type;
	pd2->op.curr = PDEV_OP_KEY_REFRESH;
	pd2->dev_comm_state = DEV_COMM_PENDING;
	pd2->g_stream_aux = pd1->g_stream_aux;
	pd2->op.op_stream_type = stream_type;

	rmi_rc = RMI_SUCCESS;

unmap_pdev2:
	buffer_unmap(pd2);
unmap_pd1_aux:
	pdev_stream_granules_unmap_unlock(pd1->g_stream_aux, stream, stream_type);
unmap_pdev1:
	buffer_unmap(pd1);

unlock_pdevs:
	granule_unlock(g_pdev1);
	granule_unlock(g_pdev2);

	res->x[0] = rmi_rc;
}

static unsigned long validate_pdev_stream_params(struct rmi_pdev_stream_params *stream_params)
{
	if (stream_params->num_addr_range > RMI_PDEV_STREAM_ADDR_RANGE_CNT) {
		return RMI_ERROR_INPUT;
	}

	if (stream_params->stream_type != RMI_PDEV_STREAM_NCOH) {
		return RMI_ERROR_NOT_SUPPORTED;
	}

	/* TODO: Check:
	 *
	 * - The IDE stream identifier is valid
	 * - The base and top of every address range is aligned to the size of a Granule
	 * - Every address range falls within a memory range permitted by the system
	 * - None of the address ranges overlaps another address range for this PDEV stream
	 * - None of the address ranges overlaps an address range of any other PDEV stream
	 * - A stream between the specified PDEV(s) is supported by the implementation
	 */

	return RMI_SUCCESS;
}

/*
 * Initiate connection of a PDEV stream.
 *
 * stream_params_addr	- PA of PDEV stream parameters
 *
 * ret1			- PDEV stream handle
 */
void smc_pdev_stream_connect(unsigned long stream_params_addr, struct smc_result *res)
{
	struct granule *g_stream_params;
	struct granule *g_pdev1;
	struct granule *g_pdev2;
	struct rmi_pdev_stream_params stream_params;
	struct pdev *pd1;
	struct pdev *pd2;
	struct pdev_stream *stream;
	bool ns_access_ok;
	unsigned long params_res;
	__unused int rc;

	if (!is_rmi_feat_da_enabled()) {
		res->x[0] = SMC_NOT_SUPPORTED;
		return;
	}

	if (!GRANULE_ALIGNED(stream_params_addr)) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	/* Map and copy Stream parameters */
	g_stream_params = find_granule(stream_params_addr);
	if ((g_stream_params == NULL) ||
	    (granule_unlocked_state(g_stream_params) != GRANULE_STATE_NS)) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	ns_access_ok = ns_buffer_read(SLOT_NS, g_stream_params, 0U,
				      sizeof(struct rmi_pdev_stream_params),
				      &stream_params);
	if (!ns_access_ok) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	/* coverity[uninit_use:SUPPRESS] */
	params_res = validate_pdev_stream_params(&stream_params);
	if (params_res != RMI_SUCCESS) {
		res->x[0] = params_res;
		return;
	}

	/* coverity[uninit_use:SUPPRESS] */
	if (!GRANULE_ALIGNED(stream_params.pdev_1) ||
	    !GRANULE_ALIGNED(stream_params.pdev_2)) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	if (!find_lock_two_granules(stream_params.pdev_1,
				GRANULE_STATE_PDEV,
				&g_pdev1,
				stream_params.pdev_2,
				GRANULE_STATE_PDEV,
				&g_pdev2)) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	pd1 = buffer_granule_map(g_pdev1, SLOT_PDEV);
	if (pd1 == NULL) {
		res->x[0] = RMI_ERROR_INPUT;
		goto unlock_pdevs;
	}

	pd2 = buffer_granule_map(g_pdev2, SLOT_PDEV2);
	if (pd2 == NULL) {
		res->x[0] = RMI_ERROR_INPUT;
		goto unmap_pdev1;
	}

	if ((((PDEV_CATEGORY(pd1) != RMI_PDEV_ENDPOINT_ACCEL_OFF_CHIP))) ||
	    (pd1->rmi_state != RMI_PDEV_STATE_READY) ||
	    (pd1->op.curr != PDEV_OP_NONE) ||
	    (pd1->dev_comm_state != DEV_COMM_IDLE) ||
	    (PDEV_CATEGORY(pd2) != RMI_PDEV_ROOTPORT) ||
	    (pd2->rmi_state != RMI_PDEV_STATE_READY) ||
	    (pd2->op.curr != PDEV_OP_NONE) ||
	    (pd2->dev_comm_state != DEV_COMM_IDLE)) {
		res->x[0] = RMI_ERROR_INPUT;
		goto unmap_pdev2;
	}

	stream = pdev_stream_granules_lock_map(pd1->g_stream_aux, stream_params.stream_type);
	assert(stream != NULL);

	if (stream->taken) {
		res->x[0] = RMI_ERROR_INPUT;
		goto unmap_pd1_aux;
	}

	pd1->op.curr = PDEV_OP_CONNECT;
	pd1->dev_comm_state = DEV_COMM_PENDING;
	pd1->op.op_stream_type = stream_params.stream_type;
	pd1->associated_stream_count += 1U;
	pd2->op.curr = PDEV_OP_CONNECT;
	pd2->dev_comm_state = DEV_COMM_PENDING;
	pd2->op.op_stream_type = stream_params.stream_type;
	pd2->associated_stream_count += 1U;
	pd2->g_stream_aux = pd1->g_stream_aux;

	rc = (int)app_run(&pd1->da_app_data, DEVICE_ASSIGN_APP_FUNC_SET_PDEV_STREAM_DATA,
		      stream_params.ide_sid, pd2->dev.bdf, 0, 0);
	assert(rc == DEV_ASSIGN_STATUS_SUCCESS);

	/* Set stream properties */
	stream->state = PDEV_STREAM_CONNECTING;
	stream->ide_sid = stream_params.ide_sid;
	stream->num_addr_range = stream_params.num_addr_range;
	stream->pd1_addr = stream_params.pdev_1;
	stream->pd2_addr = stream_params.pdev_2;
	stream->op_state = STREAM_OP_STATE_START;
	(void)memcpy(stream->addr_range,
		     stream_params.addr_range,
		     stream->num_addr_range * sizeof(struct rmi_address_range));
	stream->taken = true;

	res->x[0] = RMI_SUCCESS;
	res->x[1] = pack_stream_handle(stream_params.pdev_1, stream_params.stream_type);
unmap_pd1_aux:
	pdev_stream_granules_unmap_unlock(pd1->g_stream_aux, stream, stream_params.stream_type);
unmap_pdev2:
	buffer_unmap(pd2);
unmap_pdev1:
	buffer_unmap(pd1);

unlock_pdevs:
	granule_unlock(g_pdev1);
	granule_unlock(g_pdev2);
}

/*
 * Initiate disconnection of a PDEV stream.
 *
 * pdev1_addr		- PA of the first PDEV object
 * pdev2_addr		- PA of the second PDEV object
 * stream_handle	- Stream handle
 */
void smc_pdev_stream_disconnect(unsigned long pdev1_addr,
				unsigned long pdev2_addr,
				unsigned long stream_handle,
				struct smc_result *res)
{
	struct granule *g_pdev1;
	struct granule *g_pdev2;
	struct pdev_stream *stream;
	struct pdev *pd1;
	struct pdev *pd2;
	unsigned long rmi_rc;
	unsigned char stream_type = RMI_PDEV_STREAM_TYPE_COUNT;
	unsigned long handle_pdev1_addr;


	if (!is_rmi_feat_da_enabled()) {
		res->x[0] = SMC_NOT_SUPPORTED;
		return;
	}

	if (!GRANULE_ALIGNED(pdev1_addr) ||
	    !GRANULE_ALIGNED(pdev2_addr)) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	if ((!unpack_stream_handle(stream_handle, &handle_pdev1_addr, &stream_type)) ||
	    (handle_pdev1_addr != pdev1_addr)) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	if (!find_lock_two_granules(pdev1_addr,
				GRANULE_STATE_PDEV,
				&g_pdev1,
				pdev2_addr,
				GRANULE_STATE_PDEV,
				&g_pdev2)) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	pd1 = buffer_granule_map(g_pdev1, SLOT_PDEV);
	if (pd1 == NULL) {
		rmi_rc = RMI_ERROR_INPUT;
		goto unlock_pdevs;
	}

	stream = pdev_stream_granules_lock_map(pd1->g_stream_aux, stream_type);
	assert(stream != NULL);

	if (!stream->taken) {
		rmi_rc = RMI_ERROR_INPUT;
		goto unlock_stream;
	}

	if (stream->state != PDEV_STREAM_CONNECTED) {
		rmi_rc = RMI_ERROR_DEVICE;
		goto unlock_stream;
	}

	if (stream->pd2_addr != pdev2_addr) {
		rmi_rc = RMI_ERROR_INPUT;
		goto unlock_stream;
	}

	pd2 = buffer_granule_map(g_pdev2, SLOT_PDEV2);
	if (pd2 == NULL) {
		rmi_rc = RMI_ERROR_INPUT;
		goto unlock_stream;
	}

	if (((pd1->rmi_state != RMI_PDEV_STATE_READY) &&
	     (pd1->rmi_state != RMI_PDEV_STATE_ERROR)) ||
	    (pd1->dev_comm_state != DEV_COMM_IDLE) ||
	    ((pd2->rmi_state != RMI_PDEV_STATE_READY) &&
	     (pd2->rmi_state != RMI_PDEV_STATE_ERROR)) ||
	    (pd2->dev_comm_state != DEV_COMM_IDLE)) {
		rmi_rc = RMI_ERROR_INPUT;
		goto unmap_pdev2;
	}

	if (pd1->num_vdevs != 0U) {
		rmi_rc = RMI_ERROR_DEVICE;
		goto unmap_pdev2;
	}

	stream->state = PDEV_STREAM_DISCONNECTING;
	stream->op_state = STREAM_OP_STATE_START;
	pd1->op.curr = PDEV_OP_DISCONNECT;
	pd1->dev_comm_state = DEV_COMM_PENDING;
	pd1->op.op_stream_type = stream_type;
	pd2->op.curr = PDEV_OP_DISCONNECT;
	pd2->dev_comm_state = DEV_COMM_PENDING;
	pd2->op.op_stream_type = stream_type;
	pd2->g_stream_aux = pd1->g_stream_aux;

	rmi_rc = RMI_SUCCESS;

unmap_pdev2:
	buffer_unmap(pd2);
unlock_stream:
	pdev_stream_granules_unmap_unlock(pd1->g_stream_aux, stream, stream_type);
	buffer_unmap(pd1);

unlock_pdevs:
	granule_unlock(g_pdev1);
	granule_unlock(g_pdev2);

	res->x[0] = rmi_rc;
}

/*
 * Complete an operation on a PDEV stream.
 *
 * pdev1_addr		- PA of the first PDEV object
 * pdev2_addr		- PA of the second PDEV object
 * stream_handle	- Stream handle
 */
void smc_pdev_stream_complete(unsigned long pdev1_addr,
			      unsigned long pdev2_addr,
			      unsigned long stream_handle,
			      struct smc_result *res)
{
	struct granule *g_pdev1;
	struct granule *g_pdev2;
	struct pdev_stream *stream;
	struct pdev *pd1;
	struct pdev *pd2;
	unsigned long rmi_rc;
	unsigned long pdev1_addr_handle = 0UL;
	unsigned char stream_type = RMI_PDEV_STREAM_TYPE_COUNT;

	if (!is_rmi_feat_da_enabled()) {
		res->x[0] = SMC_NOT_SUPPORTED;
		return;
	}

	if (!GRANULE_ALIGNED(pdev1_addr) ||
	    !GRANULE_ALIGNED(pdev2_addr)) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	if ((!unpack_stream_handle(stream_handle, &pdev1_addr_handle, &stream_type)) ||
	    (pdev1_addr_handle != pdev1_addr)) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	if (!find_lock_two_granules(pdev1_addr,
				GRANULE_STATE_PDEV,
				&g_pdev1,
				pdev2_addr,
				GRANULE_STATE_PDEV,
				&g_pdev2)) {
		res->x[0] = RMI_ERROR_INPUT;
		return;

	}

	pd1 = buffer_granule_map(g_pdev1, SLOT_PDEV);
	if (pd1 == NULL) {
		rmi_rc = RMI_ERROR_INPUT;
		goto unlock_pdevs;
	}

	stream = pdev_stream_granules_lock_map(pd1->g_stream_aux, stream_type);
	assert(stream != NULL);

	if (!stream->taken) {
		rmi_rc = RMI_ERROR_INPUT;
		goto unlock_stream;
	}

	if (stream->pd2_addr != pdev2_addr) {
		rmi_rc = RMI_ERROR_INPUT;
		goto unlock_stream;
	}

	pd2 = buffer_granule_map(g_pdev2, SLOT_PDEV2);
	if (pd2 == NULL) {
		rmi_rc = RMI_ERROR_INPUT;
		goto unlock_stream;
	}

	if ((pd1->rmi_state != RMI_PDEV_STATE_READY) ||
	    (pd1->dev_comm_state != DEV_COMM_IDLE) ||
	    (pd2->rmi_state != RMI_PDEV_STATE_READY) ||
	    (pd2->dev_comm_state != DEV_COMM_IDLE)) {
		rmi_rc = RMI_ERROR_INPUT;
		goto unmap_pdev2;
	}

	if ((pd1->op.curr != PDEV_OP_STREAM_COMPLETE) ||
	    (pd2->op.curr != PDEV_OP_STREAM_COMPLETE)) {
		rmi_rc = RMI_ERROR_DEVICE;
		goto unmap_pdev2;
	}

	switch (stream->state) {
	case PDEV_STREAM_CONNECTING:
	case PDEV_STREAM_KEY_PURGING:
	case PDEV_STREAM_KEY_REFRESHING:
		stream->state = PDEV_STREAM_CONNECTED;
		break;
	case PDEV_STREAM_DISCONNECTING:
		stream->state = PDEV_STREAM_DISCONNECTED;
		stream->taken = false;
		pd1->associated_stream_count -= 1U;
		pd2->associated_stream_count -= 1U;
		break;
	default:
		rmi_rc = RMI_ERROR_DEVICE;
		goto unmap_pdev2;
	}

	stream->op_state = STREAM_OP_STATE_NONE;
	pd1->op.curr = PDEV_OP_NONE;
	pd2->op.curr = PDEV_OP_NONE;
	pd2->g_stream_aux = NULL;

	rmi_rc = RMI_SUCCESS;

unmap_pdev2:
	buffer_unmap(pd2);
unlock_stream:
	pdev_stream_granules_unmap_unlock(pd1->g_stream_aux, stream, stream_type);
	buffer_unmap(pd1);

unlock_pdevs:
	granule_unlock(g_pdev1);
	granule_unlock(g_pdev2);

	res->x[0] = rmi_rc;
}

/*
 * Initiate purge of inactive keys from a PDEV stream.
 *
 * pdev1_addr		- PA of the first PDEV object
 * pdev2_addr		- PA of the second PDEV object
 * stream_handle	- Stream handle
 */
void smc_pdev_stream_key_purge(unsigned long pdev1_addr,
			       unsigned long pdev2_addr,
			       unsigned long stream_handle,
			       struct smc_result *res)
{
	(void)pdev1_addr;
	(void)pdev2_addr;
	(void)stream_handle;
	res->x[0] = RMI_ERROR_NOT_SUPPORTED;
}
