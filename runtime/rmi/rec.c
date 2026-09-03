/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <app.h>
#include <arch.h>
#include <arch_features.h>
#include <buffer.h>
#include <debug.h>
#include <gic.h>
#include <granule.h>
#include <measurement.h>
#include <pcpu_data.h>
#include <planes.h>
#include <psci.h>
#include <realm.h>
#include <rec.h>
#include <s2tt.h>
#include <smc-handler.h>
#include <smc-rmi.h>
#include <smc.h>
#include <sro_context.h>
#include <stdbool.h>
#include <stddef.h>
#include <string.h>

static void init_rec_sysregs(STRUCT_TYPE sysreg_state *sysregs,
			     unsigned long mpidr)
{
	/* Set non-zero values only */
	sysregs->pp_sysregs.sctlr_el1 = SCTLR_EL1_FLAGS;
	sysregs->pp_sysregs.mdscr_el1 = MDSCR_EL1_TDCC_BIT;
	sysregs->vmpidr_el2 = rec_mpidr_to_mpidr(mpidr) | VMPIDR_EL2_RES1;
	sysregs->cnthctl_el2 = CNTHCTL_EL2_NO_TRAPS;
	sysregs->cptr_el2 = CPTR_EL2_VHE_INIT;
}

/*
 * Starting level of the stage 2 translation
 * lookup to VTCR_EL2.SL0[7:6].
 */
static const unsigned long sl0_val[] = {
	VTCR_SL0_4K_LM1,
	VTCR_SL0_4K_L0,
	VTCR_SL0_4K_L1,
	VTCR_SL0_4K_L2,
	VTCR_SL0_4K_L3
};

static unsigned long realm_vtcr_ps(unsigned long s2oa_limit)
{
	if (s2oa_limit > (UL(1) << 48)) {
		return VTCR_PS_52;
	}

	if (s2oa_limit > (UL(1) << 44)) {
		return VTCR_PS_48;
	}

	if (s2oa_limit > (UL(1) << 42)) {
		return VTCR_PS_44;
	}

	if (s2oa_limit > (UL(1) << 40)) {
		return VTCR_PS_42;
	}

	if (s2oa_limit > (UL(1) << 36)) {
		return VTCR_PS_40;
	}

	if (s2oa_limit > (UL(1) << 32)) {
		return VTCR_PS_36;
	}

	/* Default */
	return VTCR_PS_32;
}

unsigned long realm_vtcr(struct rd *rd)
{
	unsigned long t0sz, sl0;
	unsigned long vtcr = is_feat_vmid16_present() ?
				(VTCR_FLAGS | VTCR_VS) : VTCR_FLAGS;
	int s2_starting_level = realm_rtt_starting_level(rd);
	bool lpa2 = s2tt_lpa2_enabled(&rd->s2_ctx[PRIMARY_S2_CTX_ID]);

	assert(((!lpa2) && (s2_starting_level >= S2TT_MIN_STARTING_LEVEL)) ||
	       ((lpa2) && (s2_starting_level >= S2TT_MIN_STARTING_LEVEL_LPA2)));
	assert(s2_starting_level <= S2TT_PAGE_LEVEL);

	/*
	 * sl_starting_level can be -1, so add an offset to compensate for that
	 * to index sl0_val.
	 */
	sl0 = sl0_val[s2_starting_level + 1];

	t0sz = 64UL - realm_ipa_bits(rd);
	t0sz &= MASK(VTCR_T0SZ);

	vtcr |= t0sz;
	vtcr |= sl0;
	vtcr |= realm_vtcr_ps(rd->s2_ctx[PRIMARY_S2_CTX_ID].s2oa_limit);

	if (lpa2 == true) {
		if (s2_starting_level == -1) {
			vtcr |= VTCR_SL2_4K_LM1;
		}
		vtcr |= VTCR_DS_52BIT;
	}

	/* Enable S2PIE and S2POE */
	if (rd->rtt_s2ap_encoding == S2AP_INDIRECT_ENC) {
		vtcr |= VTCR_S2PIE | VTCR_S2POE;
	}

	return vtcr;
}

static void init_common_sysregs(struct rec *rec, struct rd *rd)
{
	unsigned long mdcr_el2_val = read_mdcr_el2();

	/* Set non-zero values only */
	rec->common_sysregs.hcr_el2 = HCR_EL2_REALM;
	rec->common_sysregs.vtcr_el2 = realm_vtcr(rd);

	/* Control trapping of accesses to PMU registers */
	if (rd->pmu_enabled) {
		mdcr_el2_val &= ~(MDCR_EL2_TPM_BIT | MDCR_EL2_TPMCR_BIT);

		/*
		 * Set MDCR_EL2.HPMN to assign event counters into
		 * the first range
		 */
		mdcr_el2_val &= ~MASK(MDCR_EL2_HPMN);
		mdcr_el2_val |= INPLACE(MDCR_EL2_HPMN, rd->pmu_num_ctrs);
	} else {
		mdcr_el2_val |= (MDCR_EL2_TPM_BIT | MDCR_EL2_TPMCR_BIT);

		/*
		 * Set HPMN to 0 so all counters are in the second
		 * (host-owned) range, making none visible to the
		 * Realm. HPMN=0 requires FEAT_HPMN0.
		 */
		if (is_feat_hpmn0_present()) {
			mdcr_el2_val &= ~MASK(MDCR_EL2_HPMN);
		}
	}

	rec->common_sysregs.mdcr_el2 = mdcr_el2_val;

}

/*
 * Function to initialize sysregs.vttbr_el2 for each plane.
 *
 * This function expects that the aux granules are mapped and initialized.
 */
static void init_vttbr(struct rec *rec, struct rd *rd)
{
	for (unsigned int i = 0U; i < realm_num_planes(rd); i++) {
		struct s2tt_context *s2_ctx = plane_to_s2_context(rd, i);
		bool lpa2 = s2tt_lpa2_enabled(s2_ctx);
		STRUCT_TYPE sysreg_state *sysregs = REC_GET_SYSREGS_FROM_AUX(rec, i);

		sysregs->vttbr_el2 =
			(granule_addr(s2_ctx->g_rtt) & MASK(TTBRx_EL2_BADDR));
		if (lpa2 == true) {
			sysregs->vttbr_el2 =
				TTBRx_EL2_SET_MSB_LPA2((granule_addr(s2_ctx->g_rtt)),
							(sysregs->vttbr_el2));
		}

		sysregs->vttbr_el2 |= INPLACE(VTTBR_EL2_VMID, s2_ctx->vmid);
	}
}

static void init_rec_regs(struct rec *rec,
			  struct rmi_rec_params *rec_params,
			  struct rd *rd)
{
	/* Plane N context is initialized in plane_enter() */
	void *rec_aux = buffer_rec_aux_granules_map(rec->g_aux, rec->num_rec_aux);

	for (unsigned int i = 0U; i < rec_num_planes(rec); i++) {
		STRUCT_TYPE sysreg_state *sysregs = REC_GET_SYSREGS_FROM_AUX(rec, i);

		if (i == PLANE_0_ID) {
			struct rec_plane *plane = rec_plane_0(rec);

			/* Initialize Plane 0 GPRS */
			for (unsigned int j = 0U; j < REC_CREATE_NR_GPRS; j++) {
				plane->regs[j] = rec_params->gprs[j];
			}

			plane->pc = rec_params->pc;

			plane->pstate = SPSR_EL2_MODE_EL1h |
				  SPSR_EL2_nRW_AARCH64 |
				  SPSR_EL2_F_BIT |
				  SPSR_EL2_I_BIT |
				  SPSR_EL2_A_BIT |
				  SPSR_EL2_D_BIT;
		}

		init_rec_sysregs(sysregs, rec_params->mpidr);
	}

	init_common_sysregs(rec, rd);
	init_vttbr(rec, rd);

	buffer_rec_aux_unmap(rec_aux, rec->num_rec_aux);
}

/* Initialize rec SIMD state */
static void rec_simd_state_init(struct rec *r)
{
	int __unused retval;

	retval = simd_context_init(SIMD_OWNER_REL1, r->aux_data.simd_ctx,
				   &r->realm_info.simd_cfg);
	assert(retval == 0);
}

/* Initialize rec PMU state */
static void rec_pmu_state_init(struct rec *r)
{
	unsigned int num_planes = rec_num_planes(r);

	for (unsigned int i = 0U; i < num_planes; i++) {
		STRUCT_TYPE sysreg_state *sysregs =
			REC_GET_SYSREGS_FROM_AUX(r, i);
		assert(sysregs->pmu != NULL);

		sysregs->pmu->pmcr_el0 = r->realm_info.pmu_enabled ?
					PMCR_EL0_INIT_RESET : PMCR_EL0_INIT;
	}
}

/*
 * Initializes granule pages that are used for attestation heap, PMU and SIMD.
 * As part of initialization this function maps and unmaps the rec aux granules.
 */
static void rec_aux_granules_init(struct rec *r)
{
	void *rec_aux;
	struct rec_aux_data *aux_data;
	int ret;
	struct pmu_state *pmu;
	uintptr_t granule_pas[MAX_REC_AUX_GRANULES];
	size_t granule_pa_count;
	size_t used_aux_pages;
	unsigned int num_planes;

	/* Map auxiliary granules */
	/* coverity[overrun-buffer-val:SUPPRESS] */
	rec_aux = buffer_rec_aux_granules_map_zeroed(r->g_aux, r->num_rec_aux);
	assert(rec_aux != NULL);

	/*
	 * Ensure we have enough aux granules for use by REC:
	 * - REC_PMU_PAGES for PMU state
	 * - REC_SIMD_PAGES for SIMD state
	 * - REC_ATTEST_PAGES for 'rec_attest_data' structure
	 * - REC_SYSREGS_PAGES to store sysregs per plane
	 * - REC_ATTEST_BUFFER_PAGES for attestation buffer
	 */
	assert(r->num_rec_aux >= REC_NUM_PAGES);

	/*
	 * Assign base address for attestation heap, PMU, SIMD, attestation
	 * data, buffer and sysregs.
	 */
	aux_data = &r->aux_data;
	pmu = (struct pmu_state *)rec_aux;
	aux_data->simd_ctx = (struct simd_context *)
		((uintptr_t)pmu + REC_PMU_SIZE);
	aux_data->attest_data = (struct rec_attest_data *)
		((uintptr_t)aux_data->simd_ctx + REC_SIMD_SIZE);
	aux_data->sysregs = (STRUCT_TYPE sysreg_state *)
		((uintptr_t)aux_data->attest_data + REC_ATTEST_SIZE);
	used_aux_pages =
		((uintptr_t)aux_data->sysregs + REC_SYSREGS_SIZE -
			(uintptr_t)rec_aux) / GRANULE_SIZE;

	assert(used_aux_pages < r->num_rec_aux);

	/* Associate the PMU state of each plane with its sysregs structure */
	num_planes = rec_num_planes(r);
	for (unsigned int i = 0U; i < num_planes; i++) {
		aux_data->sysregs[i].pmu = &pmu[i];
	}

	rec_simd_state_init(r);
	rec_pmu_state_init(r);

	/* Use the rest of the aux pages for the app */
	granule_pa_count = r->num_rec_aux - used_aux_pages;

	for (size_t i = 0UL; i < granule_pa_count; ++i) {
		granule_pas[i] = granule_addr(r->g_aux[used_aux_pages + i]);
	}

	ret = app_new_instance(&r->attest_app_data,
		ATTESTATION_APP_ID,
		granule_pas,
		granule_pa_count,
		(void *)(SLOT_BUFFER_BASE_VA +
			(((unsigned long)SLOT_REC_AUX0 + used_aux_pages) * GRANULE_SIZE)),
		0);
	if (ret != 0) {
		panic();
	}

	/* Unmap auxiliary granules */
	buffer_rec_aux_unmap(rec_aux, r->num_rec_aux);
}

void rec_set_pending_op(struct rec *rec, unsigned int pending_op)
{
	/*
	 * Make sure that a pending operation can only be set if there is no
	 * operation pending currently
	 */
	assert((pending_op == REC_PENDING_NONE) || (rec->pending_op == REC_PENDING_NONE));

	rec->pending_op = pending_op;
}

void rec_update_pending_op(struct rec *rec, unsigned int pending_op)
{
	/*
	 * Make sure that a pending operation is already set, and
	 * REC_PENDING_NONE is not being set
	 */
	assert((pending_op != REC_PENDING_NONE) && (rec->pending_op != REC_PENDING_NONE));

	rec->pending_op = pending_op;
}

static unsigned long get_rsi_feature_register_0(struct rd *rd)
{
	unsigned long rsi_feat_reg0 = 0UL;

	if (rd->da_enabled) {
		rsi_feat_reg0 |= INPLACE(RSI_FEATURE_REGISTER_0_DA,
					 RSI_FEATURE_TRUE);
	}

	return rsi_feat_reg0;
}

static bool rec_mpidr_taken(struct mpidr_rec_map *mpidr_rec_map, unsigned long mpidr)
{
	return map_mpidr_to_rec(mpidr_rec_map, mpidr) != NULL;
}

static void rd_add_rec(struct rd *rd, struct rmi_rec_params *p,
			uintptr_t rec_addr, struct rd_aux *rd_aux)
{
	int ret __unused;
	unsigned long mpidr = p->mpidr;
	struct rec_map rec_map;

	rec_map.rec = rec_addr;

	ret = sarray_insert_rec_map(&rd_aux->mpidr_rec_map.rec_map_hnd, mpidr, &rec_map);
	assert(ret == 0);

	inc_rd_obj_map_epoch(rd);
}

/*
 * SRO handle callback for RMI_OP_CONTINUE during RMI_REC_CREATE.
 *
 * This callback is executed after all the necessary memory has been donated.
 */
static void rec_create_continue(unsigned long fid, struct smc_result *res)
{
	struct granule *g_rd;
	struct granule *g_rec;
	struct granule *rec_aux_granules[MAX_REC_AUX_GRANULES];
	struct granule *g_rec_params;
	struct rec *rec;
	struct rd *rd;
	struct rmi_rec_params rec_params;
	unsigned long ret;
	bool ns_access_ok;
	unsigned int num_rec_aux;
	unsigned long rd_addr, rec_addr, rec_params_addr;
	struct sro_context *sro = my_sro_ctx();
	struct rd_aux *rd_aux = NULL;

	assert(sro != NULL);
	assert(fid == SMC_RMI_OP_CONTINUE);
	(void)fid;

	/* Get the information from the SRO Context */
	rd_addr = sro->rec_ctx.rd_addr;
	rec_addr = sro->aux_op_ctx.obj_addr;
	rec_params_addr = sro->rec_ctx.rec_params_addr;

	/* Ensure all requested aux granules have been transferred */
	assert(sro->aux_op_ctx.total_transferred ==
			sro->aux_op_ctx.requested_aux_granules);
	num_rec_aux = (unsigned int)sro->aux_op_ctx.requested_aux_granules;

	g_rec_params = find_granule(rec_params_addr);
	if ((g_rec_params == NULL) ||
		(granule_unlocked_state(g_rec_params) != GRANULE_STATE_NS)) {

		/*
		 * The command failed, so request the host to reclaim
		 * the donated memory and return.
		 */
		sro_aux_op_start_reclaim(sro, res,
					 sro->aux_op_ctx.obj_addr,
					 false,
					 RMI_ERROR_INPUT,
					 sro->aux_op_ctx.total_transferred,
					 GRANULE_STATE_REC_AUX);
		return;
	}

	ns_access_ok = ns_buffer_read(SLOT_NS, g_rec_params, 0U,
				      sizeof(rec_params), &rec_params);

	if (!ns_access_ok) {
		/*
		 * The command failed, so request the host to reclaim
		 * the donated memory and return.
		 */
		sro_aux_op_start_reclaim(sro, res,
					 sro->aux_op_ctx.obj_addr,
					 false,
					 RMI_ERROR_INPUT,
					 sro->aux_op_ctx.total_transferred,
					 GRANULE_STATE_REC_AUX);
		return;
	}

	for (unsigned int i = 0U; i < num_rec_aux; i++) {
		unsigned long addr = sro->aux_op_ctx.aux_granules_pa[i];
		rec_aux_granules[i] = find_granule(addr);

		/* The granules should have been transitioned during donation */
		assert(rec_aux_granules[i] != NULL);
		assert(granule_unlocked_state(rec_aux_granules[i]) == GRANULE_STATE_REC_AUX);
	}

	if (!find_lock_two_granules(rec_addr,
				GRANULE_STATE_PARTIAL,
				&g_rec,
				rd_addr,
				GRANULE_STATE_RD,
				&g_rd)) {
		ret = RMI_ERROR_INPUT;
		goto out_free_aux;
	}

	/*
	 * Check if the maximum supported number of granules
	 * was already reached
	 */
	if (granule_refcount_read(g_rd) == REFCOUNT_MAX) {
		ret = RMI_ERROR_REALM;
		goto out_unlock;
	}

	rd = buffer_granule_map(g_rd, SLOT_RD);
	assert(rd != NULL);

	if (get_rd_state_locked(rd) != REALM_NEW) {
		ret = RMI_ERROR_REALM;
		goto out_unmap;
	}
	rd_aux = buffer_rd_aux_granules_map(&rd->aux_granules[0],
						rd->num_rd_aux);
	assert(rd_aux != NULL);

	if (!rec_mpidr_is_valid(rec_params.mpidr) ||
	    rec_mpidr_taken(&(rd_aux->mpidr_rec_map), rec_params.mpidr)) {
		ret = RMI_ERROR_INPUT;
		goto out_unmap;
	}

	/* Verify the auxiliary granule count with rd lock held */
	if (num_rec_aux != rd->num_rec_aux) {
		ret = RMI_ERROR_INPUT;
		goto out_unmap;
	}

	rec = buffer_granule_map_zeroed(g_rec, SLOT_REC);
	assert(rec != NULL);

	rec->g_rec = g_rec;
	rec->mpidr = rec_params.mpidr;

	rec->realm_info.num_aux_planes = rd->num_aux_planes;

	/* REC always boots in PLANE_0_ID plane */
	rec->active_plane_id = PLANE_0_ID;

	rec->num_rec_aux = num_rec_aux;

	rec_set_pending_op(rec, REC_PENDING_NONE);

	rec->realm_info.primary_s2_ctx = rd->s2_ctx[PRIMARY_S2_CTX_ID];
	rec->realm_info.g_rd = g_rd;
	rec->realm_info.pmu_enabled = rd->pmu_enabled;
	rec->realm_info.cached_rsi_feature_reg0 = get_rsi_feature_register_0(rd);
	rec->realm_info.pmu_num_ctrs = rd->pmu_num_ctrs;
	rec->realm_info.algorithm = rd->algorithm;
	rec->realm_info.simd_cfg = rd->simd_cfg;
	rec->realm_info.rtt_tree_pp = rd->rtt_tree_pp;
	rec->realm_info.rtt_s2ap_encoding = rd->rtt_s2ap_encoding;
	rec->da_enabled = rd->da_enabled;

	/* Copy addresses of auxiliary granules */
	(void)memcpy((void *)rec->g_aux, (const void *)rec_aux_granules,
			(size_t)(num_rec_aux * sizeof(struct granule *)));

	rec->runnable = (rec_params.flags & REC_PARAMS_FLAG_RUNNABLE) != 0UL;
	if (rec->runnable) {
		measurement_rec_params_measure(rd->measurement[RIM_MEASUREMENT_SLOT],
					       rd->algorithm,
					       &rec_params);
	}

	/*
	 * RD has a lock-free access from RMI_REC_DESTROY, hence increment
	 * refcount atomically.
	 */
	atomic_granule_get(g_rd);

	/*
	 * Map REC aux granules, initialize aux data and unmap REC aux
	 * granules.
	 */
	rec_aux_granules_init(rec);

	/* Initialize system registers */
	init_rec_regs(rec, &rec_params, rd);

	rd_add_rec(rd, &rec_params, rec_addr, rd_aux);

	buffer_unmap(rec);

	ret = RMI_SUCCESS;

out_unmap:
	if (rd_aux != NULL) {
		buffer_rd_aux_granules_unmap(rd_aux, rd->num_rd_aux);
	}
	buffer_unmap(rd);

out_unlock:
	granule_unlock(g_rd);
	if (ret == RMI_SUCCESS) {
		granule_unlock_transition(g_rec, GRANULE_STATE_REC);
	} else {
		granule_unlock(g_rec);

	}

out_free_aux:
	if (ret != RMI_SUCCESS) {
		/*
		 * The command failed, so request the host to reclaim
		 * the donated memory and return.
		 */
		sro_aux_op_start_reclaim(sro, res,
					 rec_addr,
					 false,
					 ret,
					 sro->aux_op_ctx.total_transferred,
					 GRANULE_STATE_REC_AUX);
	} else {
		/* Finish the command with SUCCESS */
		res->x[0] = ret;
		assert(res->x[2] == 0UL);
		assert(res->x[1] == 0UL);
	}
}

void rec_continue_handler(unsigned long fid, struct smc_result *res)
{
	/* List of handlers that can be invoked from here */
	const sro_handle_cb sro_callbacks[] = {
		[SRO_OBJ_MEM_RECLAIM] = sro_obj_memory_reclaim,
		[SRO_OBJ_MEM_DONATE] = sro_obj_memory_donate,
		[SRO_OBJ_CREATE_CONTINUE] = rec_create_continue,
		[SRO_OBJ_DESTROY_FINISH] = sro_aux_op_reclaim_finish
	};
	struct sro_context *sro = my_sro_ctx();

	assert(sro != NULL);
	assert((size_t)(sro->aux_op_ctx.cb_id) < ARRAY_SIZE(sro_callbacks));

	sro_callbacks[sro->aux_op_ctx.cb_id](fid, res);
}

void smc_rec_create(unsigned long rd_addr,
		    unsigned long rec_addr,
		    unsigned long rec_params_addr,
		    struct smc_result *res)
{
	struct sro_context *sro;
	unsigned long ret;

	struct granule *gr = find_lock_granule(rec_addr, GRANULE_STATE_DELEGATED);
	if (gr == NULL) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	/*
	 * Reserve an SRO context handle.
	 * The memory is not required to be contiguous.
	 * The operaton cannot cancel.
	 */
	ret = sro_ctx_reserve(SMC_RMI_REC_CREATE, MAX_REC_AUX_GRANULES * GRANULE_SIZE,
			      false, false,
			      SMC_RMI_OP_MEM_DONATE);
	if (ret != RMI_SUCCESS) {
		granule_unlock(gr);
		res->x[0] = ret;
		return;
	}

	/* Transition to PARTIAL state while SRO flow is ongoing */
	granule_unlock_transition(gr, GRANULE_STATE_PARTIAL);

	sro = my_sro_ctx();
	assert(sro != NULL);

	/*
	 * The first step of REC_CREATE will be to request memory for
	 * the aux granules.
	 */
	/* Initialize the sro context for the command */
	sro->rec_ctx.rd_addr = rd_addr;
	sro->rec_ctx.rec_params_addr = rec_params_addr;
	sro_aux_op_init_donate(sro, res, rec_addr,
			       (unsigned long)MAX_REC_AUX_GRANULES,
			       GRANULE_STATE_REC_AUX);
}

void smc_rec_destroy(unsigned long rec_addr, struct smc_result *res)
{
	struct granule *g_rec;
	struct granule *g_rd;
	struct rec *rec;
	struct rd *rd;
	struct rd_aux *rd_aux;
	struct sro_context *sro;
	unsigned long mpidr;
	int ret;
	unsigned long ctx_reserved;

	/*
	 * Reserve the context here before any other operation so we return
	 * error if no contexts available. Otherwise, by reserving the context
	 * later, we could end up with a partially destroyed REC, for instance
	 * if find_locl_unused_granule() below passes but there are no free
	 * contexts later.
	 *
	 * The memory operation is not required to be contiguous.
	 * The operation cannot be cancelled.
	 */
	ctx_reserved = sro_ctx_reserve(SMC_RMI_REC_DESTROY, 0UL, false, false,
				      SMC_RMI_OP_MEM_RECLAIM);
	if (ctx_reserved != RMI_SUCCESS) {
		res->x[0] = ctx_reserved;
		return;
	}

	/* REC should not be destroyed if refcount != 0 */
	ret = find_lock_unused_granule(rec_addr, GRANULE_STATE_REC, &g_rec);
	if (ret != 0) {
		switch (ret) {
		case -EINVAL:
			sro_ctx_release();
			res->x[0] = RMI_ERROR_INPUT;
			return;
		default:
			assert(ret == -EBUSY);
			sro_ctx_release();
			res->x[0] = RMI_ERROR_REC;
			return;
		}
	}

	rec = buffer_granule_map(g_rec, SLOT_REC);
	assert(rec != NULL);

	g_rd = rec->realm_info.g_rd;
	mpidr = rec->mpidr;

	/* Clean up the attestation app spawned by the REC */
	(void)attest_app_delete(&rec->attest_app_data);

	/* Memory to reclaim */
	sro = my_sro_ctx();
	assert(sro != NULL);

	unsigned long num_rec_aux = rec->num_rec_aux;

	for (unsigned int i = 0U; i < num_rec_aux; i++) {
		sro->aux_op_ctx.aux_granules_pa[i] = granule_addr(rec->g_aux[i]);
	}

	buffer_unmap(rec);

	granule_unlock_transition(g_rec, GRANULE_STATE_PARTIAL);

	/*
	 * REC is now unlocked, but the RD refcount for it is still held. So we
	 * can be sure that the RD we are locking here is the same that
	 * the REC was created in.
	 */
	granule_lock(g_rd, GRANULE_STATE_RD);
	rd = buffer_granule_map(g_rd, SLOT_RD);
	assert(rd != NULL);

	rd_aux = buffer_rd_aux_granules_map(
		&rd->aux_granules[0], rd->num_rd_aux);
	assert(rd_aux != NULL);

	/* NOLINTNEXTLINE(clang-analyzer-deadcode.DeadStores) */
	ret = sarray_delete_rec_map(&rd_aux->mpidr_rec_map.rec_map_hnd,
				    mpidr, NULL);
	assert(ret == 0);

	inc_rd_obj_map_epoch(rd);
	buffer_rd_aux_granules_unmap(rd_aux, rd->num_rd_aux);
	buffer_unmap(rd);
	granule_unlock(g_rd);

	/*
	 * Decrement refcount. The refcount should be balanced before
	 * RMI_REC_DESTROY returns, and until this occurs a transient
	 * over-estimate of the refcount (in-between the unlock and decreasing
	 * the refcount) is legitimate.
	 * We use release semantic here to match acquire semantic for refcount
	 * in RMI_REALM_DESTROY.
	 */
	atomic_granule_put_release(g_rd);

	sro_aux_op_start_reclaim(sro, res,
				 rec_addr,
				 true,
				 RMI_SUCCESS, num_rec_aux,
				 GRANULE_STATE_REC_AUX);
}

/*
 * Lock and map a calling REC with a pending PSCI request.
 *
 * On success, the caller must unmap the REC and unlock @g_calling_rec.
 */
static struct rec *find_lock_map_psci_calling_rec(unsigned long calling_rec_addr,
						  struct granule **g_calling_rec)
{
	struct granule *g_rec;
	struct rec *calling_rec;

	assert(g_calling_rec != NULL);

	g_rec = find_lock_granule(calling_rec_addr, GRANULE_STATE_REC);
	if (g_rec == NULL) {
		return NULL;
	}

	/* Synchronize with REC exit before accessing mutable REC state. */
	if (granule_refcount_read_acquire(g_rec) != 0U) {
		granule_unlock(g_rec);
		return NULL;
	}

	calling_rec = buffer_granule_map(g_rec, SLOT_REC);
	assert(calling_rec != NULL);

	/* The cached target address is valid only for a pending PSCI request. */
	if (calling_rec->pending_op != REC_PENDING_PSCI_COMPLETE) {
		buffer_unmap(calling_rec);
		granule_unlock(g_rec);
		return NULL;
	}

	*g_calling_rec = g_rec;
	return calling_rec;
}

/*
 * Complete a denied PSCI request when the target REC no longer exists at the
 * address cached by the calling REC.
 */
static unsigned long smc_psci_complete_denied(unsigned long calling_rec_addr)
{
	struct granule *g_calling_rec;
	struct rec *calling_rec;
	unsigned long ret;

	calling_rec = find_lock_map_psci_calling_rec(calling_rec_addr,
						     &g_calling_rec);
	if (calling_rec == NULL) {
		return RMI_ERROR_INPUT;
	}

	ret = psci_complete_denied_request(calling_rec);

	buffer_unmap(calling_rec);
	granule_unlock(g_calling_rec);

	return ret;
}

void smc_psci_complete(unsigned long calling_rec_addr,
		       unsigned long status,
		       struct smc_result *res)
{
	struct granule *g_calling_rec, *g_target_rec;
	struct rec  *calling_rec, *target_rec;
	unsigned long target_rec_addr;
	unsigned long ret;
	void *target_rec_aux;

	if (!GRANULE_ALIGNED(calling_rec_addr)) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	calling_rec = find_lock_map_psci_calling_rec(calling_rec_addr,
						     &g_calling_rec);
	if (calling_rec == NULL) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	target_rec_addr = calling_rec->target_rec_addr;

	buffer_unmap(calling_rec);
	granule_unlock(g_calling_rec);

	if (!find_lock_two_granules(calling_rec_addr,
					GRANULE_STATE_REC,
					&g_calling_rec,
					target_rec_addr,
					GRANULE_STATE_REC,
					&g_target_rec)) {
		res->x[0] = (status == PSCI_RETURN_DENIED) ?
				smc_psci_complete_denied(calling_rec_addr) :
				RMI_ERROR_INPUT;
		return;
	}

	/*
	 * The access to a REC from RMI_REC_ENTER is only protected by the
	 * reference counter. Here, we may access the volatile (non constant)
	 * members of REC structure (such as rec->running) only if the counter
	 * is zero.
	 *
	 * This check is needed again here because rec lock is released and
	 * locked again and REC could have started running in that window.
	 */
	if (granule_refcount_read_acquire(g_calling_rec) != 0U) {
		/*
		 * The `calling` REC is running on another PE and therefore it
		 * may not have a pending PSCI request.
		 */
		ret = RMI_ERROR_INPUT;
		goto out_unlock;
	}

	calling_rec = buffer_granule_map(g_calling_rec, SLOT_REC);
	assert(calling_rec != NULL);

	target_rec = buffer_granule_map(g_target_rec, SLOT_REC2);
	assert(target_rec != NULL);

	/*
	 * The cached target address may have been reused while the calling REC
	 * lock was released, so confirm that this is still the requested REC.
	 */
	if (!psci_target_rec_matches(calling_rec, target_rec)) {
		ret = (status == PSCI_RETURN_DENIED) ?
			psci_complete_denied_request(calling_rec) : RMI_ERROR_INPUT;
		goto out_unmap_recs;
	}

	/* Reuse the REC_AUX slots for mapping Aux granules for target REC */
	target_rec_aux = buffer_rec_aux_granules_map(target_rec->g_aux,
						     target_rec->num_rec_aux);

	ret = psci_complete_request(calling_rec, target_rec, status);
	buffer_rec_aux_unmap(target_rec_aux, target_rec->num_rec_aux);

out_unmap_recs:
	buffer_unmap(target_rec);
	buffer_unmap(calling_rec);
out_unlock:
	granule_unlock(g_calling_rec);
	granule_unlock(g_target_rec);

	res->x[0] = ret;
}
