/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch.h>
#include <arch_features.h>
#include <buffer.h>
#include <debug.h>
#include <gic.h>
#include <granule.h>
#include <measurement.h>
#include <psci.h>
#include <realm.h>
#include <rec.h>
#include <s2tt.h>
#include <smc-handler.h>
#include <smc-rmi.h>
#include <smc.h>
#include <stdbool.h>
#include <stddef.h>
#include <string.h>

static void init_rec_sysregs(struct rec *rec, unsigned long rec_mpidr)
{
	/* Set non-zero values only */
	rec->sysregs.pmcr_el0 = rec->realm_info.pmu_enabled ?
				PMCR_EL0_INIT_RESET : PMCR_EL0_INIT;

	rec->sysregs.sctlr_el1 = SCTLR_EL1_FLAGS;
	rec->sysregs.mdscr_el1 = MDSCR_EL1_TDCC_BIT;
	rec->sysregs.vmpidr_el2 = rec_mpidr_to_mpidr(rec_mpidr) | VMPIDR_EL2_RES1;
	rec->sysregs.cnthctl_el2 = CNTHCTL_EL2_NO_TRAPS;
	rec->sysregs.cptr_el2 = CPTR_EL2_VHE_INIT;
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

static unsigned long realm_vtcr_ps(unsigned int parange)
{
	switch (parange) {
	case PARANGE_0001_WIDTH:
		return VTCR_PS_36;
	case PARANGE_0010_WIDTH:
		return VTCR_PS_40;
	case PARANGE_0011_WIDTH:
		return VTCR_PS_42;
	case PARANGE_0100_WIDTH:
		return VTCR_PS_44;
	case PARANGE_0101_WIDTH:
		return VTCR_PS_48;
	case PARANGE_0110_WIDTH:
		return VTCR_PS_52;
	case PARANGE_0000_WIDTH:
	default:
		return VTCR_PS_32;
	}
}

static unsigned long realm_vtcr(struct rd *rd)
{
	unsigned long t0sz, sl0;
	unsigned long vtcr = is_feat_vmid16_present() ?
				(VTCR_FLAGS | VTCR_VS) : VTCR_FLAGS;
	unsigned int parange = arch_feat_get_pa_width();
	int s2_starting_level = realm_rtt_starting_level(rd);
	bool lpa2 = rd->s2_ctx.enable_lpa2;

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
	vtcr |= realm_vtcr_ps(parange);

	if (lpa2 == true) {
		if (s2_starting_level == -1) {
			vtcr |= VCTR_SL2_4K_LM1;
		}
		vtcr |= VTCR_DS_52BIT;
	}

	return vtcr;
}

static void init_common_sysregs(struct rec *rec, struct rd *rd)
{
	unsigned long mdcr_el2_val = read_mdcr_el2();
	bool lpa2 = rd->s2_ctx.enable_lpa2;

	/* Set non-zero values only */
	rec->common_sysregs.hcr_el2 = HCR_REALM_FLAGS;
	rec->common_sysregs.vtcr_el2 =  realm_vtcr(rd);
	rec->common_sysregs.vttbr_el2 = (granule_addr(rd->s2_ctx.g_rtt) &
					MASK(TTBRx_EL2_BADDR));
	if (lpa2 == true) {
		rec->common_sysregs.vttbr_el2 &= ~MASK(TTBRx_EL2_BADDR_MSB_LPA2);
		rec->common_sysregs.vttbr_el2 |=
			INPLACE(TTBRx_EL2_BADDR_MSB_LPA2,
						EXTRACT(EL2_BADDR_MSB_LPA2,
							granule_addr(rd->s2_ctx.g_rtt)));
	}

	rec->common_sysregs.vttbr_el2 |= INPLACE(VTTBR_EL2_VMID, rd->s2_ctx.vmid);

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
	}

	rec->common_sysregs.mdcr_el2 = mdcr_el2_val;
}

static void init_rec_regs(struct rec *rec,
			  struct rmi_rec_params *rec_params,
			  struct rd *rd)
{
	unsigned int i;

	/*
	 * We only need to set non-zero values here because we're intializing
	 * data structures in the rec granule which was just converted from
	 * the DELEGATED state to REC state, and we can rely on the RMM
	 * invariant that DELEGATED granules are always zero-filled.
	 */

	for (i = 0U; i < REC_CREATE_NR_GPRS; i++) {
		rec->regs[i] = rec_params->gprs[i];
	}

	rec->pc = rec_params->pc;
	rec->pstate = SPSR_EL2_MODE_EL1h |
		      SPSR_EL2_nRW_AARCH64 |
		      SPSR_EL2_F_BIT |
		      SPSR_EL2_I_BIT |
		      SPSR_EL2_A_BIT |
		      SPSR_EL2_D_BIT;

	init_rec_sysregs(rec, rec_params->mpidr);
	init_common_sysregs(rec, rd);
}

/*
 * This function will only be invoked when the REC create fails
 * or when REC is being destroyed. Hence the REC will not be in
 * use when this function is called and therefore no lock is
 * acquired before its invocation.
 */
static void free_rec_aux_granules(struct granule *rec_aux[],
				  unsigned int cnt, bool scrub)
{
	for (unsigned int i = 0U; i < cnt; i++) {
		struct granule *g_rec_aux = rec_aux[i];

		granule_lock(g_rec_aux, GRANULE_STATE_REC_AUX);
		if (scrub) {
			buffer_granule_memzero(g_rec_aux,
			   (enum buffer_slot)((unsigned int)SLOT_REC_AUX0 + i));
		}
		granule_unlock_transition(g_rec_aux, GRANULE_STATE_DELEGATED);
	}
}

/* Initialize REC simd state */
static void rec_simd_state_init(struct rec *r)
{
	int __unused retval;

	retval = simd_context_init(SIMD_OWNER_REL1, r->aux_data.simd_ctx,
				   &r->realm_info.simd_cfg);
	assert(retval == 0);
}

/*
 * Initializes granule pages that are used for attestation heap, PMU and SIMD.
 * As part of initialization this function maps and unmaps the REC aux granules.
 */
static void rec_aux_granules_init(struct rec *r)
{
	void *rec_aux;
	struct rec_aux_data *aux_data;

	/* Map auxiliary granules */
	rec_aux = buffer_rec_aux_granules_map(r->g_aux, r->num_rec_aux);
	assert(rec_aux != NULL);

	/*
	 * Ensure we have enough aux granules for use by REC:
	 * - REC_HEAP_PAGES for MbedTLS heap
	 * - REC_PMU_PAGES for PMU state
	 * - REC_SIMD_PAGES for SIMD state
	 * - REC_ATTEST_PAGES for 'rec_attest_data' structure
	 * - REC_ATTEST_BUFFER_PAGES for attestation buffer
	 */
	assert(r->num_rec_aux >= REC_NUM_PAGES);

	/*
	 * Assign base address for attestation heap, PMU, SIMD, attestation
	 * data and buffer.
	 */
	aux_data = &r->aux_data;
	aux_data->attest_heap_buf = (uint8_t *)rec_aux;
	aux_data->pmu = (struct pmu_state *)
		((uintptr_t)aux_data->attest_heap_buf + REC_HEAP_SIZE);
	aux_data->simd_ctx = (struct simd_context *)
		((uintptr_t)aux_data->pmu + REC_PMU_SIZE);
	aux_data->attest_data = (struct rec_attest_data *)
		((uintptr_t)aux_data->simd_ctx + REC_SIMD_SIZE);
	aux_data->cca_token_buf = (uintptr_t)aux_data->attest_data +
		REC_ATTEST_SIZE;

	rec_simd_state_init(r);

	/* Unmap auxiliary granules */
	buffer_rec_aux_unmap(rec_aux, r->num_rec_aux);
}

unsigned long smc_rec_create(unsigned long rd_addr,
			     unsigned long rec_addr,
			     unsigned long rec_params_addr)
{
	struct granule *g_rd;
	struct granule *g_rec;
	struct granule *rec_aux_granules[MAX_REC_AUX_GRANULES];
	struct granule *g_rec_params;
	struct rec *rec;
	struct rd *rd;
	struct rmi_rec_params rec_params;
	unsigned long rec_idx;
	unsigned char new_rec_state = GRANULE_STATE_DELEGATED;
	unsigned long ret;
	bool ns_access_ok;
	unsigned int num_rec_aux;

	g_rec_params = find_granule(rec_params_addr);
	if ((g_rec_params == NULL) ||
		(granule_unlocked_state(g_rec_params) != GRANULE_STATE_NS)) {
		return RMI_ERROR_INPUT;
	}

	ns_access_ok = ns_buffer_read(SLOT_NS, g_rec_params, 0U,
				      sizeof(rec_params), &rec_params);

	if (!ns_access_ok) {
		return RMI_ERROR_INPUT;
	}

	/* coverity[uninit_use:SUPPRESS] */
	num_rec_aux = (unsigned int)rec_params.num_aux;
	if (num_rec_aux > MAX_REC_AUX_GRANULES) {
		return RMI_ERROR_INPUT;
	}

	/* Loop through rec_aux_granules and transit them */
	for (unsigned int i = 0U; i < num_rec_aux; i++) {
		struct granule *g_rec_aux = find_lock_granule(
						rec_params.aux[i],
						GRANULE_STATE_DELEGATED);
		if (g_rec_aux == NULL) {
			/* Unlock granules already locked before freeing them */
			for (unsigned int k = 0U; k < i; k++) {
				granule_unlock(rec_aux_granules[k]);
			}
			free_rec_aux_granules(rec_aux_granules, i, false);
			return RMI_ERROR_INPUT;
		}
		granule_unlock_transition(g_rec_aux, GRANULE_STATE_REC_AUX);
		rec_aux_granules[i] = g_rec_aux;
	}

	if (!find_lock_two_granules(rec_addr,
				GRANULE_STATE_DELEGATED,
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

	rec = buffer_granule_map(g_rec, SLOT_REC);
	assert(rec != NULL);

	rd = buffer_granule_map(g_rd, SLOT_RD);
	assert(rd != NULL);

	if (get_rd_state_locked(rd) != REALM_NEW) {
		ret = RMI_ERROR_REALM;
		goto out_unmap;
	}

	rec_idx = get_rd_rec_count_locked(rd);
	if (!rec_mpidr_is_valid(rec_params.mpidr) ||
	   (rec_idx != rec_mpidr_to_idx(rec_params.mpidr))) {
		ret = RMI_ERROR_INPUT;
		goto out_unmap;
	}

	/* Verify the auxiliary granule count with rd lock held */
	if (num_rec_aux != rd->num_rec_aux) {
		ret = RMI_ERROR_INPUT;
		goto out_unmap;
	}

	rec->g_rec = g_rec;
	rec->rec_idx = rec_idx;

	init_rec_regs(rec, &rec_params, rd);
	gic_cpu_state_init(&rec->sysregs.gicstate);

	/* Copy addresses of auxiliary granules */
	(void)memcpy(rec->g_aux, rec_aux_granules,
			num_rec_aux * sizeof(struct granule *));

	rec->num_rec_aux = num_rec_aux;

	rec->realm_info.s2_ctx = rd->s2_ctx;
	rec->realm_info.g_rd = g_rd;
	rec->realm_info.pmu_enabled = rd->pmu_enabled;
	rec->realm_info.pmu_num_ctrs = rd->pmu_num_ctrs;
	rec->realm_info.algorithm = rd->algorithm;
	rec->realm_info.simd_cfg = rd->simd_cfg;

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
	new_rec_state = GRANULE_STATE_REC;

	/*
	 * Map REC aux granules, initialize aux data and unmap REC aux
	 * granules.
	 */
	rec_aux_granules_init(rec);

	set_rd_rec_count(rd, rec_idx + 1U);

	ret = RMI_SUCCESS;

out_unmap:
	buffer_unmap(rd);
	buffer_unmap(rec);

out_unlock:
	granule_unlock(g_rd);
	granule_unlock_transition(g_rec, new_rec_state);

out_free_aux:
	if (ret != RMI_SUCCESS) {
		free_rec_aux_granules(rec_aux_granules, num_rec_aux, false);
	}
	return ret;
}

unsigned long smc_rec_destroy(unsigned long rec_addr)
{
	struct granule *g_rec;
	struct granule *g_rd;
	struct rec *rec;
	int res;

	/* REC should not be destroyed if refcount != 0 */
	res = find_lock_unused_granule(rec_addr, GRANULE_STATE_REC, &g_rec);
	if (res != 0) {
		switch (res) {
		case -EINVAL:
			return RMI_ERROR_INPUT;
		default:
			assert(res == -EBUSY);
			return RMI_ERROR_REC;
		}
	}

	rec = buffer_granule_map(g_rec, SLOT_REC);
	assert(rec != NULL);

	g_rd = rec->realm_info.g_rd;

	/* Free and scrub the auxiliary granules */
	free_rec_aux_granules(rec->g_aux, rec->num_rec_aux, true);

	granule_memzero_mapped(rec);
	buffer_unmap(rec);

	granule_unlock_transition(g_rec, GRANULE_STATE_DELEGATED);

	/*
	 * Decrement refcount. The refcount should be balanced before
	 * RMI_REC_DESTROY returns, and until this occurs a transient
	 * over-estimate of the refcount (in-between the unlock and decreasing
	 * the refcount) is legitimate.
	 * We use release semantic here to match acquire semantic for refcount
	 * in RMI_REALM_DESTROY.
	 */
	atomic_granule_put_release(g_rd);

	return RMI_SUCCESS;
}

void smc_rec_aux_count(unsigned long rd_addr, struct smc_result *res)
{
	unsigned int num_rec_aux;
	struct granule *g_rd;
	struct rd *rd;

	g_rd = find_lock_granule(rd_addr, GRANULE_STATE_RD);
	if (g_rd == NULL) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	rd = buffer_granule_map(g_rd, SLOT_RD);
	assert(rd != NULL);

	num_rec_aux = rd->num_rec_aux;
	buffer_unmap(rd);
	granule_unlock(g_rd);

	res->x[0] = RMI_SUCCESS;
	res->x[1] = (unsigned long)num_rec_aux;
}

unsigned long smc_psci_complete(unsigned long calling_rec_addr,
				unsigned long target_rec_addr,
				unsigned long status)
{
	struct granule *g_calling_rec, *g_target_rec;
	struct rec  *calling_rec, *target_rec;
	unsigned long ret;

	if (!GRANULE_ALIGNED(calling_rec_addr)) {
		return RMI_ERROR_INPUT;
	}

	if (!GRANULE_ALIGNED(target_rec_addr)) {
		return RMI_ERROR_INPUT;
	}

	if (!find_lock_two_granules(calling_rec_addr,
					GRANULE_STATE_REC,
					&g_calling_rec,
					target_rec_addr,
					GRANULE_STATE_REC,
					&g_target_rec)) {
		return RMI_ERROR_INPUT;
	}

	/*
	 * The access to a REC from RMI_REC_ENTER is only protected by the
	 * reference counter. Here, we may access the volatile (non constant)
	 * members of REC structure (such as rec->running) only if the counter
	 * is zero.
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

	ret = psci_complete_request(calling_rec, target_rec, status);

	buffer_unmap(target_rec);
	buffer_unmap(calling_rec);
out_unlock:
	granule_unlock(g_calling_rec);
	granule_unlock(g_target_rec);

	return ret;
}
