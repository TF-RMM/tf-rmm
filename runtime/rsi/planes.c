/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch_features.h>
#include <assert.h>
#include <buffer.h>
#include <gic.h>
#include <granule.h>
#include <planes.h>
#include <realm.h>
#include <rec.h>
#include <rsi-handler.h>
#include <run.h>
#include <simd.h>
#include <smc-rsi.h>
#include <timers.h>
#include <utils_def.h>

static void copy_state_from_plane_entry(struct rec_plane *plane,
					STRUCT_TYPE sysreg_state *sysregs,
					struct rsi_plane_enter *entry,
					bool restore_gic)
{
	for (unsigned int i = 0; i < RSI_PLANE_NR_GPRS; i++) {
		plane->regs[i] = entry->gprs[i];
	}

	plane->pc = entry->pc;
	plane->pstate = entry->pstate;
	if (restore_gic) {
		gic_copy_state_from_entry(&sysregs->gicstate,
			(unsigned long *)&entry->gicv3_lrs, entry->gicv3_hcr);
	}
}

void handle_rsi_plane_enter(struct rec *rec, struct rsi_result *res)
{
	struct rec_plane *plane_0 = rec_plane_0(rec);
	STRUCT_TYPE sysreg_state *sysreg_0 = rec_plane_0_sysregs(rec);
	struct rec_plane *plane_n;
	STRUCT_TYPE sysreg_state *sysreg_n;
	unsigned long plane_idx = plane_0->regs[1];
	unsigned long run_ipa = plane_0->regs[2];
	struct granule *llt = NULL;
	struct rsi_plane_run *run = NULL;
	bool restore_gic = true;

	res->action = UPDATE_REC_RETURN_TO_REALM;

	/* This command can only be executed from Plane 0 */
	assert(rec_is_plane_0_active(rec));

	if ((plane_idx == PLANE_0_ID) ||
	    (plane_idx >= rec_num_planes(rec)) ||
	    (!addr_in_rec_par(rec, run_ipa))) {
		res->smc_res.x[0] = RSI_ERROR_INPUT;
		return;
	}

	if (!realm_mem_lock_map(rec, run_ipa, (void **)&run, &llt, res)) {
		/* In case of failure res is updated */
		return;
	}

	assert((run != NULL) && (llt != NULL));

	/* Save Plane 0 state to REC */
	save_realm_state(rec, plane_0, sysreg_0);

	/*
	 * Check if the primary plane has timers that we need to be notified of
	 */
	multiplex_el2_timer(rec);

	/* Activate plane N */
	plane_n = rec_activate_plane_n(rec, (unsigned int)plane_idx);
	sysreg_n = rec_active_plane_sysregs(rec);

	if ((run->enter.flags & RSI_PLANE_ENTER_FLAGS_OWN_GIC) != 0UL) {
		rec->gic_owner = (unsigned int)plane_idx;

		/* Transfer the GIC status from Plane 0 to the new owner */
		gic_copy_state(&sysreg_n->gicstate,
			       &sysreg_0->gicstate);
		restore_gic = false;
	}

	/* Copy target Plane state from entry structure to REC */
	copy_state_from_plane_entry(plane_n, sysreg_n, &run->enter, restore_gic);

	/* Initialize trap control bits */
	sysreg_n->hcr_el2 = rec->common_sysregs.hcr_el2;

	if ((run->enter.flags & RSI_PLANE_ENTER_FLAGS_TRAP_WFI) != RSI_NO_TRAP) {
		sysreg_n->hcr_el2 |= HCR_TWI;
	}

	if ((run->enter.flags & RSI_PLANE_ENTER_FLAGS_TRAP_WFE) != RSI_NO_TRAP) {
		sysreg_n->hcr_el2 |= HCR_TWE;
	}

	if ((run->enter.flags & RSI_PLANE_ENTER_FLAGS_TRAP_SIMD) != RSI_NO_TRAP) {
		SIMD_DISABLE_ALL_CPTR_FLAGS((sysreg_n->cptr_el2));
	} else {
		/* Propagate cptr_el2 configuration from P0 to PN */
		sysreg_n->cptr_el2 = sysreg_0->cptr_el2;
	}

	plane_n->trap_simd =
		((run->enter.flags & RSI_PLANE_ENTER_FLAGS_TRAP_SIMD) != RSI_NO_TRAP);

	plane_n->trap_hc =
		((run->enter.flags & RSI_PLANE_ENTER_FLAGS_TRAP_HC) != RSI_NO_TRAP);

	/* Change active Plane */
	res->action = PLANE_CHANGED_RETURN_TO_REALM;

	/* Restore target Plane from REC */
	restore_realm_state(rec, plane_n, sysreg_n);

	/* Unmap Realm data granule */
	buffer_unmap(run);

	/* Unlock last level RTT */
	granule_unlock(llt);
}

/* Bit definitions for the index used for pmvcntr and pvmtyper registers */
#define REG_IDX_SHIFT		UL(0)
#define REG_IDX_WIDTH		UL(5)
#define REG_IDX_MASK		MASK(REG_IDX)

/*
 * Perform a RW access to the PMU PMEV register @reg_id stored in the
 * sysreg context @sysreg.
 */
static bool access_pmu_pmev_el0(struct rec *rec,
				struct rec_plane *plane,
				struct rsi_result *res,
				bool read)
{
	unsigned long plane_id = plane->regs[1];
	unsigned long sysreg_id = plane->regs[2];
	STRUCT_TYPE sysreg_state *sysregs = REC_GET_SYSREGS_FROM_AUX(rec, plane_id);

	assert(sysregs->pmu != NULL);

	if (EXTRACT(RSI_SYSREG_ADDR_KVM_SYSREG128, sysreg_id) != 0UL) {
		/*  No 128-bit registers allowed here */
		return false;
	}

	/*
	 * Generate the index for the pmev array of registers using sysreg.
	 * As per the Arm ARM, the index is stored in CRm and Op2 as follows:
	 *
	 * IDX = [CRm[1:0], Op2[2:0]]
	 */
	unsigned long reg_idx = (sysreg_id & ~RSI_SYSREG_PMEV_MASK);

	reg_idx = (((EXTRACT(RSI_SYSREG_ADDR_KVM_CRM, reg_idx) << RSI_SYSREG_ADDR_KVM_OP2_WIDTH)
		   | (EXTRACT(RSI_SYSREG_ADDR_KVM_OP2, reg_idx))) & REG_IDX_MASK);

	if (reg_idx < UL(PMU_N_PMEV_REGS)) {
		struct pmev_regs *pmev_regs = &(sysregs->pmu->pmev_regs[reg_idx]);

		if ((sysreg_id & RSI_SYSREG_PMEV_MASK) == RSI_SYSREG_PMEVCNTR_MASK) {
			if (read) {
				res->smc_res.x[1] = pmev_regs->pmevcntr_el0;
			} else {
				pmev_regs->pmevcntr_el0 = plane->regs[3];
			}
			return true;
		}

		if ((sysreg_id & RSI_SYSREG_PMEV_MASK) == RSI_SYSREG_PMEVTYPER_MASK) {
			if (read) {
				res->smc_res.x[1] = pmev_regs->pmevtyper_el0;
			} else {
				pmev_regs->pmevtyper_el0 = plane->regs[3];
			}
			return true;
		}
	}

	return false;
}

static void pmu_sysreg_access(struct rsi_result *res, unsigned long *sysreg,
			      unsigned long val, bool read)
{
	if (read) {
		res->smc_res.x[1] = *sysreg;
	} else {
		*sysreg = val;
	}
}

/*
 * Perform a RW access to the PMU register @reg_id stored in the
 * sysreg context @sysreg.
 */
static bool access_pmu_sysregs(struct rec *rec,
				struct rec_plane *plane,
				struct rsi_result *res,
				bool read)
{
	unsigned long plane_id = plane->regs[1];
	unsigned long sysreg_id = plane->regs[2];
	unsigned long val = plane->regs[3];
	STRUCT_TYPE sysreg_state *sysregs = REC_GET_SYSREGS_FROM_AUX(rec, plane_id);

	if (EXTRACT(RSI_SYSREG_ADDR_KVM_SYSREG128, sysreg_id) != 0UL) {
		/*  No 128-bit registers allowed here */
		return false;
	}

/* cppcheck-suppress misra-c2012-20.7 */
#define PMU_SYSREG_ACCESS_CASE(_sysreg)						\
	case RSI_SYSREG_KVM_ID_##_sysreg:					\
		do {								\
			assert(sysregs->pmu != NULL);				\
			pmu_sysreg_access(res, &sysregs->pmu->_sysreg,		\
					  val, read);				\
			return true;						\
		} while (false)

	switch (sysreg_id) {
		PMU_SYSREG_ACCESS_CASE(pmcr_el0);
		PMU_SYSREG_ACCESS_CASE(pmccfiltr_el0);
		PMU_SYSREG_ACCESS_CASE(pmccntr_el0);
		PMU_SYSREG_ACCESS_CASE(pmcntenset_el0);
		PMU_SYSREG_ACCESS_CASE(pmovsset_el0);
		PMU_SYSREG_ACCESS_CASE(pmselr_el0);
		PMU_SYSREG_ACCESS_CASE(pmuserenr_el0);

		PMU_SYSREG_ACCESS_CASE(pmintenset_el1);
	default:
		return false;
	}

	/* coverity[misra_c_2012_rule_2_1_violation:SUPPRESS] */
	return false;
}

static bool sysreg_access(struct rsi_result *res, unsigned long *sysreg,
			  struct reg128 *val,  bool read, bool is_128b)
{
	if (is_128b) {
		/* No 128-bit registers allowed here */
		return false;
	}

	if (read) {
		res->smc_res.x[1] = *sysreg;
		res->smc_res.x[2] = 0UL;
	} else {
		*sysreg = val->lo;
	}

	return true;
}

/*
 * Helper function to access 128-bit registers either as 128-bit or 64-bit
 * wide registers.
 *
 * As per the spec, a 64-bit access to a register will not alter its
 * 64MSBs. A 64-bit read will return 0 on the MSBs.
 *
 * It is the caller responsibility to validate that is_128 is never 'true'
 * if FEAT_SYSREG128 is not supported.
 */
static bool sysreg_access_128b(struct rsi_result *res, struct reg128 *sysreg,
			       struct reg128 *val, bool read, bool is_128b)
{
	/* 128-bit access only allowed if FEAT_SYSREG128 is present */
	assert(is_feat_sysreg128_present() || !is_128b);

	if (read) {
		res->smc_res.x[1] = sysreg->lo;
		res->smc_res.x[2] = ((is_128b) ? sysreg->hi : 0UL);
	} else {
		/* sysreg->hi will only be updated for 128-Bit access */
		sysreg->hi = ((is_128b) ? val->hi : sysreg->hi);
		sysreg->lo = val->lo;
	}

	return true;
}

/*
 * Perform a RW access to a given sysreg in a given plane.
 *
 * This function does not make any sanitization or checks on
 * the arguments so it expects all of them to be valid.
 */
static bool access_plane_sysreg(struct rec *rec,
				struct rec_plane *plane,
				struct rsi_result *res,
				bool read)
{
	unsigned long plane_id = plane->regs[1];
	unsigned long sysreg = plane->regs[2];
	STRUCT_TYPE sysreg_state *sysregs = REC_GET_SYSREGS_FROM_AUX(rec, plane_id);
	bool is_128b = (EXTRACT(RSI_SYSREG_ADDR_KVM_SYSREG128, sysreg) != 0UL);
	struct reg128 val;

	if (!is_feat_sysreg128_present() && is_128b) {
		return false;
	}

	/* Remove the SYSREG128 bitflag from the sysreg ID */
	sysreg &= ~MASK(RSI_SYSREG_ADDR_KVM_SYSREG128);

	val.hi = plane->regs[4];
	val.lo = plane->regs[3];

/* cppcheck-suppress misra-c2012-20.7 */
#define SYSREG_ACCESS_CASE(_group, _sysreg)					\
	case (RSI_SYSREG_KVM_ID_##_sysreg):					\
		return sysreg_access(res, &sysregs->_group._sysreg,		\
				     &val, read, is_128b)

/* cppcheck-suppress misra-c2012-20.7 */
#define SYSREG128_ACCESS_CASE(_group, _sysreg)					\
	case RSI_SYSREG_KVM_ID_##_sysreg:					\
		return sysreg_access_128b(res, &sysregs->_group._sysreg,	\
					  &val, read, is_128b)

	switch (sysreg) {
		SYSREG_ACCESS_CASE(pp_sysregs, cntp_ctl_el0);
		SYSREG_ACCESS_CASE(pp_sysregs, cntp_cval_el0);
		SYSREG_ACCESS_CASE(pp_sysregs, cntv_ctl_el0);
		SYSREG_ACCESS_CASE(pp_sysregs, cntv_cval_el0);
		SYSREG_ACCESS_CASE(pp_sysregs, sp_el0);
		SYSREG_ACCESS_CASE(pp_sysregs, tpidr_el0);
		SYSREG_ACCESS_CASE(pp_sysregs, tpidrro_el0);
		SYSREG_ACCESS_CASE(pp_sysregs, actlr_el1);
		SYSREG_ACCESS_CASE(pp_sysregs, afsr0_el1);
		SYSREG_ACCESS_CASE(pp_sysregs, afsr1_el1);
		SYSREG_ACCESS_CASE(pp_sysregs, amair_el1);
		SYSREG_ACCESS_CASE(pauth, apiakeylo_el1);
		SYSREG_ACCESS_CASE(pauth, apiakeyhi_el1);
		SYSREG_ACCESS_CASE(pauth, apibkeylo_el1);
		SYSREG_ACCESS_CASE(pauth, apibkeyhi_el1);
		SYSREG_ACCESS_CASE(pauth, apdakeylo_el1);
		SYSREG_ACCESS_CASE(pauth, apdakeyhi_el1);
		SYSREG_ACCESS_CASE(pauth, apdbkeylo_el1);
		SYSREG_ACCESS_CASE(pauth, apdbkeyhi_el1);
		SYSREG_ACCESS_CASE(pauth, apgakeylo_el1);
		SYSREG_ACCESS_CASE(pauth, apgakeyhi_el1);
		SYSREG_ACCESS_CASE(pp_sysregs, brbcr_el1);
		SYSREG_ACCESS_CASE(pp_sysregs, cntkctl_el1);
		SYSREG_ACCESS_CASE(pp_sysregs, contextidr_el1);
		SYSREG_ACCESS_CASE(pp_sysregs, cpacr_el1);
		SYSREG_ACCESS_CASE(pp_sysregs, csselr_el1);
		SYSREG_ACCESS_CASE(pp_sysregs, disr_el1);
		SYSREG_ACCESS_CASE(pp_sysregs, elr_el1);
		SYSREG_ACCESS_CASE(pp_sysregs, esr_el1);
		SYSREG_ACCESS_CASE(pp_sysregs, far_el1);
		SYSREG_ACCESS_CASE(pp_sysregs, mair_el1);
		SYSREG_ACCESS_CASE(pp_sysregs, mdccint_el1);
		SYSREG_ACCESS_CASE(pp_sysregs, mdscr_el1);
		SYSREG_ACCESS_CASE(pp_sysregs, pir_el1);
		SYSREG_ACCESS_CASE(pp_sysregs, pire0_el1);
		SYSREG_ACCESS_CASE(pp_sysregs, por_el1);
		SYSREG_ACCESS_CASE(pp_sysregs, sp_el1);
		SYSREG_ACCESS_CASE(pp_sysregs, sctlr_el1);
		SYSREG_ACCESS_CASE(pp_sysregs, spsr_el1);
		SYSREG_ACCESS_CASE(pp_sysregs, tcr_el1);
		SYSREG_ACCESS_CASE(pp_sysregs, tcr2_el1);
		SYSREG_ACCESS_CASE(pp_sysregs, tpidr_el1);
		SYSREG_ACCESS_CASE(pp_sysregs, vbar_el1);
		SYSREG_ACCESS_CASE(pp_sysregs, zcr_el1);

		/* Registers with 128-bit variants */
		SYSREG128_ACCESS_CASE(pp_sysregs, par_el1);
		SYSREG128_ACCESS_CASE(pp_sysregs, ttbr0_el1);
		SYSREG128_ACCESS_CASE(pp_sysregs, ttbr1_el1);
	default:
		return false;
	}

	/* coverity[misra_c_2012_rule_2_1_violation:SUPPRESS] */
	return false;
}

void handle_rsi_plane_sysreg_read(struct rec *rec, struct rsi_result *res)
{
	struct rec_plane *plane_0 = rec_plane_0(rec);
	unsigned long plane_idx = plane_0->regs[1];

	res->action = UPDATE_REC_RETURN_TO_REALM;
	res->smc_res.x[0] = RSI_ERROR_INPUT;

	/* This command can only be executed from Plane 0 */
	assert(rec_is_plane_0_active(rec));

	if ((plane_idx == PLANE_0_ID) ||
	    (plane_idx >= rec_num_planes(rec))) {
		return;
	}

	if (access_plane_sysreg(rec, plane_0, res, true) ||
	    access_pmu_sysregs(rec, plane_0, res, true) ||
	    access_pmu_pmev_el0(rec, plane_0, res, true)) {
		res->smc_res.x[0] = RSI_SUCCESS;
	}
}

void handle_rsi_plane_sysreg_write(struct rec *rec, struct rsi_result *res)
{
	struct rec_plane *plane_0 = rec_plane_0(rec);
	unsigned long plane_idx = plane_0->regs[1];

	res->action = UPDATE_REC_RETURN_TO_REALM;
	res->smc_res.x[0] = RSI_ERROR_INPUT;

	/* This command can only be executed from Plane 0 */
	assert(rec_is_plane_0_active(rec));

	if ((plane_idx == PLANE_0_ID) ||
	    (plane_idx >= rec_num_planes(rec))) {
		return;
	}

	if (access_plane_sysreg(rec, plane_0, res, false) ||
	    access_pmu_sysregs(rec, plane_0, res, false) ||
	    access_pmu_pmev_el0(rec, plane_0, res, false)) {
		res->smc_res.x[0] = RSI_SUCCESS;
	}
}
