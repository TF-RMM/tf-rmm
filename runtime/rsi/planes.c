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
#include <smc-rsi.h>
#include <timers.h>
#include <utils_def.h>

static void copy_state_from_plane_entry(struct rec_plane *plane,
					struct rsi_plane_enter *entry,
					bool restore_gic)
{
	for (unsigned int i = 0; i < RSI_PLANE_NR_GPRS; i++) {
		plane->regs[i] = entry->gprs[i];
	}

	plane->pc = entry->pc;
	plane->sysregs->pstate = entry->pstate;
	if (restore_gic) {
		gic_copy_state_from_entry(&plane->sysregs->gicstate,
			(unsigned long *)&entry->gicv3_lrs, entry->gicv3_hcr);
	}
}

void handle_rsi_plane_enter(struct rec *rec, struct rsi_result *res)
{
	struct rec_plane *plane_0 = rec_plane_0(rec);
	struct rec_plane *plane_n;
	unsigned long plane_idx = plane_0->regs[1];
	unsigned long run_ipa = plane_0->regs[2];
	enum s2_walk_status walk_status;
	struct s2_walk_result walk_res;
	struct granule *gr;
	struct rsi_plane_run *run;
	bool restore_gic = true;

	res->action = UPDATE_REC_RETURN_TO_REALM;

	/* This command can only be executed from Plane 0 */
	assert(rec_is_plane_0_active(rec));

	if ((plane_idx == PLANE_0_ID) ||
	    (plane_idx >= rec_num_planes(rec))) {
		res->smc_res.x[0] = RSI_ERROR_INPUT;
		return;
	}

	walk_status = realm_ipa_to_pa(rec, run_ipa, &walk_res);

	if (walk_status == WALK_INVALID_PARAMS) {
		res->smc_res.x[0] = RSI_ERROR_INPUT;
		return;
	}

	if (walk_status == WALK_FAIL) {
		if (walk_res.ripas_val == RIPAS_EMPTY) {
			res->smc_res.x[0] = RSI_ERROR_INPUT;
		} else {
			res->action = STAGE_2_TRANSLATION_FAULT;
			res->rtt_level = walk_res.rtt_level;
		}
		return;
	}

	/* Save Plane 0 state to REC */
	save_realm_state(rec, plane_0);

	/*
	 * Check if the primary plane has timers that we need to be notified of
	 */
	multiplex_el2_timer(rec);

	/* Map Realm data granule to RMM address space */
	gr = find_granule(walk_res.pa);
	assert(gr != NULL);

	run = (struct rsi_plane_run *)buffer_granule_map(gr, SLOT_REALM);

	/* Activate plane N */
	plane_n = rec_activate_plane_n(rec, (unsigned int)plane_idx);

	if ((run->enter.flags & RSI_PLANE_ENTER_FLAGS_OWN_GIC) != 0UL) {
		rec->gic_owner = (unsigned int)plane_idx;

		/* Transfer the GIC status from Plane 0 to the new owner */
		gic_copy_state(&plane_n->sysregs->gicstate,
			       &plane_0->sysregs->gicstate);
		restore_gic = false;
	}

	/* Copy target Plane state from entry structure to REC */
	copy_state_from_plane_entry(plane_n, &run->enter, restore_gic);

	/* Initialize trap control bits */
	plane_n->sysregs->hcr_el2 = rec->common_sysregs.hcr_el2;

	if ((run->enter.flags & RSI_PLANE_ENTER_FLAGS_TRAP_WFI) != RSI_NO_TRAP) {
		plane_n->sysregs->hcr_el2 |= HCR_TWI;
	}

	if ((run->enter.flags & RSI_PLANE_ENTER_FLAGS_TRAP_WFE) != RSI_NO_TRAP) {
		plane_n->sysregs->hcr_el2 |= HCR_TWE;
	}

	plane_n->trap_hc =
		((run->enter.flags & RSI_PLANE_ENTER_FLAGS_TRAP_HC) != RSI_NO_TRAP);

	/* Change active Plane */
	res->action = PLANE_CHANGED_RETURN_TO_REALM;

	/* Restore target Plane from REC */
	restore_realm_state(rec, plane_n);

	/* Unmap Realm data granule */
	buffer_unmap(run);

	/* Unlock last level RTT */
	granule_unlock(walk_res.llt);
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
	STRUCT_TYPE sysreg_state *sysregs = &rec->aux_data.sysregs[plane_id];

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
				pmev_regs->pmevcntr_el0 = res->smc_res.x[3];
			}
			return true;
		}

		if ((sysreg_id & RSI_SYSREG_PMEV_MASK) == RSI_SYSREG_PMEVTYPER_MASK) {
			if (read) {
				res->smc_res.x[1] = pmev_regs->pmevtyper_el0;
			} else {
				pmev_regs->pmevtyper_el0 = res->smc_res.x[3];
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
	STRUCT_TYPE sysreg_state *sysregs = &rec->aux_data.sysregs[plane_id];

	if (EXTRACT(RSI_SYSREG_ADDR_KVM_SYSREG128, sysreg_id) != 0UL) {
		/*  No 128-bit registers allowed here */
		return false;
	}

/* cppcheck-suppress misra-c2012-20.7 */
#define PMU_SYSREG_ACCESS_CASE(_sysreg)						\
	case RSI_SYSREG_KVM_ID_##_sysreg:					\
		do {								\
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
	} else {
		*sysreg = val->lo;
	}

	return true;
}

/*
 * This helper function is intended for regisers that are 128 bits wide when
 * FEAT_SYSREG128 is implemented and 64 bits otherwise.
 *
 * If FEAT_SYSREG128 is not implemented, the function will write 0 to the
 * upper 64 bits of the register in the sysreg sctructre, since @val->hi
 * is initialized to 0.
 *
 * When reading the register, the upper 64 bits will already be 0, ensuring
 * the expected value is returned.
 */
static bool sysreg_access_d128(struct rsi_result *res, struct reg128 *sysreg,
			       struct reg128 *val, bool read)
{
	if (read) {
		res->smc_res.x[1] = sysreg->lo;
		res->smc_res.x[2] = sysreg->hi;
	} else {
		sysreg->hi = val->hi;
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
	STRUCT_TYPE sysreg_state *sysregs = &rec->aux_data.sysregs[plane_id];
	bool is_128b = (EXTRACT(RSI_SYSREG_ADDR_KVM_SYSREG128, sysreg) != 0UL);
	struct reg128 val;

	/* Remove the SYSREG128 bitflag from the sysreg ID */
	sysreg &= ~MASK(RSI_SYSREG_ADDR_KVM_SYSREG128);

	/*
	 * Get the 64 msbs on a 128-bit register in case the operation is
	 * a write.
	 *
	 * Note that all the 128-bit registers accessed here are only
	 * available when FEAT_D128 is available.
	 */
	val.hi = ((is_feat_sysreg128_present()) ? plane->regs[4] : 0UL);
	val.lo = plane->regs[3];

/* cppcheck-suppress misra-c2012-20.7 */
#define SYSREG_ACCESS_CASE(_group, _sysreg)					\
	case (RSI_SYSREG_KVM_ID_##_sysreg):					\
		return sysreg_access(res, &sysregs->_group._sysreg,		\
				     &val, read, is_128b)

/* cppcheck-suppress misra-c2012-20.7 */
#define SYSREG128_ACCESS_CASE(_group, _sysreg)					\
	case RSI_SYSREG_KVM_ID_##_sysreg:					\
		return sysreg_access_d128(res, &sysregs->_group._sysreg,	\
					  &val, read)

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
