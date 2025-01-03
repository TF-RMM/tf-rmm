/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

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
	unsigned long plane_idx = plane_0->regs[1U];
	unsigned long run_ipa = plane_0->regs[2U];
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
		res->smc_res.x[0U] = RSI_ERROR_INPUT;
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
	save_realm_state(plane_0);

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

/*
 * Perform a RW access @sysreg in plane @plane_id.
 *
 * This function does not make any sanitization or checks on
 * the arguments so it expects all of them to be valid.
 */
static bool access_plane_sysreg(struct rec *rec,
				unsigned long plane_id,
				unsigned long sysreg,
				unsigned long *value,
				bool read)
{
	STRUCT_TYPE sysreg_state *sysregs = &rec->aux_data.sysregs[plane_id];

/* cppcheck-suppress misra-c2012-20.7 */
#define SYSREG_ACCESS(_group, _sysreg)						\
	do {									\
		if (read) {							\
			*value = (unsigned long)sysregs->_group._sysreg;	\
		} else {							\
			sysregs->_group._sysreg = (unsigned long)*value;	\
		}								\
										\
		return true;							\
										\
	} while (false)


/* cppcheck-suppress misra-c2012-20.7 */
#define SYSREG_ACCESS_CASE(_group, _sysreg)					\
	case (RSI_SYSREG_ID_##_sysreg):						\
		SYSREG_ACCESS(_group, _sysreg)

	switch (sysreg) {
		SYSREG_ACCESS_CASE(pp_sysregs, sp_el1);
		SYSREG_ACCESS_CASE(pp_sysregs, elr_el1);
		SYSREG_ACCESS_CASE(pp_sysregs, spsr_el1);
		SYSREG_ACCESS_CASE(pp_sysregs, csselr_el1);
		SYSREG_ACCESS_CASE(pp_sysregs, sctlr_el1);
		SYSREG_ACCESS_CASE(pp_sysregs, actlr_el1);
		SYSREG_ACCESS_CASE(pp_sysregs, cpacr_el1);
		SYSREG_ACCESS_CASE(pp_sysregs, zcr_el1);
		SYSREG_ACCESS_CASE(pp_sysregs, ttbr0_el1);
		SYSREG_ACCESS_CASE(pp_sysregs, ttbr1_el1);
		SYSREG_ACCESS_CASE(pp_sysregs, tcr_el1);
		SYSREG_ACCESS_CASE(pp_sysregs, esr_el1);
		SYSREG_ACCESS_CASE(pp_sysregs, afsr0_el1);
		SYSREG_ACCESS_CASE(pp_sysregs, afsr1_el1);
		SYSREG_ACCESS_CASE(pp_sysregs, far_el1);
		SYSREG_ACCESS_CASE(pp_sysregs, mair_el1);
		SYSREG_ACCESS_CASE(pp_sysregs, vbar_el1);
		SYSREG_ACCESS_CASE(pp_sysregs, contextidr_el1);
		SYSREG_ACCESS_CASE(pp_sysregs, tpidr_el1);
		SYSREG_ACCESS_CASE(pp_sysregs, amair_el1);
		SYSREG_ACCESS_CASE(pp_sysregs, cntkctl_el1);
		SYSREG_ACCESS_CASE(pp_sysregs, par_el1);
		SYSREG_ACCESS_CASE(pp_sysregs, mdscr_el1);
		SYSREG_ACCESS_CASE(pp_sysregs, mdccint_el1);
		SYSREG_ACCESS_CASE(pp_sysregs, disr_el1);
		SYSREG_ACCESS_CASE(pp_sysregs, brbcr_el1);
		SYSREG_ACCESS_CASE(pp_sysregs, sp_el0);
		SYSREG_ACCESS_CASE(pp_sysregs, cntp_ctl_el0);
		SYSREG_ACCESS_CASE(pp_sysregs, cntp_cval_el0);
		SYSREG_ACCESS_CASE(pp_sysregs, cntv_ctl_el0);
		SYSREG_ACCESS_CASE(pp_sysregs, cntv_cval_el0);
		SYSREG_ACCESS_CASE(pp_sysregs, tpidrro_el0);
		SYSREG_ACCESS_CASE(pp_sysregs, tpidr_el0);
		SYSREG_ACCESS_CASE(pp_sysregs, tcr2_el1);
		SYSREG_ACCESS_CASE(pp_sysregs, pir_el1);
		SYSREG_ACCESS_CASE(pp_sysregs, pire0_el1);
		SYSREG_ACCESS_CASE(pp_sysregs, por_el1);
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
	default:
		return false;
	}

	/* coverity[misra_c_2012_rule_2_1_violation:SUPPRESS] */
	return false;
}

void handle_rsi_plane_reg_read(struct rec *rec, struct rsi_result *res)
{
	struct rec_plane *plane_0 = rec_plane_0(rec);
	unsigned long plane_idx = plane_0->regs[1U];
	unsigned long sysreg_encoding = plane_0->regs[2U];

	res->action = UPDATE_REC_RETURN_TO_REALM;
	res->smc_res.x[0U] = RSI_ERROR_INPUT;

	/* This command can only be executed from Plane 0 */
	assert(rec_is_plane_0_active(rec));

	if ((plane_idx == PLANE_0_ID) ||
	    (plane_idx >= rec_num_planes(rec))) {
		return;
	}

	if (access_plane_sysreg(rec, plane_idx, sysreg_encoding,
				&(res->smc_res.x[1U]), true)) {
		res->smc_res.x[0U] = RSI_SUCCESS;
		return;
	}
}

void handle_rsi_plane_reg_write(struct rec *rec, struct rsi_result *res)
{
	struct rec_plane *plane_0 = rec_plane_0(rec);
	unsigned long plane_idx = plane_0->regs[1U];
	unsigned long sysreg_encoding = plane_0->regs[2U];
	unsigned long value = plane_0->regs[3U];

	res->action = UPDATE_REC_RETURN_TO_REALM;
	res->smc_res.x[0U] = RSI_ERROR_INPUT;

	/* This command can only be executed from Plane 0 */
	assert(rec_is_plane_0_active(rec));

	if ((plane_idx == PLANE_0_ID) ||
	    (plane_idx >= rec_num_planes(rec))) {
		return;
	}

	if (access_plane_sysreg(rec, plane_idx, sysreg_encoding, &value, false)) {
		res->smc_res.x[0U] = RSI_SUCCESS;
	}
}
