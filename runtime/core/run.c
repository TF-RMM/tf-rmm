/*
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch.h>
#include <arch_features.h>
#include <attestation.h>
#include <buffer.h>
#include <cpuid.h>
#include <exit.h>
#include <granule.h>
#include <pmu.h>
#include <rec.h>
#include <run.h>
#include <simd.h>
#include <smc-rmi.h>
#include <timers.h>

static struct ns_state g_ns_data[MAX_CPUS];
static struct pmu_state g_pmu_data[MAX_CPUS];

static void save_sysreg_state(struct sysreg_state *sysregs)
{
	sysregs->sp_el0 = read_sp_el0();
	sysregs->sp_el1 = read_sp_el1();
	sysregs->elr_el1 = read_elr_el12();
	sysregs->spsr_el1 = read_spsr_el12();
	sysregs->pmcr_el0 = read_pmcr_el0();
	sysregs->tpidrro_el0 = read_tpidrro_el0();
	sysregs->tpidr_el0 = read_tpidr_el0();
	sysregs->csselr_el1 = read_csselr_el1();
	sysregs->sctlr_el1 = read_sctlr_el12();
	sysregs->actlr_el1 = read_actlr_el1();
	sysregs->cpacr_el1 = read_cpacr_el12();
	sysregs->ttbr0_el1 = read_ttbr0_el12();
	sysregs->ttbr1_el1 = read_ttbr1_el12();
	sysregs->tcr_el1 = read_tcr_el12();
	sysregs->esr_el1 = read_esr_el12();
	sysregs->afsr0_el1 = read_afsr0_el12();
	sysregs->afsr1_el1 = read_afsr1_el12();
	sysregs->far_el1 = read_far_el12();
	sysregs->mair_el1 = read_mair_el12();
	sysregs->vbar_el1 = read_vbar_el12();

	sysregs->contextidr_el1 = read_contextidr_el12();
	sysregs->tpidr_el1 = read_tpidr_el1();
	sysregs->amair_el1 = read_amair_el12();
	sysregs->cntkctl_el1 = read_cntkctl_el12();
	sysregs->par_el1 = read_par_el1();
	sysregs->mdscr_el1 = read_mdscr_el1();
	sysregs->mdccint_el1 = read_mdccint_el1();
	sysregs->disr_el1 = read_disr_el1();
	MPAM(sysregs->mpam0_el1 = read_mpam0_el1();)

	/* Timer registers */
	sysregs->cntpoff_el2 = read_cntpoff_el2();
	sysregs->cntvoff_el2 = read_cntvoff_el2();
	sysregs->cntp_ctl_el0 = read_cntp_ctl_el02();
	sysregs->cntp_cval_el0 = read_cntp_cval_el02();
	sysregs->cntv_ctl_el0 = read_cntv_ctl_el02();
	sysregs->cntv_cval_el0 = read_cntv_cval_el02();
}

static void save_realm_state(struct rec *rec, struct rmi_rec_exit *rec_exit)
{
	save_sysreg_state(&rec->sysregs);

	rec->pc = read_elr_el2();
	rec->pstate = read_spsr_el2();

	gic_save_state(&rec->sysregs.gicstate);

	if (rec->realm_info.pmu_enabled) {
		/* Expose PMU Realm state to NS */
		pmu_update_rec_exit(rec_exit);

		/* Save PMU context */
		pmu_save_state(rec->aux_data.pmu,
				rec->realm_info.pmu_num_ctrs);
	}
}

static void restore_sysreg_state(struct sysreg_state *sysregs)
{
	write_sp_el0(sysregs->sp_el0);
	write_sp_el1(sysregs->sp_el1);
	write_elr_el12(sysregs->elr_el1);
	write_spsr_el12(sysregs->spsr_el1);
	write_pmcr_el0(sysregs->pmcr_el0);
	write_tpidrro_el0(sysregs->tpidrro_el0);
	write_tpidr_el0(sysregs->tpidr_el0);
	write_csselr_el1(sysregs->csselr_el1);
	write_sctlr_el12(sysregs->sctlr_el1);
	write_actlr_el1(sysregs->actlr_el1);
	write_cpacr_el12(sysregs->cpacr_el1);
	write_ttbr0_el12(sysregs->ttbr0_el1);
	write_ttbr1_el12(sysregs->ttbr1_el1);
	write_tcr_el12(sysregs->tcr_el1);
	write_esr_el12(sysregs->esr_el1);
	write_afsr0_el12(sysregs->afsr0_el1);
	write_afsr1_el12(sysregs->afsr1_el1);
	write_far_el12(sysregs->far_el1);
	write_mair_el12(sysregs->mair_el1);
	write_vbar_el12(sysregs->vbar_el1);

	write_contextidr_el12(sysregs->contextidr_el1);
	write_tpidr_el1(sysregs->tpidr_el1);
	write_amair_el12(sysregs->amair_el1);
	write_cntkctl_el12(sysregs->cntkctl_el1);
	write_par_el1(sysregs->par_el1);
	write_mdscr_el1(sysregs->mdscr_el1);
	write_mdccint_el1(sysregs->mdccint_el1);
	write_disr_el1(sysregs->disr_el1);
	MPAM(write_mpam0_el1(sysregs->mpam0_el1);)
	write_vmpidr_el2(sysregs->vmpidr_el2);

	/* Timer registers */
	write_cntpoff_el2(sysregs->cntpoff_el2);
	write_cntvoff_el2(sysregs->cntvoff_el2);

	/*
	 * Restore CNTx_CVAL registers before CNTx_CTL to avoid
	 * raising the interrupt signal briefly before lowering
	 * it again due to some expired CVAL left in the timer
	 * register.
	 */
	write_cntp_cval_el02(sysregs->cntp_cval_el0);
	write_cntp_ctl_el02(sysregs->cntp_ctl_el0);
	write_cntv_cval_el02(sysregs->cntv_cval_el0);
	write_cntv_ctl_el02(sysregs->cntv_ctl_el0);
}

static void configure_realm_stage2(struct rec *rec)
{
	write_vtcr_el2(rec->common_sysregs.vtcr_el2);
	write_vttbr_el2(rec->common_sysregs.vttbr_el2);
}

static void restore_realm_state(struct rec *rec)
{
	/*
	 * Restore this early to give time to the timer mask to propagate to
	 * the GIC.  Issue an ISB to ensure the register write is actually
	 * performed before doing the remaining work.
	 */
	write_cnthctl_el2(rec->sysregs.cnthctl_el2);
	isb();

	restore_sysreg_state(&rec->sysregs);

	write_elr_el2(rec->pc);
	write_spsr_el2(rec->pstate);
	write_hcr_el2(rec->sysregs.hcr_el2);

	/* Control trapping of accesses to PMU registers */
	write_mdcr_el2(rec->common_sysregs.mdcr_el2);

	gic_restore_state(&rec->sysregs.gicstate);

	configure_realm_stage2(rec);

	if (rec->realm_info.pmu_enabled) {
		/* Restore PMU context */
		pmu_restore_state(rec->aux_data.pmu,
				  rec->realm_info.pmu_num_ctrs);
	}
}

static void save_ns_state(struct rec *rec)
{
	struct ns_state *ns_state = rec->ns;

	save_sysreg_state(&ns_state->sysregs);

	/*
	 * CNTHCTL_EL2 is saved/restored separately from the main system
	 * registers, because the Realm configuration is written on every
	 * entry to the Realm, see `check_pending_timers`.
	 */
	ns_state->sysregs.cnthctl_el2 = read_cnthctl_el2();

	ns_state->icc_sre_el2 = read_icc_sre_el2();

	if (rec->realm_info.pmu_enabled) {
		/* Save PMU context */
		pmu_save_state(ns_state->pmu, rec->realm_info.pmu_num_ctrs);
	}
}

static void restore_ns_state(struct rec *rec)
{
	struct ns_state *ns_state = rec->ns;

	restore_sysreg_state(&ns_state->sysregs);

	/*
	 * CNTHCTL_EL2 is saved/restored separately from the main system
	 * registers, because the Realm configuration is written on every
	 * entry to the Realm, see `check_pending_timers`.
	 */
	write_cnthctl_el2(ns_state->sysregs.cnthctl_el2);

	write_icc_sre_el2(ns_state->icc_sre_el2);

	if (rec->realm_info.pmu_enabled) {
		/* Restore PMU state */
		pmu_restore_state(ns_state->pmu,
				  rec->realm_info.pmu_num_ctrs);
	}
}

static void activate_events(struct rec *rec)
{
	/*
	 * The only event that may be activated at the Realm is the SError.
	 */
	if (rec->serror_info.inject) {
		write_vsesr_el2(rec->serror_info.vsesr_el2);
		write_hcr_el2(rec->sysregs.hcr_el2 | HCR_VSE);
		rec->serror_info.inject = false;
	}
}

void inject_serror(struct rec *rec, unsigned long vsesr)
{
	rec->serror_info.vsesr_el2 = vsesr;
	rec->serror_info.inject = true;
}

/* Save the REC SIMD state to memory and disable simd access for the REC */
void rec_simd_save_disable(struct rec *rec)
{
	struct rec_simd_state *rec_simd;
	simd_t stype;

	rec_simd = &rec->aux_data.rec_simd;

	assert(rec_simd->simd != NULL);
	assert(rec_simd->simd_allowed == true);

	stype = rec_simd_type(rec);

	/*
	 * As the REC has used the SIMD, no need to disable traps as it must be
	 * already disabled as part of last restore.
	 */
	rec_simd->simd_allowed = false;
	simd_save_state(stype, rec_simd->simd);
	simd_disable();
}

/* Restore the REC SIMD state from memory and enable simd access for the REC */
void rec_simd_enable_restore(struct rec *rec)
{
	struct rec_simd_state *rec_simd;
	simd_t stype;

	assert(rec != NULL);
	rec_simd = &rec->aux_data.rec_simd;

	assert(rec_simd->simd != NULL);
	assert(rec_simd->simd_allowed == false);

	stype = rec_simd_type(rec);
	simd_enable(stype);
	simd_restore_state(stype, rec_simd->simd);
	rec_simd->simd_allowed = true;
	/* return with traps disabled to allow REC to use FPU and/or SVE */
}

void rec_run_loop(struct rec *rec, struct rmi_rec_exit *rec_exit)
{
	struct ns_state *ns_state;
	int realm_exception_code;
	void *rec_aux;
	unsigned int cpuid = my_cpuid();
	int ret __unused;

	assert(cpuid < MAX_CPUS);
	assert(rec->ns == NULL);

	ns_state = &g_ns_data[cpuid];

	/* Ensure PMU context is cleared */
	assert(ns_state->pmu == NULL);

	rec->ns = ns_state;

	/* Map auxiliary granules */
	rec_aux = aux_granules_map(rec->g_aux, rec->num_rec_aux);

	/*
	 * Associate the attest heap with the current CPU. This heap will be
	 * used for attestation RSI calls when the REC is running.
	 */
	ret = attestation_heap_ctx_assign_pe(&rec->aux_data.attest_data->alloc_ctx);
	assert(ret == 0);

	ns_state->pmu = &g_pmu_data[cpuid];

	save_ns_state(rec);
	restore_realm_state(rec);

	/* The REC must enter run loop with SIMD access disabled */
	assert(rec_is_simd_allowed(rec) == false);

	do {
		/*
		 * We must check the status of the arch timers in every
		 * iteration of the loop to ensure we update the timer
		 * mask on each entry to the realm and that we report any
		 * change in output level to the NS caller.
		 */
		if (check_pending_timers(rec)) {
			rec_exit->exit_reason = RMI_EXIT_IRQ;
			break;
		}

		activate_events(rec);

		/*
		 * Restore Realm PAuth Key.
		 * There shouldn't be any other function call which uses PAuth
		 * till the RMM keys are restored.
		 */
		pauth_restore_realm_keys(&rec->pauth);

		realm_exception_code = run_realm(&rec->regs[0]);

		/* Save Realm PAuth key. */
		pauth_save_realm_keys(&rec->pauth);

		/* Restore RMM PAuth key. */
		pauth_restore_rmm_keys();
	} while (handle_realm_exit(rec, rec_exit, realm_exception_code));

	/*
	 * Check if FPU/SIMD was used, and if it was, save the realm state,
	 * restore the NS state, and reenable traps in CPTR_EL2.
	 */
	if (rec_is_simd_allowed(rec)) {
		/* Save REC SIMD state to memory and disable SIMD for REC */
		rec_simd_save_disable(rec);

		/* Restore NS state based on system support for SVE or FPU */
		simd_restore_ns_state();
	}

	report_timer_state_to_ns(rec_exit);

	save_realm_state(rec, rec_exit);
	restore_ns_state(rec);

	/*
	 * Clear PMU context while exiting
	 */
	ns_state->pmu = NULL;

	/*
	 * Clear NS pointer since that struct is local to this function.
	 */
	rec->ns = NULL;

	/* Undo the heap association */
	ret = attestation_heap_ctx_unassign_pe();
	assert(ret == 0);

	/* Unmap auxiliary granules */
	aux_granules_unmap(rec_aux, rec->num_rec_aux);
}
