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
#include <debug.h>
#include <exit.h>
#include <granule.h>
#include <pmu.h>
#include <rec.h>
#include <run.h>
#include <simd.h>
#include <smc-rmi.h>
#include <timers.h>

static struct ns_state g_ns_data[MAX_CPUS];

/* NS world SIMD context */
static struct simd_context g_ns_simd_ctx[MAX_CPUS]
			__aligned(CACHE_WRITEBACK_GRANULE);

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
	sysregs->sctlr2_el1 = read_sctlr2_el12_if_present();
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
	write_sctlr2_el12_if_present(sysregs->sctlr2_el1);
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
		pmu_save_state(&ns_state->pmu, rec->realm_info.pmu_num_ctrs);
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
		pmu_restore_state(&ns_state->pmu,
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

/* Initialize the NS world SIMD context for all CPUs. */
void init_all_cpus_ns_simd_context(void)
{
	struct simd_config simd_cfg = { 0 };

	(void)simd_get_cpu_config(&simd_cfg);

	for (uint32_t i = 0; i < MAX_CPUS; i++) {
		int __unused retval;

		retval = simd_context_init(SIMD_OWNER_NWD, &g_ns_simd_ctx[i],
					   &simd_cfg);
		assert(retval == 0);
	}
}

struct simd_context *get_cpu_ns_simd_context(void)
{
	return &g_ns_simd_ctx[my_cpuid()];
}

void rec_run_loop(struct rec *rec, struct rmi_rec_exit *rec_exit)
{
	struct ns_state *ns_state;
	int realm_exception_code;
	void *rec_aux;
	unsigned int cpuid = my_cpuid();

	assert(cpuid < MAX_CPUS);
	assert(rec->ns == NULL);

	ns_state = &g_ns_data[cpuid];

	rec->ns = ns_state;

	/* Map auxiliary granules */
	rec_aux = buffer_rec_aux_granules_map(rec->g_aux, rec->num_rec_aux);

	/*
	 * Associate the attest heap with the current CPU. This heap will be
	 * used for attestation RSI calls when the REC is running.
	 */
	attestation_heap_ctx_assign_pe(&rec->aux_data.attest_data->alloc_ctx);

	save_ns_state(rec);
	restore_realm_state(rec);

	/*
	 * The run loop must be entered with active SIMD context set to current
	 * CPU's NS SIMD context
	 */
	assert(rec->active_simd_ctx == NULL);
	rec->active_simd_ctx = &g_ns_simd_ctx[cpuid];

	do {
		unsigned long rmm_cptr_el2 = read_cptr_el2();

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

		/* Restore REC's cptr_el2 */
		if (rmm_cptr_el2 != rec->sysregs.cptr_el2) {
			write_cptr_el2(rec->sysregs.cptr_el2);
			isb();
		}

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

		/* Restore RMM's cptr_el2 */
		if (rmm_cptr_el2 != rec->sysregs.cptr_el2) {
			write_cptr_el2(rmm_cptr_el2);
			isb();
		}
	} while (handle_realm_exit(rec, rec_exit, realm_exception_code));

	/*
	 * Check if FPU/SIMD was used, and if it was, save the realm state,
	 * restore the NS state.
	 */
	if (rec->active_simd_ctx == rec->aux_data.simd_ctx) {
		(void)simd_context_switch(rec->active_simd_ctx,
					  &g_ns_simd_ctx[cpuid]);

		/*
		 * As the REC SIMD context is now saved, disable all SIMD related
		 * flags in REC's cptr.
		 */
		SIMD_DISABLE_ALL_CPTR_FLAGS(rec->sysregs.cptr_el2);
	}

	/* Clear active simd_context */
	rec->active_simd_ctx = NULL;

	report_timer_state_to_ns(rec_exit);

	save_realm_state(rec, rec_exit);
	restore_ns_state(rec);

	/*
	 * Clear NS pointer since that struct is local to this function.
	 */
	rec->ns = NULL;

	/* Undo the heap association */
	attestation_heap_ctx_unassign_pe();


	/* Unmap auxiliary granules */
	buffer_rec_aux_unmap(rec_aux, rec->num_rec_aux);
}
