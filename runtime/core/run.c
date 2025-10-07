/*
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch.h>
#include <arch_features.h>
#include <buffer.h>
#include <cpuid.h>
#include <debug.h>
#include <exit.h>
#include <granule.h>
#include <mec.h>
#include <pmu.h>
#include <realm.h>
#include <rec.h>
#include <run.h>
#include <s2ap_ind.h>
#include <s2tt.h>
#include <simd.h>
#include <smc-rmi.h>
#include <timers.h>
#include <types.h>

static struct ns_state g_ns_data[MAX_CPUS];

/* NS world SIMD context */
static struct simd_context g_ns_simd_ctx[MAX_CPUS]
			__aligned(CACHE_WRITEBACK_GRANULE);

static void save_sysreg_state(struct sysreg_state *sysregs)
{
	sysregs->pp_sysregs.sp_el1 = read_sp_el1();
	sysregs->pp_sysregs.elr_el1 = read_elr_el12();
	sysregs->pp_sysregs.spsr_el1 = read_spsr_el12();
	sysregs->pp_sysregs.tpidrro_el0 = read_tpidrro_el0();
	sysregs->pp_sysregs.tpidr_el0 = read_tpidr_el0();
	sysregs->pp_sysregs.csselr_el1 = read_csselr_el1();
	sysregs->pp_sysregs.sctlr_el1 = read_sctlr_el12();
	sysregs->pp_sysregs.sctlr2_el1 = read_sctlr2_el12_if_present();
	sysregs->pp_sysregs.actlr_el1 = read_actlr_el1();
	sysregs->pp_sysregs.cpacr_el1 = read_cpacr_el12();
	sysregs->pp_sysregs.tcr_el1 = read_tcr_el12();
	sysregs->pp_sysregs.esr_el1 = read_esr_el12();
	sysregs->pp_sysregs.afsr0_el1 = read_afsr0_el12();
	sysregs->pp_sysregs.afsr1_el1 = read_afsr1_el12();
	sysregs->pp_sysregs.far_el1 = read_far_el12();
	sysregs->pp_sysregs.mair_el1 = read_mair_el12();
	sysregs->pp_sysregs.vbar_el1 = read_vbar_el12();
	sysregs->pp_sysregs.tcr2_el1 = read_tcr2_el12_if_present();

	sysregs->pp_sysregs.contextidr_el1 = read_contextidr_el12();
	sysregs->pp_sysregs.tpidr_el1 = read_tpidr_el1();
	sysregs->pp_sysregs.amair_el1 = read_amair_el12();
	sysregs->pp_sysregs.cntkctl_el1 = read_cntkctl_el12();
	sysregs->pp_sysregs.mdscr_el1 = read_mdscr_el1();
	sysregs->pp_sysregs.mdccint_el1 = read_mdccint_el1();
	sysregs->pp_sysregs.disr_el1 = read_disr_el1();

	/* S1AP state */
	sysregs->pp_sysregs.pir_el1 = read_pir_el12_if_present();
	sysregs->pp_sysregs.pire0_el1 = read_pire0_el12_if_present();
	sysregs->pp_sysregs.por_el1 = read_por_el12_if_present();

	/* Timer registers */
	sysregs->cntpoff_el2 = read_cntpoff_el2();
	sysregs->cntvoff_el2 = read_cntvoff_el2();
	sysregs->pp_sysregs.cntp_ctl_el0 = read_cntp_ctl_el02();
	sysregs->pp_sysregs.cntp_cval_el0 = read_cntp_cval_el02();
	sysregs->pp_sysregs.cntv_ctl_el0 = read_cntv_ctl_el02();
	sysregs->pp_sysregs.cntv_cval_el0 = read_cntv_cval_el02();

	/* 128-bit registers */
	if (is_feat_d128_present()) {
		sysregs->pp_sysregs.par_el1 = read128_par_el1();
		sysregs->pp_sysregs.ttbr0_el1 = read128_ttbr0_el12();
		sysregs->pp_sysregs.ttbr1_el1 = read128_ttbr1_el12();
	} else {
		sysregs->pp_sysregs.par_el1.lo = read_par_el1();
		sysregs->pp_sysregs.ttbr0_el1.lo = read_ttbr0_el12();
		sysregs->pp_sysregs.ttbr1_el1.lo = read_ttbr1_el12();
	}
}

static void save_pmu(struct rec *rec)
{
	if (rec->realm_info.pmu_enabled) {
		/* Save PMU context
		 * Save number of PMU event counters configured for the realm.
		 */
		pmu_save_state(rec_active_plane_sysregs(rec)->pmu,
				rec->realm_info.pmu_num_ctrs);
	}
}

static void restore_pmu(struct rec *rec)
{
	if (rec->realm_info.pmu_enabled) {
		/*
		 * Restore realm PMU context.
		 * Restore number of PMU counters configured for the realm.
		 */
		pmu_restore_state(rec_active_plane_sysregs(rec)->pmu,
				  rec->realm_info.pmu_num_ctrs);
	}
}

static void report_pmu_state_to_ns(struct rec *rec, struct rmi_rec_exit *rec_exit)
{
	if (rec->realm_info.pmu_enabled) {
		/* Expose PMU Realm state to NS */
		rec_exit->pmu_ovf_status = (pmu_is_ovf_set() ?
		RMI_PMU_OVERFLOW_ACTIVE : RMI_PMU_OVERFLOW_NOT_ACTIVE);
	}
}

void save_realm_state(struct rec *rec, struct rec_plane *plane,
		      STRUCT_TYPE sysreg_state *sysregs)
{
	save_sysreg_state(sysregs);

	plane->pc = read_elr_el2();
	plane->pstate = read_spsr_el2();

	plane->plane_exit_info.esr = read_esr_el2();
	plane->plane_exit_info.hpfar = read_hpfar_el2();
	plane->plane_exit_info.far = read_far_el2();

	save_pmu(rec);
	gic_save_state(&sysregs->gicstate);

	mec_realm_mecid_s2_reset();
}

static void restore_sysreg_state(struct sysreg_state *sysregs)
{
	write_sp_el1(sysregs->pp_sysregs.sp_el1);
	write_elr_el12(sysregs->pp_sysregs.elr_el1);
	write_spsr_el12(sysregs->pp_sysregs.spsr_el1);
	write_tpidrro_el0(sysregs->pp_sysregs.tpidrro_el0);
	write_tpidr_el0(sysregs->pp_sysregs.tpidr_el0);
	write_csselr_el1(sysregs->pp_sysregs.csselr_el1);
	write_sctlr_el12(sysregs->pp_sysregs.sctlr_el1);
	write_sctlr2_el12_if_present(sysregs->pp_sysregs.sctlr2_el1);
	write_actlr_el1(sysregs->pp_sysregs.actlr_el1);
	write_cpacr_el12(sysregs->pp_sysregs.cpacr_el1);
	write_tcr_el12(sysregs->pp_sysregs.tcr_el1);
	write_esr_el12(sysregs->pp_sysregs.esr_el1);
	write_afsr0_el12(sysregs->pp_sysregs.afsr0_el1);
	write_afsr1_el12(sysregs->pp_sysregs.afsr1_el1);
	write_far_el12(sysregs->pp_sysregs.far_el1);
	write_mair_el12(sysregs->pp_sysregs.mair_el1);
	write_vbar_el12(sysregs->pp_sysregs.vbar_el1);
	write_tcr2_el12_if_present(sysregs->pp_sysregs.tcr2_el1);

	write_contextidr_el12(sysregs->pp_sysregs.contextidr_el1);
	write_tpidr_el1(sysregs->pp_sysregs.tpidr_el1);
	write_amair_el12(sysregs->pp_sysregs.amair_el1);
	write_cntkctl_el12(sysregs->pp_sysregs.cntkctl_el1);
	write_mdscr_el1(sysregs->pp_sysregs.mdscr_el1);
	write_mdccint_el1(sysregs->pp_sysregs.mdccint_el1);
	write_disr_el1(sysregs->pp_sysregs.disr_el1);
	write_vmpidr_el2(sysregs->vmpidr_el2);

	/* S1AP state */
	write_pir_el12_if_present(sysregs->pp_sysregs.pir_el1);
	write_pire0_el12_if_present(sysregs->pp_sysregs.pire0_el1);
	write_por_el12_if_present(sysregs->pp_sysregs.por_el1);

	/* Timer registers */
	write_cntpoff_el2(sysregs->cntpoff_el2);
	write_cntvoff_el2(sysregs->cntvoff_el2);

	/*
	 * Restore CNTx_CVAL registers before CNTx_CTL to avoid
	 * raising the interrupt signal briefly before lowering
	 * it again due to some expired CVAL left in the timer
	 * register.
	 */

	write_cntp_cval_el02(sysregs->pp_sysregs.cntp_cval_el0);
	write_cntp_ctl_el02(sysregs->pp_sysregs.cntp_ctl_el0);
	write_cntv_cval_el02(sysregs->pp_sysregs.cntv_cval_el0);
	write_cntv_ctl_el02(sysregs->pp_sysregs.cntv_ctl_el0);

	/* 128-bit registers */
	if (is_feat_d128_present()) {
		write128_par_el1(&(sysregs->pp_sysregs.par_el1));
		write128_ttbr0_el12(&(sysregs->pp_sysregs.ttbr0_el1));
		write128_ttbr1_el12(&(sysregs->pp_sysregs.ttbr1_el1));
	} else {
		write_par_el1(sysregs->pp_sysregs.par_el1.lo);
		write_ttbr0_el12(sysregs->pp_sysregs.ttbr0_el1.lo);
		write_ttbr1_el12(sysregs->pp_sysregs.ttbr1_el1.lo);
	}
}

/*
 * Configure the realm stage 2 registers.
 * Note that there is a 1-2-1 correspondence between vttbr_el2 array index
 * and the plane ID.
 */
static void restore_realm_stage2(struct rec *rec)
{
	struct s2tt_context *s2_context;
	struct rd *rd;

	rd = buffer_granule_map(rec->realm_info.g_rd, SLOT_RD);
	assert(rd != NULL);

	s2_context = plane_to_s2_context(rd, rec->active_plane_id);

	/* Program vmec prior to Stage 2 programming */
	mec_realm_mecid_s2_init(s2_context->mecid);
	write_vtcr_el2(rec->common_sysregs.vtcr_el2);
	write_vttbr_el2(rec_active_plane_sysregs(rec)->vttbr_el2);

	if (rec->realm_info.rtt_s2ap_encoding == S2AP_INDIRECT_ENC) {
		s2ap_ind_write_overlay(s2tt_ctx_get_overlay_perm_unlocked(s2_context));
	}

	buffer_unmap(rd);
}

void restore_realm_state(struct rec *rec, struct rec_plane *plane,
			 STRUCT_TYPE sysreg_state *sysregs)
{
	/*
	 * Restore this early to give time to the timer mask to propagate to
	 * the GIC.  Issue an ISB to ensure the register write is actually
	 * performed before doing the remaining work.
	 */
	write_cnthctl_el2(sysregs->cnthctl_el2);
	isb();

	restore_sysreg_state(sysregs);

	/*
	 * Disable BRBE for R-EL1, BRBE related registers cannot be accessed
	 * from Realms as RMM will trap it.
	 */
	if (is_feat_brbe_present()) {
		write_brbcr_el1(BRBCR_INIT);
	}

	write_elr_el2(plane->pc);
	write_spsr_el2(plane->pstate);
	write_hcr_el2(sysregs->hcr_el2);

	/* Control trapping of accesses to PMU registers */
	write_mdcr_el2(rec->common_sysregs.mdcr_el2);

	restore_pmu(rec);
	gic_restore_state(&sysregs->gicstate);

	restore_realm_stage2(rec);
}

static void save_ns_state(struct rec *rec)
{
	struct ns_state *ns_state;

	assert(rec->ns != NULL);
	ns_state = rec->ns;

	save_sysreg_state(&ns_state->sysregs);

	if (is_feat_brbe_present()) {
		ns_state->sysregs.pp_sysregs.brbcr_el1 = read_brbcr_el1();
	}

	/*
	 * CNTHCTL_EL2 is saved/restored separately from the main system
	 * registers, because the Realm configuration is written on every
	 * entry to the Realm, see `check_pending_timers`.
	 */
	ns_state->sysregs.cnthctl_el2 = read_cnthctl_el2();

	ns_state->icc_sre_el2 = read_icc_sre_el2();

	if (rec->realm_info.rtt_s2ap_encoding) {
		assert(s2tt_indirect_ap_supported());
		ns_state->s2por_el1 = read_s2por_el1();
	}

	if (rec->realm_info.pmu_enabled) {
		/*
		 * Save NS PMU context.
		 * Save all implemented PMU event counters.
		 */
		pmu_save_state(&ns_state->pmu,
				(unsigned int)EXTRACT(PMCR_EL0_N, read_pmcr_el0()));
	}

	hyp_timer_save_state(&ns_state->el2_timer);
}

static void restore_ns_state(struct rec *rec)
{
	struct ns_state *ns_state;

	assert(rec->ns != NULL);
	ns_state = rec->ns;

	restore_sysreg_state(&ns_state->sysregs);

	if (is_feat_brbe_present()) {
		write_brbcr_el1(ns_state->sysregs.pp_sysregs.brbcr_el1);
	}

	/*
	 * CNTHCTL_EL2 is saved/restored separately from the main system
	 * registers, because the Realm configuration is written on every
	 * entry to the Realm, see `check_pending_timers`.
	 */
	write_cnthctl_el2(ns_state->sysregs.cnthctl_el2);

	write_icc_sre_el2(ns_state->icc_sre_el2);

	if (rec->realm_info.rtt_s2ap_encoding) {
		assert(s2tt_indirect_ap_supported());
		write_s2por_el1(ns_state->s2por_el1);
	}

	if (rec->realm_info.pmu_enabled) {
		/*
		 * Restore NS PMU state.
		 * Restore all implemented PMU event counters.
		 */
		pmu_restore_state(&ns_state->pmu,
				  (unsigned int)EXTRACT(PMCR_EL0_N, read_pmcr_el0()));
	}

	hyp_timer_restore_state(&ns_state->el2_timer);
}

static void activate_events(struct rec *rec)
{
	/*
	 * The only event that may be activated at the Realm is the SError.
	 */
	if (rec->serror_info.inject) {
		write_vsesr_el2(rec->serror_info.vsesr_el2);

		/*
		 * @TODO: The RMM Specification says to exit to Host when Planes
		 * encounter an SError. But SError should be injected into the
		 * original plane N and not be re-routed to P0. Regardless if
		 * P0 gets re-scheduled, we need a syndrome to be passed to P0.
		 */
		write_hcr_el2(rec_active_plane_sysregs(rec)->hcr_el2 | HCR_VSE);
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
	unsigned int cpuid = my_cpuid();
	struct rec_plane *plane = rec_active_plane(rec);
	STRUCT_TYPE sysreg_state *sysregs = rec_active_plane_sysregs(rec);
	bool skip_timer_report = false;

	assert(cpuid < MAX_CPUS);
	assert(rec->ns == NULL);

	ns_state = &g_ns_data[cpuid];

	rec->ns = ns_state;

	save_ns_state(rec);
	restore_realm_state(rec, plane, sysregs);

	/*
	 * The run loop must be entered with active SIMD context set to current
	 * CPU's NS SIMD context
	 */
	assert(rec->active_simd_ctx == NULL);
	rec->active_simd_ctx = &g_ns_simd_ctx[cpuid];

	/*
	 * In case we enter straight into a Plane N, we might need to
	 * adjust EL2 timer to get notified of Plane 0 EL1 timers.
	 */
	if (!rec_is_plane_0_active(rec)) {
		multiplex_el2_timer(rec);
	}

	do {
		unsigned long rmm_cptr_el2 = read_cptr_el2();

		/* Active plane can change on each exit */
		plane = rec_active_plane(rec);
		sysregs = rec_active_plane_sysregs(rec);

		/*
		 * We must check the status of the arch timers in every
		 * iteration of the loop to ensure we update the timer
		 * mask on each entry to the realm and that we report any
		 * change in output level to the NS caller.
		 */
		if (check_pending_timers(sysregs)) {
			if (!rec_is_plane_0_active(rec)) {
				bool plane_n_exited;

				skip_timer_report = true;
				report_timer_state_to_ns(rec, rec_exit);

				/* Switch to P0 to handle timer interrupt */
				plane_n_exited = handle_plane_n_exit(rec, rec_exit,
							ARM_EXCEPTION_IRQ_LEL, true);

				if (!plane_n_exited) {
					/*
					 * @TODO: This condition needs to be properly
					 * reported back to NS.
					 */
					ERROR("%s at %s: handle_plane_n_exit failed!\n",
							__FILE__, __func__);
				}
			}
			rec_exit->exit_reason = RMI_EXIT_IRQ;
			break;
		}

		activate_events(rec);

		/* Restore REC's cptr_el2 */
		if (rmm_cptr_el2 != sysregs->cptr_el2) {
			write_cptr_el2(sysregs->cptr_el2);
			isb();
		}

		/*
		 * Restore Realm PAuth Key.
		 * There shouldn't be any other function call which uses PAuth
		 * till the RMM keys are restored.
		 */
		pauth_restore_realm_keys(&sysregs->pauth);

		realm_exception_code = run_realm(&plane->regs[0],
						 &sysregs->pp_sysregs.sp_el0);

		/* Save Realm PAuth key. */
		pauth_save_realm_keys(&sysregs->pauth);

		/* Restore RMM PAuth key. */
		pauth_restore_rmm_keys();

		/* Restore RMM's cptr_el2 */
		if (rmm_cptr_el2 != sysregs->cptr_el2) {
			write_cptr_el2(rmm_cptr_el2);
			isb();
		}
	} while (handle_realm_exit(rec, rec_exit, realm_exception_code));

	/* Active plane can change on each exit */
	plane = rec_active_plane(rec);
	sysregs = rec_active_plane_sysregs(rec);

	/*
	 * Check if FPU/SIMD was used, and if it was, save the realm state,
	 * restore the NS state.
	 */
	if (rec->active_simd_ctx == rec->aux_data.simd_ctx) {
		(void)simd_context_switch(rec->active_simd_ctx,
					  &g_ns_simd_ctx[cpuid]);

		/*
		 * As the REC SIMD context is now saved, disable all SIMD
		 * related flags current plane's cptr.
		 */
		SIMD_DISABLE_ALL_CPTR_FLAGS(sysregs->cptr_el2);
	}

	/* Clear active simd_context */
	rec->active_simd_ctx = NULL;

	if (!skip_timer_report) {
		/* Timer status already reported */
		report_timer_state_to_ns(rec, rec_exit);
	}

	/* Expose PMU Realm state to NS */
	report_pmu_state_to_ns(rec, rec_exit);

	save_realm_state(rec, plane, sysregs);

	restore_ns_state(rec);

	/*
	 * Clear NS pointer since that struct is local to this function.
	 */
	rec->ns = NULL;
}
