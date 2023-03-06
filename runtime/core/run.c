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
#include <fpu_helpers.h>
#include <rec.h>
#include <run.h>
#include <smc-rmi.h>
#include <sve.h>
#include <timers.h>

static struct ns_state g_ns_data[MAX_CPUS];
static uint8_t g_sve_data[MAX_CPUS][sizeof(struct sve_state)]
		__attribute__((aligned(sizeof(__uint128_t))));

/*
 * Initialize the aux data and any buffer pointers to the aux granule memory for
 * use by REC when it is entered.
 */
static void init_aux_data(struct rec_aux_data *aux_data,
			  void *rec_aux,
			  unsigned int num_rec_aux)
{
	aux_data->attest_heap_buf = (uint8_t *)rec_aux;

	/* Ensure we have enough aux granules for use by REC */
	assert(num_rec_aux >= REC_HEAP_PAGES);
}

/*
 * The parent REC granules lock is expected to be acquired
 * before functions map_rec_aux() and unmap_rec_aux() are called.
 */
static void *map_rec_aux(struct granule *rec_aux_pages[], unsigned long num_aux)
{
	void *rec_aux = NULL;

	for (unsigned long i = 0UL; i < num_aux; i++) {
		void *aux = granule_map(rec_aux_pages[i], SLOT_REC_AUX0 + i);

		if (i == 0UL) {
			rec_aux = aux;
		}
	}
	return rec_aux;
}

static void unmap_rec_aux(void *rec_aux, unsigned long num_aux)
{
	unsigned char *rec_aux_vaddr = (unsigned char *)rec_aux;

	for (unsigned long i = 0UL; i < num_aux; i++) {
		buffer_unmap(rec_aux_vaddr + i * GRANULE_SIZE);
	}
}

static void save_sysreg_state(struct sysreg_state *sysregs)
{
	sysregs->sp_el0 = read_sp_el0();
	sysregs->sp_el1 = read_sp_el1();
	sysregs->elr_el1 = read_elr_el12();
	sysregs->spsr_el1 = read_spsr_el12();
	sysregs->pmcr_el0 = read_pmcr_el0();
	sysregs->pmuserenr_el0 = read_pmuserenr_el0();
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

static void save_realm_state(struct rec *rec)
{
	save_sysreg_state(&rec->sysregs);

	rec->pc = read_elr_el2();
	rec->pstate = read_spsr_el2();

	gic_save_state(&rec->sysregs.gicstate);
}

static void restore_sysreg_state(struct sysreg_state *sysregs)
{
	write_sp_el0(sysregs->sp_el0);
	write_sp_el1(sysregs->sp_el1);
	write_elr_el12(sysregs->elr_el1);
	write_spsr_el12(sysregs->spsr_el1);
	write_pmcr_el0(sysregs->pmcr_el0);
	write_pmuserenr_el0(sysregs->pmuserenr_el0);
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

	gic_restore_state(&rec->sysregs.gicstate);
}

static void configure_realm_stage2(struct rec *rec)
{
	write_vtcr_el2(rec->common_sysregs.vtcr_el2);
	write_vttbr_el2(rec->common_sysregs.vttbr_el2);
}

static void save_ns_state(struct ns_state *ns_state)
{
	save_sysreg_state(&ns_state->sysregs);

	/*
	 * CNTHCTL_EL2 is saved/restored separately from the main system
	 * registers, because the Realm configuration is written on every
	 * entry to the Realm, see `check_pending_timers`.
	 */
	ns_state->sysregs.cnthctl_el2 = read_cnthctl_el2();

	ns_state->icc_sre_el2 = read_icc_sre_el2();
}

static void restore_ns_state(struct ns_state *ns_state)
{
	restore_sysreg_state(&ns_state->sysregs);

	/*
	 * CNTHCTL_EL2 is saved/restored separately from the main system
	 * registers, because the Realm configuration is written on every
	 * entry to the Realm, see `check_pending_timers`.
	 */
	write_cnthctl_el2(ns_state->sysregs.cnthctl_el2);

	write_icc_sre_el2(ns_state->icc_sre_el2);
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

void rec_run_loop(struct rec *rec, struct rmi_rec_exit *rec_exit)
{
	struct ns_state *ns_state;
	int realm_exception_code;
	void *rec_aux;
	unsigned int cpuid = my_cpuid();

	assert(rec->ns == NULL);

	assert(cpuid < MAX_CPUS);
	ns_state = &g_ns_data[cpuid];

	/* ensure SVE/FPU context is cleared */
	assert(ns_state->sve == NULL);
	assert(ns_state->fpu == NULL);

	/* Map auxiliary granules */
	rec_aux = map_rec_aux(rec->g_aux, rec->num_rec_aux);

	init_aux_data(&(rec->aux_data), rec_aux, rec->num_rec_aux);

	/*
	 * The attset heap on the REC aux pages is mapped now. It is time to
	 * associate it with the current CPU.
	 * This heap will be used for attestation RSI calls when the
	 * REC is running.
	 */
	attestation_heap_ctx_assign_pe(&rec->alloc_info.ctx);

	/*
	 * Initialise the heap for attestation if necessary.
	 */
	if (!rec->alloc_info.ctx_initialised) {
		(void)attestation_heap_ctx_init(rec->aux_data.attest_heap_buf,
						REC_HEAP_PAGES * SZ_4K);
		rec->alloc_info.ctx_initialised = true;
	}

	if (is_feat_sve_present()) {
		ns_state->sve = (struct sve_state *)&g_sve_data[cpuid];
	} else {
		ns_state->fpu = (struct fpu_state *)&g_sve_data[cpuid];
	}

	save_ns_state(ns_state);
	restore_realm_state(rec);

	/* Prepare for lazy save/restore of FPU/SIMD registers. */
	rec->ns = ns_state;
	assert(rec->fpu_ctx.used == false);

	configure_realm_stage2(rec);

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
		realm_exception_code = run_realm(&rec->regs[0]);
	} while (handle_realm_exit(rec, rec_exit, realm_exception_code));

	/*
	 * Check if FPU/SIMD was used, and if it was, save the realm state,
	 * restore the NS state, and reenable traps in CPTR_EL2.
	 */
	if (rec->fpu_ctx.used) {
		unsigned long cptr;

		cptr = read_cptr_el2();
		cptr &= ~MASK(CPTR_EL2_ZEN);
		cptr |= INPLACE(CPTR_EL2_ZEN, CPTR_EL2_ZEN_NO_TRAP_11);
		write_cptr_el2(cptr);
		isb();

		fpu_save_state(&rec->fpu_ctx.fpu);
		if (ns_state->sve != NULL) {
			restore_sve_state(ns_state->sve);
		} else {
			assert(ns_state->fpu != NULL);
			fpu_restore_state(ns_state->fpu);
		}

		cptr = read_cptr_el2();
		cptr &= ~(MASK(CPTR_EL2_FPEN) | MASK(CPTR_EL2_ZEN));
		cptr |= INPLACE(CPTR_EL2_FPEN, CPTR_EL2_FPEN_TRAP_ALL_00) |
			INPLACE(CPTR_EL2_ZEN, CPTR_EL2_ZEN_TRAP_ALL_00);
		write_cptr_el2(cptr);
		isb();
		rec->fpu_ctx.used = false;
	}

	/*
	 * Clear FPU/SVE context while exiting
	 */
	ns_state->sve = NULL;
	ns_state->fpu = NULL;

	/*
	 * Clear NS pointer since that struct is local to this function.
	 */
	rec->ns = NULL;

	report_timer_state_to_ns(rec_exit);

	save_realm_state(rec);
	restore_ns_state(ns_state);

	/* Undo the heap association */
	attestation_heap_ctx_unassign_pe();
	/* Unmap auxiliary granules */
	unmap_rec_aux(rec_aux, rec->num_rec_aux);
}
