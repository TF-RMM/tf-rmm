/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

/* TODO: This file will need clean up */

#ifndef ARCH_HELPERS_H
#define ARCH_HELPERS_H

#include <arch.h>
#include <instr_helpers.h>
#include <stdbool.h>
#include <stddef.h>

/* Define read function for system register */
#define DEFINE_SYSREG_READ_FUNC(_name)			\
	DEFINE_SYSREG_READ_FUNC_(_name, _name)

/* Define read & write function for system register */
#define DEFINE_SYSREG_RW_FUNCS(_name)			\
	DEFINE_SYSREG_READ_FUNC_(_name, _name)		\
	DEFINE_SYSREG_WRITE_FUNC_(_name, _name)

/* Define read & write function for renamed system register */
#define DEFINE_RENAME_SYSREG_RW_FUNCS(_name, _reg_name)	\
	DEFINE_SYSREG_READ_FUNC_(_name, _reg_name)	\
	DEFINE_SYSREG_WRITE_FUNC_(_name, _reg_name)

/* Define read function for renamed system register */
#define DEFINE_RENAME_SYSREG_READ_FUNC(_name, _reg_name)	\
	DEFINE_SYSREG_READ_FUNC_(_name, _reg_name)

/* Define write function for renamed system register */
#define DEFINE_RENAME_SYSREG_WRITE_FUNC(_name, _reg_name)	\
	DEFINE_SYSREG_WRITE_FUNC_(_name, _reg_name)

/*******************************************************************************
 * TLB maintenance accessor prototypes
 ******************************************************************************/
DEFINE_SYSOP_TYPE_FUNC(tlbi, alle1)
DEFINE_SYSOP_TYPE_FUNC(tlbi, alle1is)
DEFINE_SYSOP_TYPE_FUNC(tlbi, alle2)
DEFINE_SYSOP_TYPE_FUNC(tlbi, alle2is)
DEFINE_SYSOP_TYPE_FUNC(tlbi, vmalle1)
DEFINE_SYSOP_TYPE_FUNC(tlbi, vmalle1is)
DEFINE_SYSOP_TYPE_FUNC(tlbi, vmalls12e1)

DEFINE_SYSOP_TYPE_PARAM_FUNC(tlbi, vaae1is)
DEFINE_SYSOP_TYPE_PARAM_FUNC(tlbi, vaale1is)
DEFINE_SYSOP_TYPE_PARAM_FUNC(tlbi, vae2)
DEFINE_SYSOP_TYPE_PARAM_FUNC(tlbi, vae2is)
DEFINE_SYSOP_TYPE_PARAM_FUNC(tlbi, vale2is)
DEFINE_SYSOP_TYPE_PARAM_FUNC(tlbi, ipas2e1is)

/*******************************************************************************
 * Cache maintenance accessor prototypes
 ******************************************************************************/
DEFINE_SYSOP_TYPE_PARAM_FUNC(dc, isw)
DEFINE_SYSOP_TYPE_PARAM_FUNC(dc, cisw)
DEFINE_SYSOP_TYPE_PARAM_FUNC(dc, csw)
DEFINE_SYSOP_TYPE_PARAM_FUNC(dc, cvac)
DEFINE_SYSOP_TYPE_PARAM_FUNC(dc, ivac)
DEFINE_SYSOP_TYPE_PARAM_FUNC(dc, civac)
DEFINE_SYSOP_TYPE_PARAM_FUNC(dc, cvau)
DEFINE_SYSOP_DCZVA

/*******************************************************************************
 * Address translation accessor prototypes
 ******************************************************************************/
DEFINE_SYSOP_TYPE_PARAM_FUNC(at, s12e1r)
DEFINE_SYSOP_TYPE_PARAM_FUNC(at, s12e1w)
DEFINE_SYSOP_TYPE_PARAM_FUNC(at, s12e0r)
DEFINE_SYSOP_TYPE_PARAM_FUNC(at, s12e0w)
DEFINE_SYSOP_TYPE_PARAM_FUNC(at, s1e1r)
DEFINE_SYSOP_TYPE_PARAM_FUNC(at, s1e2r)

/*******************************************************************************
 * Strip Pointer Authentication Code
 ******************************************************************************/
DEFINE_SYSOP_PARAM_FUNC(xpaci)

/*******************************************************************************
 * Cache management
 ******************************************************************************/
void flush_dcache_range(uintptr_t addr, size_t size);
void clean_dcache_range(uintptr_t addr, size_t size);
void inv_dcache_range(uintptr_t addr, size_t size);

#define is_dcache_enabled() ((read_sctlr_el2() & SCTLR_ELx_C_BIT) != 0UL)

/*******************************************************************************
 * MMU management
 ******************************************************************************/
#define is_mmu_enabled() ((read_sctlr_el2() & SCTLR_ELx_M_BIT) != 0UL)

/*******************************************************************************
 * FPU management
 ******************************************************************************/
#define is_fpen_enabled() (EXTRACT(CPTR_EL2_VHE_FPEN, read_cptr_el2()) == \
					CPTR_EL2_VHE_FPEN_NO_TRAP_11)

/*******************************************************************************
 * SVE management
 ******************************************************************************/
#define is_zen_enabled() (EXTRACT(CPTR_EL2_VHE_ZEN, read_cptr_el2()) == \
			  CPTR_EL2_VHE_ZEN_NO_TRAP_11)

/*******************************************************************************
 * SME management
 ******************************************************************************/
#define is_smen_enabled() (EXTRACT(CPTR_EL2_SMEN, read_cptr_el2()) == \
			   CPTR_EL2_SMEN_NO_TRAP_11)

/*******************************************************************************
 * Misc. accessor prototypes
 ******************************************************************************/
#define write_daifclr(val) SYSREG_WRITE_CONST(daifclr, val)
#define write_daifset(val) SYSREG_WRITE_CONST(daifset, val)

DEFINE_SYSOP_FUNC(wfi)
DEFINE_SYSOP_FUNC(wfe)
DEFINE_SYSOP_FUNC(sev)
DEFINE_SYSOP_FUNC(isb)

/*******************************************************************************
 * Stack Pointer Select
 ******************************************************************************/
#define write_spsel(val) SYSREG_WRITE_CONST(spsel, val)

/*******************************************************************************
 * Read Stack Pointer
 ******************************************************************************/
#define read_sp(var) READ_REGISTER(var, sp)

static inline void enable_irq(void)
{
	/*
	 * The compiler memory barrier will prevent the compiler from
	 * scheduling non-volatile memory access after the write to the
	 * register.
	 *
	 * This could happen if some initialization code issues non-volatile
	 * accesses to an area used by an interrupt handler, in the assumption
	 * that it is safe as the interrupts are disabled at the time it does
	 * that (according to program order). However, non-volatile accesses
	 * are not necessarily in program order relatively with volatile inline
	 * assembly statements (and volatile accesses).
	 */
	COMPILER_BARRIER();
	write_daifclr(DAIF_IRQ_BIT);
	isb();
}

static inline void enable_fiq(void)
{
	COMPILER_BARRIER();
	write_daifclr(DAIF_FIQ_BIT);
	isb();
}

static inline void enable_serror(void)
{
	COMPILER_BARRIER();
	write_daifclr(DAIF_ABT_BIT);
	isb();
}

static inline void enable_debug_exceptions(void)
{
	COMPILER_BARRIER();
	write_daifclr(DAIF_DBG_BIT);
	isb();
}

static inline void disable_irq(void)
{
	COMPILER_BARRIER();
	write_daifset(DAIF_IRQ_BIT);
	isb();
}

static inline void disable_fiq(void)
{
	COMPILER_BARRIER();
	write_daifset(DAIF_FIQ_BIT);
	isb();
}

static inline void disable_serror(void)
{
	COMPILER_BARRIER();
	write_daifset(DAIF_ABT_BIT);
	isb();
}

static inline void disable_debug_exceptions(void)
{
	COMPILER_BARRIER();
	write_daifset(DAIF_DBG_BIT);
	isb();
}

/*******************************************************************************
 * System register accessor prototypes
 ******************************************************************************/
DEFINE_SYSREG_RW_FUNCS(sp_el0)
DEFINE_SYSREG_RW_FUNCS(sp_el1)
DEFINE_SYSREG_RW_FUNCS(elr_el12)
DEFINE_SYSREG_RW_FUNCS(spsr_el12)

DEFINE_SYSREG_RW_FUNCS(pmccfiltr_el0)
DEFINE_SYSREG_RW_FUNCS(pmccntr_el0)
DEFINE_SYSREG_RW_FUNCS(pmcntenclr_el0)
DEFINE_SYSREG_RW_FUNCS(pmcntenset_el0)
DEFINE_SYSREG_RW_FUNCS(pmcr_el0)
DEFINE_SYSREG_RW_FUNCS(pmintenclr_el1)
DEFINE_SYSREG_RW_FUNCS(pmintenset_el1)
DEFINE_SYSREG_RW_FUNCS(pmovsclr_el0)
DEFINE_SYSREG_RW_FUNCS(pmovsset_el0)
DEFINE_SYSREG_RW_FUNCS(pmselr_el0)
DEFINE_SYSREG_RW_FUNCS(pmuserenr_el0)
DEFINE_SYSREG_RW_FUNCS(pmxevcntr_el0)
DEFINE_SYSREG_RW_FUNCS(pmxevtyper_el0)

DEFINE_SYSREG_RW_FUNCS(pmevcntr0_el0)
DEFINE_SYSREG_RW_FUNCS(pmevcntr1_el0)
DEFINE_SYSREG_RW_FUNCS(pmevcntr2_el0)
DEFINE_SYSREG_RW_FUNCS(pmevcntr3_el0)
DEFINE_SYSREG_RW_FUNCS(pmevcntr4_el0)
DEFINE_SYSREG_RW_FUNCS(pmevcntr5_el0)
DEFINE_SYSREG_RW_FUNCS(pmevcntr6_el0)
DEFINE_SYSREG_RW_FUNCS(pmevcntr7_el0)
DEFINE_SYSREG_RW_FUNCS(pmevcntr8_el0)
DEFINE_SYSREG_RW_FUNCS(pmevcntr9_el0)
DEFINE_SYSREG_RW_FUNCS(pmevcntr10_el0)
DEFINE_SYSREG_RW_FUNCS(pmevcntr11_el0)
DEFINE_SYSREG_RW_FUNCS(pmevcntr12_el0)
DEFINE_SYSREG_RW_FUNCS(pmevcntr13_el0)
DEFINE_SYSREG_RW_FUNCS(pmevcntr14_el0)
DEFINE_SYSREG_RW_FUNCS(pmevcntr15_el0)
DEFINE_SYSREG_RW_FUNCS(pmevcntr16_el0)
DEFINE_SYSREG_RW_FUNCS(pmevcntr17_el0)
DEFINE_SYSREG_RW_FUNCS(pmevcntr18_el0)
DEFINE_SYSREG_RW_FUNCS(pmevcntr19_el0)
DEFINE_SYSREG_RW_FUNCS(pmevcntr20_el0)
DEFINE_SYSREG_RW_FUNCS(pmevcntr21_el0)
DEFINE_SYSREG_RW_FUNCS(pmevcntr22_el0)
DEFINE_SYSREG_RW_FUNCS(pmevcntr23_el0)
DEFINE_SYSREG_RW_FUNCS(pmevcntr24_el0)
DEFINE_SYSREG_RW_FUNCS(pmevcntr25_el0)
DEFINE_SYSREG_RW_FUNCS(pmevcntr26_el0)
DEFINE_SYSREG_RW_FUNCS(pmevcntr27_el0)
DEFINE_SYSREG_RW_FUNCS(pmevcntr28_el0)
DEFINE_SYSREG_RW_FUNCS(pmevcntr29_el0)
DEFINE_SYSREG_RW_FUNCS(pmevcntr30_el0)

DEFINE_SYSREG_RW_FUNCS(pmevtyper0_el0)
DEFINE_SYSREG_RW_FUNCS(pmevtyper1_el0)
DEFINE_SYSREG_RW_FUNCS(pmevtyper2_el0)
DEFINE_SYSREG_RW_FUNCS(pmevtyper3_el0)
DEFINE_SYSREG_RW_FUNCS(pmevtyper4_el0)
DEFINE_SYSREG_RW_FUNCS(pmevtyper5_el0)
DEFINE_SYSREG_RW_FUNCS(pmevtyper6_el0)
DEFINE_SYSREG_RW_FUNCS(pmevtyper7_el0)
DEFINE_SYSREG_RW_FUNCS(pmevtyper8_el0)
DEFINE_SYSREG_RW_FUNCS(pmevtyper9_el0)
DEFINE_SYSREG_RW_FUNCS(pmevtyper10_el0)
DEFINE_SYSREG_RW_FUNCS(pmevtyper11_el0)
DEFINE_SYSREG_RW_FUNCS(pmevtyper12_el0)
DEFINE_SYSREG_RW_FUNCS(pmevtyper13_el0)
DEFINE_SYSREG_RW_FUNCS(pmevtyper14_el0)
DEFINE_SYSREG_RW_FUNCS(pmevtyper15_el0)
DEFINE_SYSREG_RW_FUNCS(pmevtyper16_el0)
DEFINE_SYSREG_RW_FUNCS(pmevtyper17_el0)
DEFINE_SYSREG_RW_FUNCS(pmevtyper18_el0)
DEFINE_SYSREG_RW_FUNCS(pmevtyper19_el0)
DEFINE_SYSREG_RW_FUNCS(pmevtyper20_el0)
DEFINE_SYSREG_RW_FUNCS(pmevtyper21_el0)
DEFINE_SYSREG_RW_FUNCS(pmevtyper22_el0)
DEFINE_SYSREG_RW_FUNCS(pmevtyper23_el0)
DEFINE_SYSREG_RW_FUNCS(pmevtyper24_el0)
DEFINE_SYSREG_RW_FUNCS(pmevtyper25_el0)
DEFINE_SYSREG_RW_FUNCS(pmevtyper26_el0)
DEFINE_SYSREG_RW_FUNCS(pmevtyper27_el0)
DEFINE_SYSREG_RW_FUNCS(pmevtyper28_el0)
DEFINE_SYSREG_RW_FUNCS(pmevtyper29_el0)
DEFINE_SYSREG_RW_FUNCS(pmevtyper30_el0)

DEFINE_SYSREG_RW_FUNCS(tpidrro_el0)
DEFINE_SYSREG_RW_FUNCS(tpidr_el0)
DEFINE_SYSREG_RW_FUNCS(tpidr_el2)
DEFINE_SYSREG_RW_FUNCS(csselr_el1)
DEFINE_SYSREG_RW_FUNCS(sctlr_el12)
DEFINE_SYSREG_RW_FUNCS(cpacr_el12)
DEFINE_RENAME_SYSREG_RW_FUNCS(zcr_el2, ZCR_EL2)
DEFINE_RENAME_SYSREG_RW_FUNCS(zcr_el12, ZCR_EL12)
DEFINE_RENAME_SYSREG_RW_FUNCS(smcr_el2, SMCR_EL2)
DEFINE_RENAME_SYSREG_RW_FUNCS(svcr, SVCR)
DEFINE_SYSREG_RW_FUNCS(ttbr0_el12)
DEFINE_SYSREG_RW_FUNCS(ttbr1_el12)
DEFINE_SYSREG_RW_FUNCS(tcr_el12)
DEFINE_SYSREG_RW_FUNCS(esr_el12)
DEFINE_SYSREG_RW_FUNCS(afsr0_el12)
DEFINE_SYSREG_RW_FUNCS(afsr1_el12)
DEFINE_SYSREG_RW_FUNCS(far_el12)
DEFINE_SYSREG_RW_FUNCS(mair_el12)
DEFINE_SYSREG_RW_FUNCS(vbar_el12)
DEFINE_SYSREG_RW_FUNCS(contextidr_el12)
DEFINE_SYSREG_RW_FUNCS(tpidr_el1)
DEFINE_SYSREG_RW_FUNCS(amair_el12)
DEFINE_SYSREG_RW_FUNCS(cntkctl_el12)
DEFINE_SYSREG_RW_FUNCS(mdscr_el1)
DEFINE_SYSREG_RW_FUNCS(mdccint_el1)
DEFINE_SYSREG_RW_FUNCS(disr_el1)
DEFINE_SYSREG_RW_FUNCS(cnrv_ctl_el02)
DEFINE_SYSREG_RW_FUNCS(vtcr_el2)
DEFINE_SYSREG_RW_FUNCS(vsesr_el2)
DEFINE_SYSREG_RW_FUNCS(par_el1)
DEFINE_SYSREG_READ_FUNC(id_pfr1_el1)
DEFINE_RENAME_SYSREG_READ_FUNC(ID_AA64AFR0_EL1, id_aa64afr0_el1)
DEFINE_RENAME_SYSREG_READ_FUNC(ID_AA64AFR1_EL1, id_aa64afr1_el1)
DEFINE_RENAME_SYSREG_READ_FUNC(ID_AA64DFR0_EL1, id_aa64dfr0_el1)
DEFINE_RENAME_SYSREG_READ_FUNC(ID_AA64DFR1_EL1, id_aa64dfr1_el1)
DEFINE_RENAME_SYSREG_READ_FUNC(ID_AA64ISAR0_EL1, id_aa64isar0_el1)
DEFINE_RENAME_SYSREG_READ_FUNC(ID_AA64ISAR1_EL1, id_aa64isar1_el1)
DEFINE_RENAME_SYSREG_READ_FUNC(ID_AA64MMFR0_EL1, id_aa64mmfr0_el1)
DEFINE_RENAME_SYSREG_READ_FUNC(ID_AA64MMFR1_EL1, id_aa64mmfr1_el1)
DEFINE_RENAME_SYSREG_READ_FUNC(ID_AA64MMFR2_EL1, id_aa64mmfr2_el1)
DEFINE_RENAME_SYSREG_READ_FUNC(ID_AA64MMFR3_EL1, ID_AA64MMFR3)
DEFINE_RENAME_SYSREG_READ_FUNC(id_aa64mmfr3_el1, ID_AA64MMFR3)
DEFINE_RENAME_SYSREG_READ_FUNC(ID_AA64PFR0_EL1, id_aa64pfr0_el1)
DEFINE_RENAME_SYSREG_READ_FUNC(ID_AA64PFR1_EL1, id_aa64pfr1_el1)
DEFINE_SYSREG_READ_FUNC(id_aa64afr0_el1)
DEFINE_SYSREG_READ_FUNC(id_aa64afr1_el1)
DEFINE_SYSREG_READ_FUNC(id_aa64dfr0_el1)
DEFINE_SYSREG_READ_FUNC(id_aa64dfr1_el1)
DEFINE_RENAME_SYSREG_READ_FUNC(id_aa64zfr0_el1, ID_AA64ZFR0_EL1)
DEFINE_RENAME_SYSREG_READ_FUNC(id_aa64smfr0_el1, ID_AA64SMFR0_EL1)
DEFINE_SYSREG_READ_FUNC(id_aa64isar0_el1)
DEFINE_SYSREG_READ_FUNC(id_aa64isar1_el1)
DEFINE_SYSREG_READ_FUNC(id_aa64mmfr0_el1)
DEFINE_SYSREG_READ_FUNC(id_aa64mmfr1_el1)
DEFINE_SYSREG_READ_FUNC(id_aa64mmfr2_el1)
DEFINE_SYSREG_READ_FUNC(id_aa64pfr0_el1)
DEFINE_SYSREG_READ_FUNC(id_aa64pfr1_el1)
DEFINE_RENAME_SYSREG_RW_FUNCS(mpam0_el1, MPAM0_EL1)
DEFINE_SYSREG_READ_FUNC(id_afr0_el1)
DEFINE_SYSREG_READ_FUNC(CurrentEl)
DEFINE_SYSREG_READ_FUNC(ctr_el0)
DEFINE_SYSREG_RW_FUNCS(daif)
DEFINE_SYSREG_RW_FUNCS(spsr_el1)
DEFINE_SYSREG_RW_FUNCS(spsr_el2)
DEFINE_SYSREG_RW_FUNCS(elr_el1)
DEFINE_SYSREG_RW_FUNCS(elr_el2)

DEFINE_SYSREG_READ_FUNC(midr_el1)
DEFINE_SYSREG_READ_FUNC(mpidr_el1)

DEFINE_SYSREG_RW_FUNCS(hcr_el2)
DEFINE_RENAME_SYSREG_RW_FUNCS(hcrx_el2, HCRX_EL2)

DEFINE_SYSREG_RW_FUNCS(vbar_el1)
DEFINE_SYSREG_RW_FUNCS(vbar_el2)

DEFINE_SYSREG_RW_FUNCS(sctlr_el1)
DEFINE_SYSREG_RW_FUNCS(sctlr_el2)
DEFINE_RENAME_SYSREG_RW_FUNCS(sctlr2_el12, SCTLR2_EL12)

DEFINE_SYSREG_RW_FUNCS(actlr_el1)
DEFINE_SYSREG_RW_FUNCS(actlr_el2)

DEFINE_SYSREG_RW_FUNCS(esr_el1)
DEFINE_SYSREG_RW_FUNCS(esr_el2)

DEFINE_SYSREG_RW_FUNCS(afsr0_el1)
DEFINE_SYSREG_RW_FUNCS(afsr0_el2)

DEFINE_SYSREG_RW_FUNCS(afsr1_el1)
DEFINE_SYSREG_RW_FUNCS(afsr1_el2)

DEFINE_SYSREG_RW_FUNCS(far_el1)
DEFINE_SYSREG_RW_FUNCS(far_el2)
DEFINE_SYSREG_RW_FUNCS(hpfar_el2)

DEFINE_SYSREG_RW_FUNCS(mair_el1)
DEFINE_SYSREG_RW_FUNCS(mair_el2)

DEFINE_SYSREG_RW_FUNCS(amair_el1)
DEFINE_SYSREG_RW_FUNCS(amair_el2)

DEFINE_SYSREG_READ_FUNC(rvbar_el1)
DEFINE_SYSREG_READ_FUNC(rvbar_el2)

DEFINE_SYSREG_RW_FUNCS(rmr_el1)
DEFINE_SYSREG_RW_FUNCS(rmr_el2)

DEFINE_SYSREG_RW_FUNCS(tcr_el1)
DEFINE_SYSREG_RW_FUNCS(tcr_el2)

DEFINE_SYSREG_RW_FUNCS(ttbr0_el1)
DEFINE_SYSREG_RW_FUNCS(ttbr0_el2)
DEFINE_SYSREG_RW_FUNCS(ttbr1_el2)

DEFINE_SYSREG_RW_FUNCS(ttbr1_el1)

DEFINE_SYSREG_RW_FUNCS(vttbr_el2)

DEFINE_SYSREG_RW_FUNCS(cptr_el2)

DEFINE_SYSREG_RW_FUNCS(cpacr_el1)

DEFINE_SYSREG_RW_FUNCS(vpidr_el2)
DEFINE_SYSREG_RW_FUNCS(vmpidr_el2)

DEFINE_SYSREG_READ_FUNC(isr_el1)

DEFINE_SYSREG_RW_FUNCS(mdcr_el2)
DEFINE_SYSREG_RW_FUNCS(hstr_el2)
DEFINE_SYSREG_RW_FUNCS(mpam2_el2)
DEFINE_SYSREG_RW_FUNCS(mpamhcr_el2)
DEFINE_SYSREG_RW_FUNCS(pmscr_el2)

DEFINE_RENAME_SYSREG_RW_FUNCS(fpcr, FPCR)
DEFINE_RENAME_SYSREG_RW_FUNCS(fpsr, FPSR)

DEFINE_SYSREG_READ_FUNC(dczid_el0)

DEFINE_RENAME_SYSREG_RW_FUNCS(dit, DIT)

/*******************************************************************************
 * Timer register accessor prototypes
 ******************************************************************************/
DEFINE_SYSREG_RW_FUNCS(cntfrq_el0)
DEFINE_SYSREG_RW_FUNCS(cnthp_ctl_el2)
DEFINE_SYSREG_RW_FUNCS(cnthp_tval_el2)
DEFINE_SYSREG_RW_FUNCS(cnthp_cval_el2)
DEFINE_SYSREG_RW_FUNCS(cntps_ctl_el1)
DEFINE_SYSREG_RW_FUNCS(cntps_tval_el1)
DEFINE_SYSREG_RW_FUNCS(cntps_cval_el1)
DEFINE_SYSREG_RW_FUNCS(cntp_ctl_el0)
DEFINE_SYSREG_RW_FUNCS(cntp_tval_el0)
DEFINE_SYSREG_RW_FUNCS(cntp_cval_el0)
DEFINE_SYSREG_READ_FUNC(cntpct_el0)
DEFINE_SYSREG_RW_FUNCS(cnthctl_el2)
DEFINE_SYSREG_RW_FUNCS(cntp_ctl_el02)
DEFINE_SYSREG_RW_FUNCS(cntp_cval_el02)
DEFINE_SYSREG_RW_FUNCS(cntv_ctl_el02)
DEFINE_SYSREG_RW_FUNCS(cntv_cval_el02)
DEFINE_SYSREG_RW_FUNCS(cntvoff_el2)
DEFINE_RENAME_SYSREG_RW_FUNCS(cntpoff_el2, CNTPOFF_EL2)

/*******************************************************************************
 * Interrupt Controller register accessor prototypes
 ******************************************************************************/
DEFINE_RENAME_SYSREG_RW_FUNCS(icc_sre_el2, ICC_SRE_EL2)
DEFINE_RENAME_SYSREG_RW_FUNCS(icc_ctrl_el1, ICC_CTLR_EL1)
DEFINE_RENAME_SYSREG_RW_FUNCS(icc_hppir1_el1, ICC_HPPIR1_EL1)

/*******************************************************************************
 * Virtual GIC register accessor prototypes
 ******************************************************************************/
DEFINE_RENAME_SYSREG_RW_FUNCS(ich_ap0r0_el2, ICH_AP0R0_EL2)
DEFINE_RENAME_SYSREG_RW_FUNCS(ich_ap0r1_el2, ICH_AP0R1_EL2)
DEFINE_RENAME_SYSREG_RW_FUNCS(ich_ap0r2_el2, ICH_AP0R2_EL2)
DEFINE_RENAME_SYSREG_RW_FUNCS(ich_ap0r3_el2, ICH_AP0R3_EL2)
DEFINE_RENAME_SYSREG_RW_FUNCS(ich_ap1r0_el2, ICH_AP1R0_EL2)
DEFINE_RENAME_SYSREG_RW_FUNCS(ich_ap1r1_el2, ICH_AP1R1_EL2)
DEFINE_RENAME_SYSREG_RW_FUNCS(ich_ap1r2_el2, ICH_AP1R2_EL2)
DEFINE_RENAME_SYSREG_RW_FUNCS(ich_ap1r3_el2, ICH_AP1R3_EL2)

DEFINE_RENAME_SYSREG_RW_FUNCS(ich_lr0_el2, ICH_LR0_EL2)
DEFINE_RENAME_SYSREG_RW_FUNCS(ich_lr1_el2, ICH_LR1_EL2)
DEFINE_RENAME_SYSREG_RW_FUNCS(ich_lr2_el2, ICH_LR2_EL2)
DEFINE_RENAME_SYSREG_RW_FUNCS(ich_lr3_el2, ICH_LR3_EL2)
DEFINE_RENAME_SYSREG_RW_FUNCS(ich_lr4_el2, ICH_LR4_EL2)
DEFINE_RENAME_SYSREG_RW_FUNCS(ich_lr5_el2, ICH_LR5_EL2)
DEFINE_RENAME_SYSREG_RW_FUNCS(ich_lr6_el2, ICH_LR6_EL2)
DEFINE_RENAME_SYSREG_RW_FUNCS(ich_lr7_el2, ICH_LR7_EL2)
DEFINE_RENAME_SYSREG_RW_FUNCS(ich_lr8_el2, ICH_LR8_EL2)
DEFINE_RENAME_SYSREG_RW_FUNCS(ich_lr9_el2, ICH_LR9_EL2)
DEFINE_RENAME_SYSREG_RW_FUNCS(ich_lr10_el2, ICH_LR10_EL2)
DEFINE_RENAME_SYSREG_RW_FUNCS(ich_lr11_el2, ICH_LR11_EL2)
DEFINE_RENAME_SYSREG_RW_FUNCS(ich_lr12_el2, ICH_LR12_EL2)
DEFINE_RENAME_SYSREG_RW_FUNCS(ich_lr13_el2, ICH_LR13_EL2)
DEFINE_RENAME_SYSREG_RW_FUNCS(ich_lr14_el2, ICH_LR14_EL2)
DEFINE_RENAME_SYSREG_RW_FUNCS(ich_lr15_el2, ICH_LR15_EL2)

DEFINE_RENAME_SYSREG_RW_FUNCS(ich_hcr_el2, ICH_HCR_EL2)
DEFINE_RENAME_SYSREG_RW_FUNCS(ich_vmcr_el2, ICH_VMCR_EL2)
DEFINE_RENAME_SYSREG_READ_FUNC(ich_vtr_el2, ICH_VTR_EL2)
DEFINE_RENAME_SYSREG_READ_FUNC(ich_misr_el2, ICH_MISR_EL2)

/* Armv8.3 Pointer Authentication Registers */
DEFINE_RENAME_SYSREG_RW_FUNCS(apiakeyhi_el1, APIAKeyHi_EL1)
DEFINE_RENAME_SYSREG_RW_FUNCS(apiakeylo_el1, APIAKeyLo_EL1)
DEFINE_RENAME_SYSREG_RW_FUNCS(apibkeyhi_el1, APIBKeyHi_EL1)
DEFINE_RENAME_SYSREG_RW_FUNCS(apibkeylo_el1, APIBKeyLo_EL1)
DEFINE_RENAME_SYSREG_RW_FUNCS(apdakeyhi_el1, APDAKeyHi_EL1)
DEFINE_RENAME_SYSREG_RW_FUNCS(apdakeylo_el1, APDAKeyLo_EL1)
DEFINE_RENAME_SYSREG_RW_FUNCS(apdbkeyhi_el1, APDBKeyHi_EL1)
DEFINE_RENAME_SYSREG_RW_FUNCS(apdbkeylo_el1, APDBKeyLo_EL1)
DEFINE_RENAME_SYSREG_RW_FUNCS(apgakeyhi_el1, APGAKeyHi_EL1)
DEFINE_RENAME_SYSREG_RW_FUNCS(apgakeylo_el1, APGAKeyLo_EL1)

/* Armv8.5 MTE Registers */
DEFINE_RENAME_SYSREG_RW_FUNCS(tfsre0_el1, TFSRE0_EL1)
DEFINE_RENAME_SYSREG_RW_FUNCS(tfsr_el1, TFSR_EL1)
DEFINE_RENAME_SYSREG_RW_FUNCS(rgsr_el1, RGSR_EL1)
DEFINE_RENAME_SYSREG_RW_FUNCS(gcr_el1, GCR_EL1)

/* Armv8.5 Random Number Register */
DEFINE_RENAME_SYSREG_READ_FUNC(rndr, RNDR)

#endif /* ARCH_HELPERS_H */
