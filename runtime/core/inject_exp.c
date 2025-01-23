/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch.h>
#include <arch_helpers.h>
#include <assert.h>
#include <debug.h>
#include <inject_exp.h>
#include <rec.h>

/*
 * Calculate the address of the vector entry when an exception is inserted
 * into the Realm.
 *
 * @vbar The base address of the vector table in the Realm.
 * @spsr The Saved Program Status Register at EL2.
 * @apply_sea_ease_offset Flag indicating whether we need to apply an offset
 *			  to the vector entry to execute SERROR vector.
 */
static unsigned long calc_vector_entry(unsigned long vbar, unsigned long spsr,
				       bool apply_sea_ease_offset)
{
	unsigned long offset;

	if ((spsr & MASK(SPSR_EL2_MODE)) == SPSR_EL2_MODE_EL1h) {
		offset = VBAR_CEL_SP_ELx_OFFSET;
	} else if ((spsr & MASK(SPSR_EL2_MODE)) == SPSR_EL2_MODE_EL1t) {
		offset = VBAR_CEL_SP_EL0_OFFSET;
	} else if ((spsr & MASK(SPSR_EL2_MODE)) == SPSR_EL2_MODE_EL0t) {
		if ((spsr & MASK(SPSR_EL2_nRW)) == SPSR_EL2_nRW_AARCH64) {
			offset = VBAR_LEL_AA64_OFFSET;
		} else {
			offset = VBAR_LEL_AA32_OFFSET;
			return vbar + offset;
		}
	} else {
		assert(false);
		offset = 0UL;
	}

	if (apply_sea_ease_offset) {
		offset += VBAR_SERROR_OFFSET;
	}

	return vbar + offset;
}

/*
 * Explicitly create all bits of SPSR to get PSTATE when an exception is
 * injected into the Realm.
 *
 * The code is based on "Aarch64.exceptions.takeexception" described in
 * DDI0602 revision 2023-06.
 * "https://developer.arm.com/documentation/ddi0602/2023-06/Shared-Pseudocode/aarch64-exceptions-takeexception?lang=en"
 *
 * NOTE: This piece of code must be reviewed every release to ensure that
 * we keep up with new ARCH features which introduces a new SPSR bit.
 */
static unsigned long calc_spsr(unsigned long old_spsr,
			       unsigned long old_sctlr)
{
	/* Set the mode */
	unsigned long spsr = SPSR_EL2_MODE_EL1h;

	/* Mask all exceptions, update DAIF bits */
	spsr |= MASK(SPSR_EL2_DAIF);

	/*
	 * BTYPE bits are cleared as FEAT_BTI is mandatory since
	 * v9.2 of the architecture.
	 */
	spsr &= ~MASK(SPSR_EL2_BTYPE);

	/*
	 * If SSBS is implemented, take the value from SCTLR.DSSBS.
	 * Otherwise, SPSR.SSBS = RES0.
	 */
	if (is_feat_ssbs_present()) {
		if ((old_sctlr & SCTLR_ELx_DSSBS_BIT) != 0UL) {
			spsr |= SPSR_EL2_SSBS_BIT;
		} else {
			spsr &= ~SPSR_EL2_SSBS_BIT;
		}
	}

	/*
	 * If FEAT_NMI is implemented, ALLINT = !(SCTLR.SPINTMASK).
	 * Otherwise, SPSR.ALLINT = RES0.
	 */
	if (is_feat_nmi_present()) {
		if ((old_sctlr & SCTLR_ELx_SPINTMASK_BIT) == 0UL) {
			spsr |= SPSR_EL2_ALLINT_BIT;
		} else {
			spsr &= ~SPSR_EL2_ALLINT_BIT;
		}
	}

	/* Clear PSTATE.IL bit explicitly */
	spsr &= ~SPSR_EL2_IL_BIT;

	/* Clear PSTATE.SS bit explicitly */
	spsr &= ~SPSR_EL2_SS_BIT;

	/*
	 * Update PSTATE.PAN bit.
	 * FEAT_PAN is mandatory from v8.1.
	 */
	if ((old_sctlr & SCTLR_ELx_SPAN_BIT) == 0UL) {
		spsr |= SPSR_EL2_PAN_BIT;
	}

	/*
	 * UAO bit is cleared as FEAT_UAO is mandatory since
	 * v9.2 of the architecture.
	 */
	spsr &= ~SPSR_EL2_UAO_BIT;

	/* DIT bit is unchanged */
	spsr |= (old_spsr & SPSR_EL2_DIT_BIT);

	/*
	 * If FEAT_MTE2 is implemented, mask tag faults by setting TCO bit.
	 * Otherwise, SPSR.TCO = RES0.
	 */
	if (is_feat_mte2_present()) {
		spsr |= SPSR_EL2_TCO_BIT;
	}

	/* NZCV bits are unchanged */
	spsr |= (old_spsr & MASK(SPSR_EL2_NZCV_BITS));

	/*
	 * If FEAT_EBEP is present, set PM bit.
	 * Otherwise, SPSR.PM = RES0.
	 */
	if (is_feat_ebep_present()) {
		spsr |= SPSR_EL2_PM_BIT;
	}

	/*
	 * If FEAT_SEBEP is present, explicitly clear PPEND bit.
	 * Otherwise, SPSR.PPEND = RES0.
	 */
	if (is_feat_sebep_present()) {
		spsr &= ~SPSR_EL2_PPEND_BIT;
	}

	/*
	 * If FEAT_GCS is present, update EXLOCK bit.
	 * Otherwise, SPSR.EXLOCK = RES0.
	 */
	if (is_feat_gcs_present()) {
		if ((read_gcscr_el12() & GCSCR_EXLOCK_EN_BIT) != 0UL) {
			spsr |= SPSR_EL2_EXLOCK_BIT;
		} else {
			spsr &= ~SPSR_EL2_EXLOCK_BIT;
		}
	}

	return spsr;
}

/*
 * Calculate the content of the Realm's esr_el1 register when
 * the Synchronous Instruction or Data Abort is injected into
 * the Realm (EL1).
 *
 * The value is constructed from the @esr_el2 & @spsr_el2 that
 * are captured when the exception from the Realm was taken to EL2.
 *
 * The fault status code (ESR_EL1.I/DFSC) is set to @fsc
 */
static unsigned long calc_esr_idabort(unsigned long esr_el2,
				      unsigned long spsr_el2,
				      unsigned long fsc)
{
	/*
	 * Copy esr_el2 into esr_el1 apart from the following fields:
	 * - The exception class (EC). Its value depends on whether the
	 *   exception to EL2 was from either EL1 or EL0.
	 * - I/DFSC. It will be set to @fsc.
	 * - FnV. It will set to zero.
	 * - S1PTW. It will be set to zero.
	 */
	unsigned long esr_el1 = esr_el2 & ~(MASK(ESR_EL2_EC)	    |
					    MASK(ESR_EL2_ABORT_FSC) |
					    ESR_EL2_ABORT_FNV_BIT   |
					    ESR_EL2_ABORT_S1PTW_BIT);

	unsigned long ec = esr_el2 & MASK(ESR_EL2_EC);

	assert((ec == ESR_EL2_EC_INST_ABORT) || (ec == ESR_EL2_EC_DATA_ABORT));
	if ((spsr_el2 & MASK(SPSR_EL2_MODE)) != SPSR_EL2_MODE_EL0t) {
		ec += 1UL << ESR_EL2_EC_SHIFT;
	}
	esr_el1 |= ec;

	/*
	 * Set the I/DFSC.
	 */
	assert((fsc & ~MASK(ESR_EL2_ABORT_FSC)) == 0UL);
	esr_el1 |= fsc;

	/*
	 * Set the EA.
	 */
	esr_el1 |= ESR_EL2_ABORT_EA_BIT;

	return esr_el1;
}

/*
 * Inject the Synchronous Instruction or Data Abort into the current REC.
 * The I/DFSC field in the ESR_EL1 is set to @fsc
 */
void inject_sync_idabort(unsigned long fsc)
{
	unsigned long esr_el2 = read_esr_el2();
	unsigned long far_el2 = read_far_el2();
	unsigned long elr_el2 = read_elr_el2();
	unsigned long spsr_el2 = read_spsr_el2();
	unsigned long vbar_el1 = read_vbar_el12();
	unsigned long sctlr_el1 = read_sctlr_el12();

	unsigned long esr_el1 = calc_esr_idabort(esr_el2, spsr_el2, fsc);
	bool sctlr2_ease_bit = ((read_sctlr2_el12_if_present() &
				 SCTLR2_ELx_EASE_BIT) != 0UL);
	unsigned long pc = calc_vector_entry(vbar_el1, spsr_el2,
					     sctlr2_ease_bit);
	unsigned long spsr = calc_spsr(spsr_el2, sctlr_el1);

	write_far_el12(far_el2);
	write_elr_el12(elr_el2);
	write_spsr_el12(spsr_el2);
	write_esr_el12(esr_el1);
	write_elr_el2(pc);
	write_spsr_el2(spsr);

	INFO("Inject Sync EA into current REC. FAR_EL2: 0x%lx, ELR_EL2: 0x%lx\n",
			far_el2, elr_el2);
}

/*
 * Inject the Synchronous Instruction or Data Abort into @rec.
 * The I/DFSC field in the ESR_EL1 is set to @fsc
 */
void inject_sync_idabort_rec(struct rec *rec, unsigned long fsc)
{
	struct rec_plane *plane = rec_active_plane(rec);
	bool sctlr2_ease_bit;

	sctlr2_ease_bit = ((plane->sysregs->pp_sysregs.sctlr2_el1 &
			    SCTLR2_ELx_EASE_BIT) != 0UL);

	plane->sysregs->pp_sysregs.far_el1 = plane->last_run_info.far;
	plane->sysregs->pp_sysregs.elr_el1 = plane->pc;
	plane->sysregs->pp_sysregs.spsr_el1 = plane->sysregs->pstate;
	plane->sysregs->pp_sysregs.esr_el1 =
		calc_esr_idabort(plane->last_run_info.esr,
						  plane->sysregs->pstate, fsc);
	plane->pc = calc_vector_entry(plane->sysregs->pp_sysregs.vbar_el1,
				      plane->sysregs->pstate, sctlr2_ease_bit);
	plane->sysregs->pstate =
		calc_spsr(plane->sysregs->pstate, plane->sysregs->pp_sysregs.sctlr_el1);

	INFO("Inject Sync EA into Plane %u of REC 0x%lx FAR_EL1: 0x%lx, ELR_EL1: 0x%lx\n",
			rec->active_plane_id, (unsigned long)rec,
			plane->sysregs->pp_sysregs.far_el1,
			plane->sysregs->pp_sysregs.elr_el1);
}

/*
 * Inject the Undefined Synchronous Exception into the current REC.
 */
void realm_inject_undef_abort(void)
{
	unsigned long esr = MASK(ESR_EL2_IL) | ESR_EL2_EC_UNKNOWN;
	unsigned long elr = read_elr_el2();
	unsigned long spsr = read_spsr_el2();
	unsigned long vbar = read_vbar_el12();
	unsigned long sctlr = read_sctlr_el12();

	unsigned long pc = calc_vector_entry(vbar, spsr, false);
	unsigned long new_spsr = calc_spsr(spsr, sctlr);

	write_elr_el12(elr);
	write_spsr_el12(spsr);
	write_esr_el12(esr);

	write_elr_el2(pc);
	write_spsr_el2(new_spsr);
}
