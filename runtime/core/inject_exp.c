/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch.h>
#include <arch_helpers.h>
#include <assert.h>
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
 * Calculate the value of the pstate when an exception
 * is inserted into the Realm.
 */
static unsigned long calc_pstate(void)
{
	/*
	 * The pstate is EL1, AArch64, SPSel = SP_ELx and:
	 * DAIF = '1111b'
	 * NZCV = '0000b'
	 * TODO: setup TCO, DIT, UAO, PAN, SSBS, BTYPE
	 */
	unsigned long pstate = SPSR_EL2_MODE_EL1h |
			       SPSR_EL2_nRW_AARCH64 |
			       SPSR_EL2_F_BIT |
			       SPSR_EL2_I_BIT |
			       SPSR_EL2_A_BIT |
			       SPSR_EL2_D_BIT;
	return pstate;
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
	unsigned long vbar_el2 = read_vbar_el12();

	unsigned long esr_el1 = calc_esr_idabort(esr_el2, spsr_el2, fsc);
	bool sctlr2_ease_bit = ((read_sctlr2_el12_if_present() &
				 SCTLR2_ELx_EASE_BIT) != 0UL);
	unsigned long pc = calc_vector_entry(vbar_el2, spsr_el2,
					     sctlr2_ease_bit);
	unsigned long pstate = calc_pstate();

	write_far_el12(far_el2);
	write_elr_el12(elr_el2);
	write_spsr_el12(spsr_el2);
	write_esr_el12(esr_el1);
	write_elr_el2(pc);
	write_spsr_el2(pstate);
}

/*
 * Inject the Synchronous Instruction or Data Abort into @rec.
 * The I/DFSC field in the ESR_EL1 is set to @fsc
 */
void inject_sync_idabort_rec(struct rec *rec, unsigned long fsc)
{
	bool sctlr2_ease_bit = ((rec->sysregs.sctlr2_el1 &
				 SCTLR2_ELx_EASE_BIT) != 0UL);

	rec->sysregs.far_el1 = rec->last_run_info.far;
	rec->sysregs.elr_el1 = rec->pc;
	rec->sysregs.spsr_el1 = rec->pstate;
	rec->sysregs.esr_el1 = calc_esr_idabort(rec->last_run_info.esr,
						rec->pstate, fsc);
	rec->pc = calc_vector_entry(rec->sysregs.vbar_el1, rec->pstate,
				    sctlr2_ease_bit);
	rec->pstate = calc_pstate();
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

	unsigned long pc = calc_vector_entry(vbar, spsr, false);
	unsigned long pstate = calc_pstate();

	write_elr_el12(elr);
	write_spsr_el12(spsr);
	write_esr_el12(esr);

	write_elr_el2(pc);
	write_spsr_el2(pstate);
}
