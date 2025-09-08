/*
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch.h>
#include <arch_features.h>
#include <arch_helpers.h>
#include <debug.h>
#include <esr.h>
#include <inject_exp.h>
#include <rec.h>
#include <smc-rmi.h>
#include <sysreg_traps.h>

#define SYSREG_CASE(reg) \
	case ESR_EL2_SYSREG_##ID_AA64##reg##_EL1:

/*
 * Handle ID_AA64XXX<n>_EL1 instructions
 */
static bool handle_id_sysreg_trap(struct rec *rec,
				  struct rmi_rec_exit *rec_exit,
				  unsigned long esr, bool *skip_adv_pc)
{
	unsigned int rt;
	unsigned long idreg, value;
	unsigned long mask = 0U;

	(void)rec_exit;
	(void)skip_adv_pc;

	/*
	 * We only set HCR_EL2.TID3 to trap ID registers at the moment and
	 * that only traps reads of registers. Seeing a write here indicates a
	 * consistency problem with the RMM and we should panic immediately.
	 */
	assert(!ESR_EL2_SYSREG_IS_WRITE(esr));

	/*
	 * Read Rt value from the issued instruction,
	 * the general-purpose register used for the transfer.
	 * Rt bits [9:5] of ISS field cannot exceed 0b11111.
	 */
	rt = (unsigned int)ESR_EL2_SYSREG_ISS_RT(esr);

	/* Handle writes to XZR register */
	if (rt == 31U) {
		return true;
	}

	idreg = esr & ESR_EL2_SYSREG_MASK;

	switch (idreg) {
	SYSREG_CASE(AFR0)
		value = READ_CACHED_REG(id_aa64afr0_el1);
		break;
	SYSREG_CASE(AFR1)
		value = READ_CACHED_REG(id_aa64afr1_el1);
		break;
	SYSREG_CASE(DFR0)
		value = READ_CACHED_REG(id_aa64dfr0_el1);

		/*
		 * Clear BRBE bits for realms
		 */
		mask = MASK(ID_AA64DFR0_EL1_BRBE);
		value &= ~mask;

		break;
	SYSREG_CASE(DFR1)
		value = READ_CACHED_REG(id_aa64dfr1_el1);
		break;
	SYSREG_CASE(DFR2)
		value = READ_CACHED_REG(id_aa64dfr2_el1);
		break;
	SYSREG_CASE(FPFR0)
		value = READ_CACHED_REG(id_aa64fpfr0_el1);
		break;
	SYSREG_CASE(ISAR0)
		value = READ_CACHED_REG(id_aa64isar0_el1);
		break;
	SYSREG_CASE(ISAR1)
		value = READ_CACHED_REG(id_aa64isar1_el1);
		break;
	SYSREG_CASE(MMFR0)
		value = READ_CACHED_REG(id_aa64mmfr0_el1);
		break;
	SYSREG_CASE(MMFR1)
		value = READ_CACHED_REG(id_aa64mmfr1_el1);
		break;
	SYSREG_CASE(MMFR2)
		value = READ_CACHED_REG(id_aa64mmfr2_el1);
		break;
	SYSREG_CASE(MMFR3)
		value = READ_CACHED_REG(id_aa64mmfr3_el1);
		break;
	SYSREG_CASE(MMFR4)
		value = READ_CACHED_REG(id_aa64mmfr4_el1);
		break;
	SYSREG_CASE(PFR0)
		/*
		 * Workaround for TF-A trapping AMU registers access
		 * to EL3 in Realm state.
		 */
		value = READ_CACHED_REG(id_aa64pfr0_el1);

		/*
		 * Clear SVE, MPAM and AMU bits for current realm.
		 */
		if (rec->realm_info.simd_cfg.sve_en == false) {
			mask = MASK(ID_AA64PFR0_EL1_SVE);
		}
		mask |= (MASK(ID_AA64PFR0_EL1_MPAM) | \
			MASK(ID_AA64PFR0_EL1_AMU));

		value &= ~mask;
		break;
	SYSREG_CASE(PFR1)
		value = READ_CACHED_REG(id_aa64pfr1_el1);

		mask |= (MASK(ID_AA64PFR1_EL1_MPAM_F) | \
			MASK(ID_AA64PFR1_EL1_SME));

		value &= ~mask;
		break;
	SYSREG_CASE(PFR2)
		value = READ_CACHED_REG(id_aa64pfr2_el1);
		break;
	SYSREG_CASE(SMFR0)
		/*
		 * SME not supported for Realms, clear all fields in SME feature
		 * register ID_AA64SMFR0_EL1
		 */
		value = 0UL;
		break;
	SYSREG_CASE(ZFR0)
		if (is_feat_sve_present() && rec->realm_info.simd_cfg.sve_en) {
			value = READ_CACHED_REG(id_aa64zfr0_el1);
		} else {
			value = 0UL;
		}
		break;
	default:
		/* All other encodings are in the RES0 space */
		WARN("Accessing unknown ID register.\n");
		value = 0UL;
	}

	rec->regs[rt] = value;
	return true;
}

static bool handle_icc_el1_sysreg_trap(struct rec *rec,
				       struct rmi_rec_exit *rec_exit,
				       unsigned long esr, bool *skip_adv_pc)
{
	__unused unsigned long sysreg = esr & ESR_EL2_SYSREG_MASK;

	(void)rec;
	(void)skip_adv_pc;

	/*
	 * We should only have configured ICH_HCR_EL2 to trap on DIR and we
	 * always trap on the SGIRs following the architecture, so make sure
	 * we're not accidentally trapping on some other register here.
	 */
	assert((sysreg == ESR_EL2_SYSREG_ICC_DIR) ||
	       (sysreg == ESR_EL2_SYSREG_ICC_SGI1R_EL1) ||
	       (sysreg == ESR_EL2_SYSREG_ICC_SGI0R_EL1));

	/*
	 * The registers above should only trap to EL2 for writes, read
	 * instructions are not defined and should cause an Undefined exception
	 * at EL1.
	 */
	assert(ESR_EL2_SYSREG_IS_WRITE(esr));

	rec_exit->exit_reason = RMI_EXIT_SYNC;
	rec_exit->esr = esr;
	return false;
}

static bool inject_undef_abort_on_sysreg_trap(struct rec *rec,
					      struct rmi_rec_exit *rec_exit,
					      unsigned long esr, bool *skip_adv_pc)
{
	(void)rec;
	(void)rec_exit;
	(void)esr;

	realm_inject_undef_abort();
	*skip_adv_pc = true;

	return true;
}

typedef bool (*sysreg_handler_fn)(struct rec *rec, struct rmi_rec_exit *rec_exit,
				  unsigned long esr, bool *skip_adv_pc);

struct sysreg_handler {
	unsigned long esr_mask;
	unsigned long esr_value;
	sysreg_handler_fn fn;
};

#define SYSREG_HANDLER(_mask, _value, _handler_fn) \
	{ .esr_mask = (_mask), .esr_value = (_value), .fn = (_handler_fn) }

static const struct sysreg_handler sysreg_handlers[] = {
	SYSREG_HANDLER(ESR_EL2_SYSREG_ID_MASK, ESR_EL2_SYSREG_ID,
		       handle_id_sysreg_trap),
	SYSREG_HANDLER(ESR_EL2_SYSREG_ICC_EL1_MASK, ESR_EL2_SYSREG_ICC_EL1,
		       handle_icc_el1_sysreg_trap),
	SYSREG_HANDLER(ESR_EL2_SYSREG_MASK, ESR_EL2_SYSREG_ICC_PMR_EL1,
		       handle_icc_el1_sysreg_trap),
	SYSREG_HANDLER(ESR_EL2_SYSREG_BRBE_MASK, ESR_EL2_SYSREG_BRBE,
			inject_undef_abort_on_sysreg_trap),
	SYSREG_HANDLER(ESR_EL2_SYSREG_MPAM_MASK, ESR_EL2_SYSREG_MPAM,
			inject_undef_abort_on_sysreg_trap)
};

static unsigned long get_sysreg_write_value(struct rec *rec, unsigned long esr)
{
	/* Rt bits [9:5] of ISS field cannot exceed 0b11111 */
	unsigned int rt = (unsigned int)ESR_EL2_SYSREG_ISS_RT(esr);

	/* Handle reads from XZR register */
	if (rt == 31U) {
		return 0UL;
	}

	return rec->regs[rt];
}

static void emulate_sysreg_access_ns(struct rec *rec,
				     struct rmi_rec_exit *rec_exit,
				     unsigned long esr)
{
	if (ESR_EL2_SYSREG_IS_WRITE(esr)) {
		rec_exit->gprs[0] = get_sysreg_write_value(rec, esr);
	}
}

/*
 * Handle trapped MSR, MRS or System instruction execution
 * in AArch64 state
 */
bool handle_sysreg_access_trap(struct rec *rec, struct rmi_rec_exit *rec_exit,
			       unsigned long esr)
{
	/*
	 * Read Rt value from the issued instruction,
	 * the general-purpose register used for the transfer.
	 * Rt bits [9:5] of ISS field cannot exceed 0b11111.
	 */
	unsigned int rt = (unsigned int)ESR_EL2_SYSREG_ISS_RT(esr);
	unsigned int __unused op0, op1, crn, crm, op2;
	unsigned long __unused sysreg;
	bool skip_advance_pc = false;

	/* Check for 32-bit instruction trapped */
	assert(ESR_IL(esr) != 0UL);

	/* cppcheck-suppress misra-c2012-14.2 */
	for (unsigned int i = 0U; i < ARRAY_SIZE(sysreg_handlers); i++) {
		const struct sysreg_handler *handler = &sysreg_handlers[i];

		if ((esr & handler->esr_mask) == handler->esr_value) {
			bool handled = handler->fn(rec, rec_exit, esr, &skip_advance_pc);

			if (!handled) {
				emulate_sysreg_access_ns(rec, rec_exit, esr);
			}
			if (!skip_advance_pc) {
				advance_pc();
			}

			return handled;
		}
	}

	/*
	 * For now, treat all unhandled accesses as RAZ/WI.
	 * Handle writes to XZR register.
	 */
	if (!ESR_EL2_SYSREG_IS_WRITE(esr) && (rt != 31U)) {
		rec->regs[rt] = 0UL;
	}

	sysreg = esr & ESR_EL2_SYSREG_MASK;

	/* Extract sytem register encoding */
	op0 = (unsigned int)EXTRACT(ESR_EL2_SYSREG_TRAP_OP0, sysreg);
	op1 = (unsigned int)EXTRACT(ESR_EL2_SYSREG_TRAP_OP1, sysreg);
	crn = (unsigned int)EXTRACT(ESR_EL2_SYSREG_TRAP_CRN, sysreg);
	crm = (unsigned int)EXTRACT(ESR_EL2_SYSREG_TRAP_CRM, sysreg);
	op2 = (unsigned int)EXTRACT(ESR_EL2_SYSREG_TRAP_OP2, sysreg);

	INFO("Unhandled %s S%u_%u_C%u_C%u_%u\n",
		ESR_EL2_SYSREG_IS_WRITE(esr) ? "write" : "read",
		op0, op1, crn, crm, op2);

	advance_pc();
	return true;
}
