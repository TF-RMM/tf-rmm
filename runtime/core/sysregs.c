/*
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch.h>
#include <arch_helpers.h>
#include <debug.h>
#include <esr.h>
#include <memory_alloc.h>
#include <rec.h>
#include <smc-rmi.h>

#define SYSREG_READ_CASE(reg) \
	case ESR_EL2_SYSREG_##reg: return read_##reg()

static unsigned long read_idreg(unsigned int idreg)
{
	switch (idreg) {
	SYSREG_READ_CASE(ID_AA64PFR0_EL1);
	SYSREG_READ_CASE(ID_AA64PFR1_EL1);
	/*
	 * TODO: not supported without SVE:
	 * SYSREG_READ_CASE(ID_AA64ZFR0_EL1);
	 */
	SYSREG_READ_CASE(ID_AA64DFR0_EL1);
	SYSREG_READ_CASE(ID_AA64DFR1_EL1);
	SYSREG_READ_CASE(ID_AA64AFR0_EL1);
	SYSREG_READ_CASE(ID_AA64AFR1_EL1);
	SYSREG_READ_CASE(ID_AA64ISAR0_EL1);
	SYSREG_READ_CASE(ID_AA64ISAR1_EL1);
	SYSREG_READ_CASE(ID_AA64MMFR0_EL1);
	SYSREG_READ_CASE(ID_AA64MMFR1_EL1);
	SYSREG_READ_CASE(ID_AA64MMFR2_EL1);

	default:
		/* All other encodings are in the RES0 space */
		return 0UL;
	}
}

/*
 * Handle ID_AA64XXX<n>_EL1 instructions
 */
static bool handle_id_sysreg_trap(struct rec *rec,
				  struct rmi_rec_exit *rec_exit,
				  unsigned long esr)
{
	unsigned int rt;
	unsigned long idreg, mask;

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
	rt = ESR_EL2_SYSREG_ISS_RT(esr);

	/* Handle writes to XZR register */
	if (rt == 31U) {
		return true;
	}

	idreg = esr & ESR_EL2_SYSREG_MASK;

	if (idreg == ESR_EL2_SYSREG_ID_AA64ISAR1_EL1) {
		/* Clear Address and Generic Authentication bits */
		mask = (0xfUL << ESR_EL2_SYSREG_ID_AA64ISAR1_APA_SHIFT) |
		       (0xfUL << ESR_EL2_SYSREG_ID_AA64ISAR1_API_SHIFT) |
		       (0xfUL << ESR_EL2_SYSREG_ID_AA64ISAR1_GPA_SHIFT) |
		       (0xfUL << ESR_EL2_SYSREG_ID_AA64ISAR1_GPI_SHIFT);
	/*
	 * Workaround for TF-A trapping AMU registers access
	 * to EL3 in Realm state
	 */
	} else if (idreg == ESR_EL2_SYSREG_ID_AA64PFR0_EL1) {
		/* Clear support for Activity Monitors Extension */
		mask = MASK(ID_AA64PFR0_EL1_AMU);

		/*
		 * Clear support for SVE. This is a temporary fix until RMM
		 * completely supports SVE.
		 */
		mask |= MASK(ID_AA64PFR0_EL1_SVE);
	} else {
		mask = 0UL;
	}

	rec->regs[rt] = read_idreg(idreg) & ~mask;
	return true;
}

static bool handle_icc_el1_sysreg_trap(struct rec *rec,
				       struct rmi_rec_exit *rec_exit,
				       unsigned long esr)
{
	__unused unsigned long sysreg = esr & ESR_EL2_SYSREG_MASK;

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

typedef bool (*sysreg_handler_fn)(struct rec *rec, struct rmi_rec_exit *rec_exit,
				  unsigned long esr);

struct sysreg_handler {
	unsigned long esr_mask;
	unsigned long esr_value;
	sysreg_handler_fn fn;
};

#define SYSREG_HANDLER(_mask, _value, _handler_fn) \
	{ .esr_mask = (_mask), .esr_value = (_value), .fn = _handler_fn }

static const struct sysreg_handler sysreg_handlers[] = {
	SYSREG_HANDLER(ESR_EL2_SYSREG_ID_MASK, ESR_EL2_SYSREG_ID, handle_id_sysreg_trap),
	SYSREG_HANDLER(ESR_EL2_SYSREG_ICC_EL1_MASK, ESR_EL2_SYSREG_ICC_EL1, handle_icc_el1_sysreg_trap),
	SYSREG_HANDLER(ESR_EL2_SYSREG_MASK, ESR_EL2_SYSREG_ICC_PMR_EL1, handle_icc_el1_sysreg_trap)
};

static unsigned long get_sysreg_write_value(struct rec *rec, unsigned long esr)
{
	/* Rt bits [9:5] of ISS field cannot exceed 0b11111 */
	unsigned int rt = ESR_EL2_SYSREG_ISS_RT(esr);

	/* Handle reads from XZR register */
	if (rt == 31U) {
		return 0UL;
	}

	return rec->regs[rt];
}

static void emulate_sysreg_access_ns(struct rec *rec, struct rmi_rec_exit *rec_exit,
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
	unsigned int rt = ESR_EL2_SYSREG_ISS_RT(esr);
	unsigned int __unused op0, op1, crn, crm, op2;
	unsigned long __unused sysreg;

	/* Check for 32-bit instruction trapped */
	assert(ESR_IL(esr) != 0UL);

	for (unsigned int i = 0U; i < ARRAY_LEN(sysreg_handlers); i++) {
		const struct sysreg_handler *handler = &sysreg_handlers[i];

		if ((esr & handler->esr_mask) == handler->esr_value) {
			bool handled = handler->fn(rec, rec_exit, esr);

			if (!handled) {
				emulate_sysreg_access_ns(rec, rec_exit, esr);
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
	op0 = EXTRACT(ESR_EL2_SYSREG_TRAP_OP0, sysreg);
	op1 = EXTRACT(ESR_EL2_SYSREG_TRAP_OP1, sysreg);
	crn = EXTRACT(ESR_EL2_SYSREG_TRAP_CRN, sysreg);
	crm = EXTRACT(ESR_EL2_SYSREG_TRAP_CRM, sysreg);
	op2 = EXTRACT(ESR_EL2_SYSREG_TRAP_OP2, sysreg);

	INFO("Unhandled %s S%u_%u_C%u_C%u_%u\n",
		ESR_EL2_SYSREG_IS_WRITE(esr) ? "write" : "read",
		op0, op1, crn, crm, op2);

	return true;
}
