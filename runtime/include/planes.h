/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef PLANES_H
#define PLANES_H

#include <smc-rmi.h>
#include <utils_def.h>

/* Plane 0 on a realm has always index '0' */
#define PLANE_0_ID			(0U)

/*
 * Index of the primary S2_CTX.
 *
 * Note that the mapping between plane ID and context ID is 1:1.
 */
#define PRIMARY_S2_CTX_ID		(PLANE_0_ID)

/* Maximum number of Stage 2 Translation contexts needed per realm */
#define MAX_S2_CTXS			(MAX_TOTAL_PLANES)

/* Macros to access cookie used on RSI_MEM_SET_PERM_INDEX */
#define GET_RTT_BASE_FROM_COOKIE(_cookie)	((_cookie) & GRANULE_MASK)
#define GET_RTT_IDX_FROM_COOKIE(_cookie)	((_cookie) & ~GRANULE_MASK)
#define RTT_COOKIE_CREATE(_addr, _idx)		(((_addr) & GRANULE_MASK) | \
						 ((_idx) & ~GRANULE_MASK))

/* Arquitectural registers used per plane */
STRUCT_TYPE plane_el01_regs {
	unsigned long actlr_el1;
	unsigned long afsr0_el1;
	unsigned long afsr1_el1;
	unsigned long amair_el1;
	unsigned long brbcr_el1;
	unsigned long cntkctl_el1;
	unsigned long contextidr_el1;
	unsigned long cpacr_el1;
	unsigned long csselr_el1;
	unsigned long disr_el1;
	unsigned long elr_el1;
	unsigned long esr_el1;
	unsigned long far_el1;
	unsigned long mair_el1;
	unsigned long mdccint_el1;
	unsigned long mdscr_el1;
	unsigned long par_el1;
	unsigned long pir_el1;
	unsigned long pire0_el1;
	unsigned long por_el1;
	unsigned long sctlr_el1;
	unsigned long sctlr2_el1;
	unsigned long sp_el1;
	unsigned long spsr_el1;
	unsigned long tcr_el1;
	unsigned long tcr2_el1;
	unsigned long tpidr_el1;
	unsigned long ttbr0_el1;
	unsigned long ttbr1_el1;
	unsigned long vbar_el1;
	unsigned long zcr_el1;

	unsigned long cntp_ctl_el0;
	unsigned long cntp_cval_el0;
	unsigned long cntv_ctl_el0;
	unsigned long cntv_cval_el0;
	unsigned long sp_el0;
	unsigned long tpidrro_el0;
	unsigned long tpidr_el0;
};

#endif /* PLANES_H */
