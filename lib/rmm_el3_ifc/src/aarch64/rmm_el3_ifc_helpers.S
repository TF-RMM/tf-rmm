/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <asm_macros.S>
#include <rmm_el3_ifc.h>

	.globl rmm_el3_ifc_validate_cpuid

/*
 * This function performs an early validation of the CPU Id received
 * during warm boot and stores it into tpidr_el2.
 *
 * If the validation fails it will call into EL3 and will not return
 * to the caller.
 *
 * It returns the CPU Id.
 *
 * Clobber list: x0, x1
 */
func rmm_el3_ifc_validate_cpuid
	/*
	 * Check that the current CPU Id does not exceed the maximum allowed.
	 */
	mov_imm	x1, MAX_CPUS
	cmp	x0, x1
	b.hs	1f
	/* Setup this CPU Id */
	msr	tpidr_el2, x0
	ret

1:
	/* CPU Id out of range */
	mov_imm	x0, SMC_RMM_BOOT_COMPLETE
	mov_imm	x1, E_RMM_BOOT_CPU_ID_OUT_OF_RANGE
	smc	#0
	/* EL3 Firmware should never return here, so panic if it does */
	asm_panic

endfunc rmm_el3_ifc_validate_cpuid
