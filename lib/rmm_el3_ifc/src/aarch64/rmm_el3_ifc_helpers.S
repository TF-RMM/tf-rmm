/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <asm_macros.S>
#include <rmm_el3_ifc.h>

	.globl rmm_el3_ifc_validate_cpuid
	.globl rmm_el3_ifc_early_reserve_mem_local

/*
 * This function performs an early validation of the CPU Id received
 * during warm boot.
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
	ret

1:
	/* CPU Id out of range */
	mov_imm	x0, SMC_RMM_BOOT_COMPLETE
	mov_imm	x1, E_RMM_BOOT_CPU_ID_OUT_OF_RANGE
	smc	#0
	/* EL3 Firmware should never return here, so panic if it does */
	asm_panic

endfunc rmm_el3_ifc_validate_cpuid

/*
 * Early-boot assembly helper for CPU-local memory reservation with hardcoded values:
 * - alignment: 12 (4KB granule)
 * - flags bit[0]: 1 (RESERVE_MEM_FLAG_LOCAL_CPU)
 *
 * This minimal helper is used only on the early boot path, before the normal
 * C runtime is available. Later allocations use rmm_el3_ifc_reserve_memory().
 *
 * This function reserves CPU-local memory from EL3 via SMC call.
 *
 * Arguments:
 *   x0 - Number of pages to reserve
 *
 * Returns:
 *   x0 - Physical address (PA) of the reserved memory on success
 *        Returns back to EL3 with Error code on failure.
 *
 * Clobber list: x0, x1, x2, x3, x4 (due to SMC call)
 */
func rmm_el3_ifc_early_reserve_mem_local
	/* Calculate size in bytes: size = num_pages << GRANULE_SHIFT */
	lsl	x1, x0, #GRANULE_SHIFT

	/*
	 * Prepare x2 with flags and alignment:
	 * - bit [0]: local cpu flag = 1 (RESERVE_MEM_FLAG_LOCAL_CPU)
	 * - bits [31:1]: flags = 0
	 * - bits [55:32]: reserved = 0
	 * - bits [63:56]: alignment = GRANULE_SHIFT
	 * x2 = (GRANULE_SHIFT << RESERVE_MEM_ALIGN_SHIFT) | RESERVE_MEM_FLAG_LOCAL_CPU
	 */
	mov_imm	x2, ((GRANULE_SHIFT << RESERVE_MEM_ALIGN_SHIFT) | RESERVE_MEM_FLAG_LOCAL_CPU)

	/*
	 * Prepare SMC function ID:
	 * SMC_RMM_RESERVE_MEMORY = 0xC40001BB
	 */
	mov_imm	x0, SMC_RMM_RESERVE_MEMORY

	/* Execute SMC call */
	smc	#0

	/*
	 * Check if SMC call was successful.
	 * x0 contains the return code:
	 *   0 = success
	 *   negative = error code
	 * x1 contains the physical address on success
	 */
	cmp	x0, #0
	b.ne	1f

	/* Success: return the PA from x1 */
	mov	x0, x1
	ret

1:
	/* No memory */
	mov_imm	x0, SMC_RMM_BOOT_COMPLETE
	mov_imm	x1, E_RMM_BOOT_NO_MEM
	smc	#0
	/* EL3 Firmware should never return here, so panic if it does */
	asm_panic

endfunc rmm_el3_ifc_early_reserve_mem_local
