/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <asm_macros.S>
#include <pcpu_data.h>

.globl pcpu_region_alloc
.globl pcpu_switch_to_high_va

/*
 * Reserves the current CPU's per-CPU region and returns its base physical
 * address.
 *
 * The first granule of that region holds `struct pcpu_metadata`. The remaining
 * granules hold the private per-CPU data, the regular RMM stack, and the
 * exception-handler stack.
 *
 * Arguments:
 *   x0 - EL3 activation token. Zero means first entry on this CPU. Non-zero
 *        means reuse the already allocated per-CPU region whose base PA is
 *        carried in the token.
 *
 * Returns:
 *   x0 - Base physical address of the current CPU's per-CPU region
 *
 * Clobbers: x0, x1, x2, x3, x4
 */
func pcpu_region_alloc
	/*
	 * If EL3 activation token is not zero, it means that the current CPU
	 * has already entered RMM before and is entering again, possibly through LFA.
	 * In this case, the per-CPU region has already been allocated and initialized by
	 * the previous boot of the CPU and there's no need to allocate again.
	 */
	cbz	x0, 1f
	ret
1:
	/* Load PCPU_REGION_PAGES into x0 */
	mov_imm	x0, PCPU_REGION_PAGES

	/* Tail call to the CPU-local early-boot EL3 memory reservation helper. */
	b	rmm_el3_ifc_early_reserve_mem_local
endfunc pcpu_region_alloc

/*
 * Replace the physical-address view in TPIDR_EL2, SP, and SP_EL0 with the
 * fixed high-VA view for the current CPU.
 *
 * The low GRANULE_SHIFT bits of TPIDR_EL2 keep carrying the CPU ID.
 *
 * Clobbers: x0, x1, x2
 */
func pcpu_switch_to_high_va
	/* Preserve the CPU ID from the low GRANULE_SHIFT bits of TPIDR_EL2. */
	mrs	x0, tpidr_el2
	and	x0, x0, #(GRANULE_SIZE - 1)

	/* Load the fixed high VA of the current CPU's metadata page. */
	mov_imm	x1, PCPU_METADATA_BASE_VA

	/* Rebuild TPIDR_EL2 as [PCPU_METADATA_BASE_VA | CPU ID]. */
	orr	x0, x0, x1
	msr	tpidr_el2, x0

	/* Switch the regular RMM stack pointer from PA to high VA. */
	mov_imm	x2, STACK_TOP_VA
	mov	sp, x2

	/* Switch the exception-handler stack pointer from PA to high VA. */
	mov_imm	x2, EH_STACK_TOP_VA
	msr	sp_el0, x2
	ret
endfunc pcpu_switch_to_high_va
