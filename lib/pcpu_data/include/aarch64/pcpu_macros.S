/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */
#ifndef PCPU_MACROS_S
#define PCPU_MACROS_S

#include <asm_macros.S>
#include <pcpu_data.h>

/*
 * Reserve the current CPU's per-CPU region and initialize the early stack.
 *
 * The per-CPU region contains, in order, the metadata page
 * (`struct pcpu_metadata`), the private per-CPU data pages, the regular RMM
 * stack, and the exception-handler stack.
 * Since the metadata page is the first granule, the region base PA returned
 * by pcpu_region_alloc() is also the metadata-page PA consumed by
 * pcpu_metadata_early_init().
 *
 * The call sites may keep the activation token in different registers,
 * depending on which boot arguments still need to be preserved on that path.
 * This macro normalizes those values into the AAPCS call registers before
 * calling the helpers.
 *
 * Before MMU enable, TPIDR_EL2 and SP use physical addresses. After
 * pcpu_switch_to_high_va(), they are rewritten to the fixed per-CPU high VAs.
 *
 * Arguments:
 *   _token_reg - A register that holds the EL3 activation token.
 *   _cpu_id_reg - A register that holds the CPU Id (<= 4095)
 *
 * Returns:
 *   x0 - Base physical address of the current CPU's per-CPU region
 *
 * Clobbers: x0, x1, x2, x3, x4, lr
 */
.macro pcpu_region_alloc_sp_init _token_reg, _cpu_id_reg

	mov	x0, \_token_reg /* Pass activation token to pcpu_region_alloc */
	bl	pcpu_region_alloc

	/*
	 * If _token_reg was 0, then we have just allocated memory for this CPU.
	 * So, X0 now contains the base physical address of that per-CPU region.
	 *
	 * Otherwise, if _token_reg was not zero, then `pcpu_region_alloc` had no
	 * effect and X0 still has the activation token, which is that same base PA.
	 *
	 * Either way, X0 is the base PA of the per-CPU region, which is also the
	 * PA of `struct pcpu_metadata`, because metadata is stored in the first
	 * granule of the region.
	 */


	mov	x4, x0

	/*
	 * Before the stack is reused as a physical-address stack, discard stale
	 * cache lines for the regular and exception-handler stack pages only.
	 *
	 * The metadata page is intentionally excluded from this range, because it's
	 * handled by the metadata writer function.
	 */
	mov_imm	x0, PCPU_STACK_BASE_PA_OFFSET
	add	x0, x4, x0
	mov_imm	x1, ((RMM_NUM_PAGES_PER_STACK + EH_STACK_PAGES) * GRANULE_SIZE)
	bl	inv_dcache_range

	mov	x0, x4

	/*
	 * Calculate the top of the regular RMM stack and set SP to that value.
	 *
	 * We have allocated PCPU_REGION_PAGES already, so the stack pointer will
	 * point to the top of the RMM stack (equal to the bottom of the EH stack region).
	 * From there it will "grow" downwards.
	 *
	 * For now, SP is a physical address. Later, pcpu_switch_to_high_va() rewrites
	 * it to the fixed high VA for this CPU after MMU activation.
	 */
	mov_imm	x1, PCPU_STACK_TOP_PA_OFFSET
	add	sp, x0, x1
	/* Stack is set up. C functions can be called now. */

	/* x0 has the metadata-page PA; move CPU ID to x1 and token to x2. */
	mov	x1, \_cpu_id_reg
	mov	x2, \_token_reg
	bl	pcpu_metadata_early_init
.endm

#endif /* PCPU_MACROS_S */
