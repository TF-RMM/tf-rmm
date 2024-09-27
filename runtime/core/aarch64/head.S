/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch.h>
#include <asm_macros.S>
#include <rmm_el3_ifc.h>

.globl rmm_entry

/*
 * Initialize essential R-EL2 sysregs and C runtime environment
 */
.macro rmm_el2_init_env _vector, _is_cold_boot_flag, _warm_boot

	/*
	 * Stash arguments from previous boot stage
	 */
	mov	x20, x0
	mov	x21, x1
	mov	x22, x2
	mov	x23, x3

	/* Disable DIT */
	msr	DIT, xzr

	mov_imm	x1, SCTLR_EL2_INIT
	msr	sctlr_el2, x1

	mov_imm	x2, HCR_EL2_INIT
	msr	hcr_el2, x2

	mov_imm	x3, CPTR_EL2_VHE_INIT
	msr	cptr_el2, x3

	mov_imm	x4, ICC_SRE_EL2_INIT
	msr	ICC_SRE_EL2, x4

	isb

	ldr	x1, \_is_cold_boot_flag
	cbz	x1, 1f

	/*
	 * As PIE is enabled, fixup the Global Descriptor Table only
	 * once during cold boot. This is needed before accessing any
	 * symbol addresses.
	 */
	bl	fixup_gdt_reloc

	/* Cold and warm boot need to go through this path */
1:
	/* Early validate and init CPU Id */
	mov	x0, x20
	bl	rmm_el3_ifc_validate_cpuid

	/*
	 * Setup stack on this CPU. X0 already contains the CPU Id. The stack
	 * address set here is the physical address of the stack buffer. During
	 * RMM boot the stack for this CPU is going to be mapped in the high VA
	 * space of this CPU, and the SP is updated to the VA of the stack
	 * bottom after MMU activation. After that, accessing the physical stack
	 * address causes exception as the stack buffer is not flat-mapped in
	 * the VA space of the CPU.
	 */
	bl	rmm_get_my_stack
	mov	sp, x0

	/*
	 * Setup exception vectors
	 */
	adrp	x3, \_vector
	add	x3, x3, :lo12:\_vector
	msr	vbar_el2, x3
	isb

	/*
	 * Find out whether this is a cold or warm boot
	 */
	ldr	x1, \_is_cold_boot_flag
	cbnz	x1, 2f

	/*
	 * Restore arguments in preparation for the warm boot path
	 */
	mov	x0, x20
	mov	x1, x21
	mov	x2, x22
	mov	x3, x23
	b	\_warm_boot

2:
	/*
	 * RMM starts with MMU disabled (and hence with data cacheability disabled).
	 * EL3 loads RMM with caches enabled, so while it can ensure cache lines are
	 * clean, it cannot ensure that cache lines for RMM memory locations are not
	 * allocated in cache.
	 * During init, RMM writes to BSS and various parts of RMM as part of PIE
	 * fixup with data cacheability disabled, hence cache lines containing stale
	 * data must be invalidated, so that upon turning on MMU (and hence enabling
	 * cacheability), we read updated values.
	 */
	adrp	x0, rmm_base
	adrp	x2, rmm_end
	sub	x1, x2, x0
	bl	inv_dcache_range

	/*
	 * Update cold boot flag to indicate cold boot is done
	 */
	adr	x2, \_is_cold_boot_flag
	str	xzr, [x2]

	/*
	 * Initialize BSS section
	 */
	adrp	x0, bss_start
	add	x0, x0, :lo12:bss_start
	adrp	x1, bss_end
	add	x1, x1, :lo12:bss_end
	sub	x2, x1, x0
	mov	x1, xzr
	bl	memset

	/*
	 * Restore args received from previous BL image
	 */
	mov	x0, x20
	mov	x1, x21
	mov	x2, x22
	mov	x3, x23
.endm

/*
 * This is the main entry for both Primary and secondary PEs.
 */
func rmm_entry
	rmm_el2_init_env el2_vectors, cold_boot_flag, skip_to_warmboot

	/*
	 * Initialize platform specific peripherals like UART and
	 * xlat tables.
	 */
	bl	plat_setup
	bl	xlat_enable_mmu_el2
	bl	pauth_init_enable_el2

	bl	rmm_main
	b	smc_ret

skip_to_warmboot:
	/*
	 * Carry on with the rest of the RMM warmboot path
	 */
	bl	plat_warmboot_setup
	bl	xlat_enable_mmu_el2
	bl	pauth_init_enable_el2

	bl	rmm_warmboot_main
smc_ret:
	mov_imm	x0, SMC_RMM_BOOT_COMPLETE
	mov_imm	x1, E_RMM_BOOT_SUCCESS
	smc	#0

	/* Jump to the SMC handler post-init */
	b	rmm_handler

	/*
	 * Flag to mark if it is a cold boot.
	 * 1: cold boot, 0: warmboot.
	 */
.align 3
cold_boot_flag:
	.dword		1
endfunc rmm_entry
