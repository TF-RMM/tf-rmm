/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <app_header.h>
#include <arch.h>
#include <asm_macros.S>
#include <pcpu_macros.S>
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
	mov	x24, x4
	mov	x25, lr

	/* Disable DIT */
	msr	DIT, xzr

	mov_imm	x1, SCTLR_EL2_INIT
	msr	sctlr_el2, x1

	mov_imm	x2, HCR_EL2_REALM
	msr	hcr_el2, x2

	mov_imm	x3, CPTR_EL2_VHE_INIT
	msr	cptr_el2, x3

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

	/* Setup exception vectors */
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
	 * Warm entry for this CPU:
	 * - obtain this CPU's per-CPU region base:
	 *   - if the activation token is non-zero, reuse the existing region base PA
	 *   - if the activation token is zero, allocate the region now for this CPU's
	 *     first RMM entry
	 * - the resulting region base PA is also the metadata-page PA, because the
	 *   metadata page is the first granule of the per-CPU region
	 * - build (or rebuild) TPIDR_EL2 as [metadata-page PA | CPU ID]
	 * - set SP to the top of the RMM stack (backed by physical pages)
	 *
	 * On this path the token is currently held in x21.
	 */
	pcpu_region_alloc_sp_init	x21, x20

	/* Initialize architecture regs */
	bl	rmm_arch_init

	/*
	 * Restore arguments in preparation for the warm boot path
	 */
	mov	x0, x20
	mov	x1, x21
	mov	x2, x22
	mov	x3, x23
	mov	x4, x24
	b	\_warm_boot

/* Only use this path if we have a cold boot. */
2:
	/*
	 * First RMM entry on the boot CPU:
	 * - reserve a new per-CPU region from EL3
	 * - initialize its metadata page, which acts as the header for that region
	 * - build TPIDR_EL2 as [metadata-page PA | CPU ID]
	 * - set SP to the top of the RMM stack (backed by physical pages)
	 *
	 * On this path the token is currently held in x24.
	 */
	pcpu_region_alloc_sp_init	x24, x20

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
	mov	x0, x25 /* x25 is the start of RMM image */
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
	 * Save RMM image addresses.
	 */
	adrp	x1, rmm_entry /* rmm_entry is page alined */
#ifndef APP_COUNT
#error APP_COUNT is not defined
#endif
#if APP_COUNT == 0
	mov	x0, x1
#else
	sub	x0, x25, #4
#endif
	bl 	app_save_rmm_entry_info

	/*
	 * This function has to be called before plat_setup
	 * and rmm_arch_init, since arch features are queried
	 * by them.
	 */
	bl	arch_features_query_el3_support

	/* Initialize architecture regs */
	bl	rmm_arch_init

	/*
	 * Restore args received from previous BL image
	 */
	mov	x0, x20
	mov	x1, x21
	mov	x2, x22
	mov	x3, x23
	mov	x4, x24
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
	/* Initialize MEC before MMU is enabled */
	bl	mec_init_mmu
	bl	xlat_enable_mmu_el2
	/*
	 * Replace the PA-backed early view with the fixed high-VA view:
	 * - TPIDR_EL2 changes from [metadata PA | CPU ID] to [metadata VA | CPU ID]
	 * - SP and SP_EL0 change from PA stacks to the fixed high-VA stacks
	 */
	bl	pcpu_switch_to_high_va
	/* C runtime is available again */
	bl	pauth_init_enable_el2

#ifdef STACK_PROTECTOR_ENABLED
	/*
	 * The canary init function uses spin_lock and hence it is
	 * called after MMU is enabled.
	 */
	bl	rmm_init_stack_canary
#endif /* STACK_PROTECTOR_ENABLED */

	/*
	 * After rmm_main, we'll have the activation token
	 * returned in X0 and ready to be used in smc_ret.
	 */
	bl	rmm_main
	b	smc_ret

/* Only run this for warm boot. */
skip_to_warmboot:
	/*
	 * Per-CPU warmboot setup for this CPU while still running on the PA-backed
	 * early stack. This prepares the fixed high-VA mappings for the current CPU.
	 */
	bl	plat_warmboot_setup
	/* Initialize MEC before MMU is enabled */
	bl	mec_init_mmu
	bl	xlat_enable_mmu_el2
	/*
	 * Replace the PA-backed early view with the fixed high-VA view:
	 * - TPIDR_EL2 changes from [metadata PA | CPU ID] to [metadata VA | CPU ID]
	 * - SP and SP_EL0 change from PA stacks to the fixed high-VA stacks
	 */
	bl	pcpu_switch_to_high_va
	/* C runtime is available again */
	bl	pauth_init_enable_el2

	/*
	 * After rmm_warmboot_main, we'll have the activation token
	 * returned in X0 and ready to be used in smc_ret.
	 */
	bl	rmm_warmboot_main

/* Execute at the end of both the cold and warm boot. */
smc_ret:
	/*
	 * Notify EL3 that RMM boot is complete.
	 * x0: SMC_RMM_BOOT_COMPLETE
	 * x1: E_RMM_BOOT_SUCCESS
	 * x2: activation_token
	 */
	mov	x2, x0
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
