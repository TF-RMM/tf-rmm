/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch.h>
#include <arch_helpers.h>
#include <debug.h>
#include <gic.h>
#include <host_utils.h>
#include <platform_api.h>
#include <rmm_el3_ifc.h>
#include <stdint.h>
#include <xlat_tables.h>

#define RMM_EL3_IFC_ABI_VERSION		(RMM_EL3_IFC_SUPPORTED_VERSION)
#define RMM_EL3_MAX_CPUS		(1U)

/*
 * Define and set the Boot Interface arguments.
 */
static unsigned char el3_rmm_shared_buffer[PAGE_SIZE] __aligned(PAGE_SIZE);

/*
 * Create a basic boot manifest.
 */
static struct rmm_core_manifest *boot_manifest =
			(struct rmm_core_manifest *)el3_rmm_shared_buffer;

/*
 * Performs some initialization needed before RMM can be ran, such as
 * setting up callbacks for sysreg access.
 */
static void setup_sysreg_and_boot_manifest(void)
{
	/*
	 * By default, set current CPU to be CPU0.
	 * Fake host doesn't support using more than one CPU.
	 */
	host_util_set_cpuid(0U);

	/*
	 * Initialize ID_AA64MMFR0_EL1 with a physical address
	 * range of 48 bits (PARange bits set to 0b0101)
	 */
	(void)host_util_set_default_sysreg_cb("id_aa64mmfr0_el1",
				INPLACE(ID_AA64MMFR0_EL1_PARANGE, 5UL));

	/*
	 * Initialize ICH_VTR_EL2 with 6 preemption bits.
	 * (PREbits is equal number of preemption bits minus one)
	 */
	(void)host_util_set_default_sysreg_cb("ich_vtr_el2",
				INPLACE(ICH_VTR_EL2_PRE_BITS, 5UL));

	/* SCTLR_EL2 is reset to zero */
	(void)host_util_set_default_sysreg_cb("sctlr_el2", 0UL);

	/* TPIDR_EL2 is reset to zero */
	(void)host_util_set_default_sysreg_cb("tpidr_el2", 0UL);

	/* Initialize the boot manifest */
	boot_manifest->version = RMM_EL3_IFC_SUPPORTED_VERSION;
	boot_manifest->plat_data = (uintptr_t)NULL;

	/* Store current CPU ID into tpidr_el2 */
	write_tpidr_el2(0);
}

/*
 * Function to emulate the MMU enablement for the fake_host architecture.
 */
static void enable_fake_host_mmu(void)
{
	write_sctlr_el2(SCTLR_EL2_WXN | SCTLR_EL2_M);
}

void rmm_main(void);

int main(int argc, char *argv[])
{
	(void)argc;
	(void)argv;

	VERBOSE("RMM: Beginning of Fake Host execution\n");

	setup_sysreg_and_boot_manifest();

	plat_setup(0UL,
		   RMM_EL3_IFC_ABI_VERSION,
		   RMM_EL3_MAX_CPUS,
		   (uintptr_t)&el3_rmm_shared_buffer);

	/*
	 * Enable the MMU. This is needed as some initialization code
	 * called by rmm_main() asserts that the mmu is enabled.
	 */
	enable_fake_host_mmu();

	/* Start RMM */
	rmm_main();

	VERBOSE("RMM: Fake Host execution completed\n");

	return 0;
}
