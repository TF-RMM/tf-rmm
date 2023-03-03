/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch_helpers.h>
#include <debug.h>
#include <host_utils.h>
#include <platform_api.h>
#include <rmm_el3_ifc.h>

#define RMM_EL3_IFC_ABI_VERSION		(RMM_EL3_IFC_SUPPORTED_VERSION)
#define RMM_EL3_MAX_CPUS		(1U)

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

	host_util_set_cpuid(0U);

	host_util_setup_sysreg_and_boot_manifest();

	plat_setup(0UL,
		   RMM_EL3_IFC_ABI_VERSION,
		   RMM_EL3_MAX_CPUS,
		   (uintptr_t)host_util_get_el3_rmm_shared_buffer());

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
