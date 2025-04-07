/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <app.h>
#include <app_header.h>
#include <arch_features.h>
#include <attest_app.h>
#include <buffer.h>
#include <debug.h>
#include <random_app.h>
#include <rmm_el3_ifc.h>
#include <run.h>
#include <simd.h>
#include <smc-rmi.h>
#include <smc-rsi.h>

#ifdef NDEBUG
#define RMM_BUILD_TYPE	"release"
#else
#define RMM_BUILD_TYPE	"debug"
#endif

#define VER_STRING(toolchain, major, minor, patch) \
		toolchain __STRING(major) "." \
		__STRING(minor) "." __STRING(patch)

static void rmm_arch_init(void)
{
	unsigned long hcrx_el2_init = HCRX_INIT;

	/* All access to MPAM registers from EL1/0 must be trapped by RMM */
	if (is_feat_mpam_present()) {
		unsigned long mpamidr_el1 = read_mpamidr_el1();

		if ((mpamidr_el1 & MPAMIDR_EL1_HAS_HCR_BIT) != 0UL) {
			write_mpamhcr_el2(MPAMHCR_EL2_INIT);
		}

		write_mpam2_el2(MPAM2_EL2_INIT);
	}

	SPE(write_pmscr_el2(PMSCR_EL2_INIT));

	write_cnthctl_el2(CNTHCTL_EL2_INIT);
	write_vpidr_el2(read_midr_el1());
	write_mdcr_el2(MDCR_EL2_INIT |
			INPLACE(MDCR_EL2_HPMN,
			EXTRACT(PMCR_EL0_N, read_pmcr_el0())));

	/* Enable EL1 access to sctlr2_el1 if the register is present */
	if (is_feat_sctlr2x_present()) {
		hcrx_el2_init |= HCRX_SCTLR2EN;
	}

	write_hcrx_el2(hcrx_el2_init);

	/* Disable BRBE at R-EL2 and prevent access to BRBE regs from R-EL1 */
	if (is_feat_brbe_present()) {
		write_brbcr_el2(BRBCR_INIT);
		write_hdfgrtr_el2((read_hdfgrtr_el2()) & (~HDFGRTR_EL2_INIT_CLEAR_MASK));
	}


}

/* coverity[misra_c_2012_rule_8_4_violation:SUPPRESS] */
/* coverity[misra_c_2012_rule_8_7_violation:SUPPRESS] */
void rmm_warmboot_main(void)
{
	/*
	 * Do the rest of RMM architecture init
	 */
	rmm_arch_init();

	/*
	 * Finish initializing the slot buffer mechanism
	 */
	slot_buf_finish_warmboot_init();

	/*
	 * Random app init
	 */
#ifdef RMM_FPU_USE_AT_REL2
	simd_context_save(get_cpu_ns_simd_context());
#endif
	random_app_init_prng();
#ifdef RMM_FPU_USE_AT_REL2
	simd_context_restore(get_cpu_ns_simd_context());
#endif
	/*
	 * Attest app init
	 */
	attest_app_init_per_cpu_instance();
}

/*
 * This function is called from rmm_entry() in head.S
 * and should be defined with external linkage, no
 * compatible declaration is required.
 */
/* coverity[misra_c_2012_rule_8_4_violation:SUPPRESS] */
/* coverity[misra_c_2012_rule_8_7_violation:SUPPRESS] */
void rmm_main(void)
{
	unsigned int rmm_el3_ifc_version = rmm_el3_ifc_get_version();
	unsigned int manifest_version = rmm_el3_ifc_get_manifest_version();
	unsigned long rmi_revision = rmi_get_highest_supported_version();
	unsigned long rsi_revision = rsi_get_highest_supported_version();

	/*
	 * Report project name, version, build type and
	 * commit information if it is present
	 */
	NOTICE("Booting %s v.%s(%s) %s Built: %s %s with %s\n",
	       NAME, VERSION, RMM_BUILD_TYPE, COMMIT_INFO, __DATE__, __TIME__,
#ifdef __clang__
	VER_STRING("Clang ", __clang_major__, __clang_minor__,
		__clang_patchlevel__)
#else
	VER_STRING("GCC ", __GNUC__, __GNUC_MINOR__,
		__GNUC_PATCHLEVEL__)
#endif
		);

	/* Report Boot Interface version */
	NOTICE("RMM-EL3 Interface v.%u.%u\n",
		RMM_EL3_IFC_GET_VERS_MAJOR(rmm_el3_ifc_version),
		RMM_EL3_IFC_GET_VERS_MINOR(rmm_el3_ifc_version));

	/* Report Boot Manifest version */
	NOTICE("Boot Manifest Interface v.%u.%u\n",
		RMM_EL3_MANIFEST_GET_VERS_MAJOR(manifest_version),
		RMM_EL3_MANIFEST_GET_VERS_MINOR(manifest_version));

	/* Report higher supported RMI revision */
	NOTICE("RMI ABI revision v%lu.%lu\n",
	       RMI_ABI_VERSION_GET_MAJOR(rmi_revision),
	       RMI_ABI_VERSION_GET_MINOR(rmi_revision));

	/* Report higher supported RSI revision */
	NOTICE("RSI ABI revision v%lu.%lu\n",
	       RSI_ABI_VERSION_GET_MAJOR(rsi_revision),
	       RSI_ABI_VERSION_GET_MINOR(rsi_revision));

	app_info_setup();
	app_framework_setup();

	simd_init();

	/* Initialize the NS SIMD context for all CPUs */
	init_all_cpus_ns_simd_context();

#ifdef RMM_FPU_USE_AT_REL2
	simd_context_save(get_cpu_ns_simd_context());
#endif

	/*
	 * Initialise the prng for this CPU, as it may be used by the attest
	 * global init during key calculation. This fuinction is also called in
	 * rmm_warmboot_main, but it is not a problem as initialisation happens
	 * only once, regardless of the number of calls to this function.
	 */
	random_app_init_prng();

	/*
	 * TODO: this function shouldn't panic!!
	 * It should be possible to startup RMM without working attestation
	 * Probably could still panic if there is an error during app management
	 */
	if (attest_app_global_init() != 0) {
		WARN("Attestation init failed.\n");
	}

#ifdef RMM_FPU_USE_AT_REL2
	/*
	 * TODO: Do not save and restore NS state. Instead after
	 * attestation init clear FPU state.
	 */
	simd_context_restore(get_cpu_ns_simd_context());
#endif

	rmm_warmboot_main();
}
