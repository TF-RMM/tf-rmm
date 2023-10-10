/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors
 */

#include <arch.h>
#include <arch_helpers.h>
#include <cpuid.h>
#include <entropy.h>
#include <pauth.h>
#include <pauth_pvt.h>

/* APIAKey Array */
static __uint128_t g_rmm_pauth_apia[MAX_CPUS];

/*
 * Program APIAKey_EL1 with random key generated from
 * a TRNG entropy source
 */
/* coverity[misra_c_2012_rule_8_7_violation:SUPPRESS] */
PAUTH_NONE_ATTR void pauth_init_enable_el2(void)
{
	uint64_t low;
	uint64_t high;
	unsigned int cpu_id = my_cpuid();

	while (!arch_collect_entropy(&low)) {
	}

	while (!arch_collect_entropy(&high)) {
	}

	g_rmm_pauth_apia[cpu_id] = (((__uint128_t)high << 64) | low);

	/*
	 * Allow access to PAuth instructions and registers
	 * holding "key" values in EL0/1 without trapping to EL2
	 */
	write_hcr_el2(read_hcr_el2() | HCR_API | HCR_APK);
	pauth_restore_rmm_keys();

	/*
	 * Enable pointer authentication in EL2
	 */
	write_sctlr_el2(read_sctlr_el2() | SCTLR_ELx_EnIA_BIT);
	isb();
}

PAUTH_NONE_ATTR void pauth_restore_rmm_keys(void)
{
	unsigned int cpu_id = my_cpuid();

	write_apiakeylo_el1((uint64_t)g_rmm_pauth_apia[cpu_id]);
	write_apiakeyhi_el1((uint64_t)(g_rmm_pauth_apia[cpu_id] >> 64));
	isb();
}

PAUTH_NONE_ATTR void pauth_restore_realm_keys(struct pauth_state *pauth)
{
	write_apiakeylo_el1(pauth->apiakeylo_el1);
	write_apiakeyhi_el1(pauth->apiakeyhi_el1);
	write_apibkeylo_el1(pauth->apibkeylo_el1);
	write_apibkeyhi_el1(pauth->apibkeyhi_el1);
	write_apdakeylo_el1(pauth->apdakeylo_el1);
	write_apdakeyhi_el1(pauth->apdakeyhi_el1);
	write_apdbkeylo_el1(pauth->apdbkeylo_el1);
	write_apdbkeyhi_el1(pauth->apdbkeyhi_el1);
	write_apgakeylo_el1(pauth->apgakeylo_el1);
	write_apgakeyhi_el1(pauth->apgakeyhi_el1);
	isb();
}

PAUTH_NONE_ATTR void pauth_save_realm_keys(struct pauth_state *pauth)
{
	pauth->apiakeylo_el1 = read_apiakeylo_el1();
	pauth->apiakeyhi_el1 = read_apiakeyhi_el1();
	pauth->apibkeylo_el1 = read_apibkeylo_el1();
	pauth->apibkeyhi_el1 = read_apibkeyhi_el1();
	pauth->apdakeylo_el1 = read_apdakeylo_el1();
	pauth->apdakeyhi_el1 = read_apdakeyhi_el1();
	pauth->apdbkeylo_el1 = read_apdbkeylo_el1();
	pauth->apdbkeyhi_el1 = read_apdbkeyhi_el1();
	pauth->apgakeylo_el1 = read_apgakeylo_el1();
	pauth->apgakeyhi_el1 = read_apgakeyhi_el1();
}
