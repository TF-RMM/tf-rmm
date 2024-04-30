/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch_helpers.h>
#include <buffer.h>
#include <debug.h>
#include <errno.h>
#include <granule.h>
#include <host_defs.h>
#include <host_utils.h>
#include <limits.h>
#include <platform_api.h>
#include <rmm_el3_ifc.h>
#include <stdlib.h>
#include <string.h>
#include <test_private.h>
#include <time.h>
#include <utest_exit.h>
#include <xlat_tables.h>

/*
 * Define and set the Boot Interface arguments.
 */
#define RMM_EL3_IFC_ABI_VERSION		\
	RMM_EL3_IFC_MAKE_VERSION(RMM_EL3_IFC_VERS_MAJOR, RMM_EL3_IFC_VERS_MINOR)
#define RMM_EL3_MAX_CPUS		(MAX_CPUS)

/* Maximum size of the assertion check string */
#define CHECK_SIZE			U(80)

/* Assertion control variables */
static char assert_check[CHECK_SIZE + 1U];
static bool assert_expected;
static bool asserted;

static uintptr_t callbacks[CB_IDS];

static void start_primary_pe(void)
{
	host_util_set_cpuid(0U);

	/* Early setup the CpuId into tpidr_el2 */
	write_tpidr_el2(0U);

	plat_setup(0UL,
		   RMM_EL3_IFC_ABI_VERSION,
		   RMM_EL3_MAX_CPUS,
		   (uintptr_t)host_util_get_el3_rmm_shared_buffer());

	/*
	 * Enable the MMU. This is needed as some initialization code
	 * called by rmm_main() asserts that the mmu is enabled.
	 */
	xlat_enable_mmu_el2();

	/*
	 * rmm_main() finishhes the warmboot path.
	 *
	 * Note: It is expected that the attestation init will fail.
	 */
	rmm_main();
}

static void start_secondary_pe(unsigned int cpuid)
{
	host_util_set_cpuid(cpuid);

	/*
	 * Early setup the CpuId into tpidr_el2 for each secondary.
	 */
	write_tpidr_el2(cpuid);

	plat_warmboot_setup(0UL,
			    RMM_EL3_IFC_ABI_VERSION,
			    RMM_EL3_MAX_CPUS,
			    (uintptr_t)host_util_get_el3_rmm_shared_buffer());

	/*
	 * Enable the MMU. This is needed to avoid assertions during boot up
	 * that would otherwise occur if the MMU is disabled.
	 */
	xlat_enable_mmu_el2();

	/*
	 * Finalize the warmboot path.
	 * This enables the slot buffer mechanism.
	 */
	rmm_warmboot_main();
}

void test_helpers_rmm_start(bool secondaries)
{
	static bool initialized;

	if (initialized == false) {
		/* Enable RMM and setup basic structures for each test. */
		host_util_setup_sysreg_and_boot_manifest();

		/* bringup primary CPU */
		start_primary_pe();

		if (secondaries) {
			for (unsigned int i = 1U; i < RMM_EL3_MAX_CPUS; i++) {
				start_secondary_pe(i);
			}
			host_util_set_cpuid(0U);

			/* Take a snapshot of the current sysreg status */
			host_util_take_sysreg_snapshot();
		}
		initialized = true;
	} else {
		/* Restore the sysreg status */
		host_util_restore_sysreg_snapshot();
	}
}

unsigned int test_helpers_get_nr_granules(void)
{
	return HOST_NR_GRANULES;
}

unsigned long test_helpers_get_rand_in_range(unsigned long min,
					     unsigned long max)
{
	unsigned long retval = ((unsigned long)rand() << 32) | rand();

	if ((max - min) == ULONG_MAX) {
		return retval;
	}

	return (retval %  (max - min + 1)) + min;
}

int test_helpers_register_cb(union test_harness_cbs cb, enum cb_ids id)
{
	if (id >= CB_IDS) {
		return -EINVAL;
	}

	/*
	 * Covert the pointer stored in cb into a generic one
	 * and store it.
	 * We ignore the exact the cb corresponding to the cbs_id
	 * and just use the first one.
	 */
	callbacks[id] = (uintptr_t)cb.buffer_map;

	return 0;
}

int test_helpers_unregister_cb(enum cb_ids id)
{
	union test_harness_cbs cb;

	/*
	 * Set the callback to NULL.
	 * We ignore the exact the cb corresponding to the cbs_id
	 * and just use the first one.
	 */
	cb.buffer_map = NULL;
	return test_helpers_register_cb(cb, id);
}

/* Assertion control */
void __assert_fail(const char *assertion, const char *file,
		   unsigned int line, const char *function)
{
	(void)function;

	asserted = true;

	if (assert_expected == true) {
		if (strlen(assert_check) > 0U) {
			if (strncmp(assert_check, assertion,
				    strlen(assertion)) != 0) {
				VERBOSE("Assertion mismatch on %s at line %u\n",
					file, line);
				VERBOSE("Expected assertion \"%s\"\n",
					assert_check);
				VERBOSE("Received assertion \"%s\"\n",
					assertion);
				utest_exit_fail("Assertion mismatch\n");
			}
		}
	} else {
		VERBOSE("Unexpected assertion \"%s\" on file %s at line %u\n",
			assertion, file, line);
		utest_exit_fail("Unexpected assertion\n");
	}

	assert_check[0] = '\0';
	assert_expected = false;

	VERBOSE("Expected assertion \"%s\" on file %s at line %u\n",
			assertion, file, line);

	utest_exit_pass();
}

void test_helpers_expect_assert_fail_with_check(bool expected, char *check)
{
	if (check == NULL) {
		assert_check[0] = '\0';
	} else {
		if (strlen(check) > CHECK_SIZE) {
			utest_exit_fail("Assert check string too large");
		}
		strncpy(assert_check, check, CHECK_SIZE);
		assert_check[CHECK_SIZE] = '\0';
	}
	asserted = false;
	assert_expected = expected;
}

void test_helpers_expect_assert_fail(bool expected)
{
	test_helpers_expect_assert_fail_with_check(expected, NULL);
}

void test_helpers_fail_if_no_assert_failed(void)
{
	if (asserted == false) {
		utest_exit_fail("Expected assertion did not happen");
	} else {
		asserted = false;
		assert_check[0] = '\0';
		assert_expected = false;
	}

}

void test_helpers_init(void)
{
	static int random_seed;

	/* Initialize the random seed */
	while (random_seed == 0) {
		random_seed = (int)time(NULL);
		srand(random_seed);
	}
}

struct granule *test_helpers_granule_struct_base(void)
{
	return addr_to_granule(host_util_get_granule_base());
}

/******************************************************************
 * Private APIs shared with other host_test files.
 *****************************************************************/
uintptr_t get_cb(enum cb_ids id)
{
	assert(id < CB_IDS);

	return callbacks[id];

}
