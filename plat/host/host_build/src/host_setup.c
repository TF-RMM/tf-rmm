/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <app.h>
#include <app_header.h>
#include <arch_helpers.h>
#include <assert.h>
#include <debug.h>
#include <host_realm.h>
#include <host_rmi_wrappers.h>
#include <host_utils.h>
#include <platform_api.h>
#include <rmm_el3_ifc.h>
#include <s2tt.h>
#include <smc-rmi.h>
#include <smc-rsi.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

/* Create a simple 4 level (Lvl 0 - LvL 3) RTT structure */
#define RTT_COUNT 4

/* Define the EL3-RMM interface version as set from EL3 */
#define EL3_IFC_ABI_VERSION		\
	RMM_EL3_IFC_MAKE_VERSION(RMM_EL3_IFC_VERS_MAJOR, RMM_EL3_IFC_VERS_MINOR)
#define RMM_EL3_MAX_CPUS		(1U)

static struct host_realm g_realm;

/*
 * Function to emulate the MMU enablement for the fake_host architecture.
 */
static void enable_fake_host_mmu(void)
{
	write_sctlr_el2(SCTLR_ELx_WXN_BIT | SCTLR_ELx_M_BIT);
}

void *allocate_granule(void)
{
	static unsigned int next_granule_index;
	unsigned long granule;

	if (next_granule_index >= HOST_NR_GRANULES) {
		panic();
	}

	granule = host_util_get_granule_base() +
		  next_granule_index * GRANULE_SIZE;
	++next_granule_index;

	return (void *)granule;
}

unsigned long host_realm_get_realm_buffer(void)
{
	return (unsigned long)g_realm.realm_buffer;
}


static int host_create_realm_and_activate(struct host_realm *realm)
{
	struct smc_result result;
	unsigned int i;

	/* Allocate granules */
	realm->rd = allocate_granule();
	realm->rec = allocate_granule();
	realm->rec_params = allocate_granule();
	realm->rec_run = allocate_granule();
	realm->realm_params = allocate_granule();

	host_rmi_version(MAKE_RMI_REVISION(1, 0), &result);
	CHECK_RMI_RESULT();
	INFO("RMI Version is 0x%lx : 0x%lx\n", result.x[1], result.x[2]);

	host_rmi_granule_delegate(realm->rd, &result);
	CHECK_RMI_RESULT();
	host_rmi_granule_delegate(realm->rec, &result);
	CHECK_RMI_RESULT();
	for (i = 0; i < RTT_COUNT; ++i) {
		realm->rtts[i] = allocate_granule();
		host_rmi_granule_delegate(realm->rtts[i], &result);
		CHECK_RMI_RESULT();
	}

	memset(realm->realm_params, 0, sizeof(*realm->realm_params));
	realm->realm_params->s2sz = arch_feat_get_pa_width();
	realm->realm_params->rtt_num_start = 1;
	realm->realm_params->rtt_base = (uintptr_t)realm->rtts[0];
	realm->realm_params->num_bps = 1;
	realm->realm_params->num_wps = 1;

	host_rmi_realm_create(realm->rd, realm->realm_params, &result);
	CHECK_RMI_RESULT();

	/* Create RTT table to start at IPA 0x0 */
	for (i = 1; i < RTT_COUNT; ++i) {
		host_rmi_rtt_create(realm->rd, realm->rtts[i], 0, i, &result);
		CHECK_RMI_RESULT();
	}

	realm->realm_buffer = (uintptr_t)allocate_granule();
	host_rmi_granule_delegate((void *)realm->realm_buffer, &result);
	CHECK_RMI_RESULT();

	host_rmi_rtt_init_ripas(realm->rd, REALM_BUFFER_IPA,
				REALM_BUFFER_IPA + GRANULE_SIZE,
				&result);
	CHECK_RMI_RESULT();

	host_rmi_data_create_unknown(realm->rd, realm->realm_buffer, REALM_BUFFER_IPA, &result);
	CHECK_RMI_RESULT();

	host_rmi_rec_aux_count(realm->rd, &result);
	CHECK_RMI_RESULT();
	realm->rec_aux_count = result.x[1];

	assert(realm->rec_aux_count == MAX_REC_AUX_GRANULES);
	INFO("A rec requires %lu rec aux pages\n", realm->rec_aux_count);

	memset(realm->rec_params, 0, sizeof(*realm->rec_params));
	for (i = 0; i < realm->rec_aux_count; ++i) {
		realm->rec_aux_granules[i] = allocate_granule();
		realm->rec_params->aux[i] = (uintptr_t)realm->rec_aux_granules[i];
		host_rmi_granule_delegate(realm->rec_aux_granules[i], &result);
		CHECK_RMI_RESULT();
	}
	realm->rec_params->num_aux = realm->rec_aux_count;
	realm->rec_params->flags |= REC_PARAMS_FLAG_RUNNABLE;
	realm->rec_params->pc = (uintptr_t)realm_start;

	host_rmi_rec_create(realm->rd, realm->rec, realm->rec_params, &result);
	CHECK_RMI_RESULT();
	host_rmi_realm_activate(realm->rd, &result);
	CHECK_RMI_RESULT();

	return 0;
}

static int host_destroy_realm(struct host_realm *realm)
{
	struct smc_result result;
	unsigned long i;

	assert(realm != NULL);

	host_rmi_rec_destroy(realm->rec, &result);
	CHECK_RMI_RESULT();

	for (i = 0; i < realm->rec_aux_count; ++i) {
		host_rmi_granule_undelegate(realm->rec_aux_granules[i], &result);
		CHECK_RMI_RESULT();
	}

	host_rmi_data_destroy(realm->rd, REALM_BUFFER_IPA, &result);
	CHECK_RMI_RESULT();
	host_rmi_granule_undelegate((void *)realm->realm_buffer, &result);
	CHECK_RMI_RESULT();

	for (i = RTT_COUNT-1; i >= 1; --i) {
		host_rmi_rtt_destroy(realm->rd, 0, i, &result);
		CHECK_RMI_RESULT();
		host_rmi_granule_undelegate(realm->rtts[i], &result);
		CHECK_RMI_RESULT();
	}

	host_rmi_realm_destroy(realm->rd, &result);
	CHECK_RMI_RESULT();
	host_rmi_granule_undelegate(realm->rd, &result);
	CHECK_RMI_RESULT();
	host_rmi_granule_undelegate(realm->rec, &result);
	CHECK_RMI_RESULT();

	return 0;
}

static int host_realm_run_attest(struct host_realm *realm)
{
	struct smc_result result;

	/* Execute the Realm */
	memset(realm->rec_run, 0, sizeof(*realm->rec_run));
	host_rmi_rec_enter(realm->rec, realm->rec_run, &result);
	CHECK_RMI_RESULT();

	while (realm->rec_run->exit.exit_reason == RMI_EXIT_IRQ) {
		/* Clear the IRQ in ISR_EL1 and re-enter Realm */
		host_write_sysreg("isr_el1", 0x0);
		host_rmi_rec_enter(realm->rec, realm->rec_run, &result);
		CHECK_RMI_RESULT();
	}

	if (realm->rec_run->exit.exit_reason == RMI_EXIT_FIQ) {
		INFO("Realm executed successfully and exited due to FIQ.\n");
	}

	return 0;
}

void initialise_app_headers(int argc, char *argv[])
{
	(void) argc;
	int ret __unused;
	struct app_header *app_header;
	char *base_dir, *base_dir_copy, *lastPtr;

	/* Define default apps with their metadata */
	static const struct {
		unsigned long id;
		const char *filename;
	} apps[] = {
		{ RMM_RANDOM_APP_ID, "rmm_app_random.elf" },
		{ ATTESTATION_APP_ID, "rmm_app_attestation.elf" }
		/* Add new Apps here */
	};

	/* Get base directory from argv[0] */
	base_dir_copy = strdup(argv[0]);
	if (base_dir_copy == NULL) {
		ERROR("Failed to allocate memory for base directory\n");
		exit(1);
	}

	lastPtr = strrchr(base_dir_copy, '/');
	if (lastPtr != NULL) {
		*(lastPtr + 1) = '\0';
	} else {
		base_dir_copy[0] = '\0';
	}
	base_dir = base_dir_copy;

	/* Register apps with their full paths */
	for (unsigned int idx = 0; idx < APP_COUNT - 1; idx++) {
		char *full_path;
		size_t path_len;

		ret = app_get_header_ptr_at_index(idx, &app_header);
		assert(ret == 0);

		/* Calculate required buffer size and allocate */
		path_len = strlen(base_dir) + strlen(apps[idx].filename) + 1;
		full_path = malloc(path_len);
		if (full_path == NULL) {
			ERROR("Failed to allocate memory for app path\n");
			free(base_dir_copy);
			exit(1);
		}

		/* Build full path */
		(void) snprintf(full_path, path_len, "%s%s", base_dir, apps[idx].filename);

		/* Check if file exists and is readable */
		FILE *test_file = fopen(full_path, "rb");
		if (test_file == NULL) {
			ERROR("App file not found or not readable: %s\n", full_path);
			free(full_path);
			free(base_dir_copy);
			exit(1);
		}
		(void) fclose(test_file);

		app_header->app_id = apps[idx].id;
		app_header->app_elf_name = full_path;

		NOTICE("Registering app: id=%lu, filename='%s'\n",
			app_header->app_id, full_path);
	}
	free(base_dir_copy);
}

int main(int argc, char *argv[])
{
	int rc;

	initialise_app_headers(argc, argv);

	VERBOSE("RMM: Beginning of Fake Host execution\n");

	host_util_set_cpuid(0U);

	host_util_setup_sysreg_and_boot_manifest();

	arch_features_query_el3_support();

	plat_setup(0UL,
		   EL3_IFC_ABI_VERSION,
		   RMM_EL3_MAX_CPUS,
		   (uintptr_t)host_util_get_el3_rmm_shared_buffer());

	/*
	 * Enable the MMU. This is needed as some initialization code
	 * called by rmm_main() asserts that the mmu is enabled.
	 */
	enable_fake_host_mmu();

	/* Start RMM */
	rmm_main();

	/* Create a realm and a rec */
	if (host_create_realm_and_activate(&g_realm) != 0) {
		ERROR("ERROR: failed to create realm");
		return -1;
	}

	/* Run rec to invoke attest related RSIs */
	rc = host_realm_run_attest(&g_realm);
	if (rc != 0) {
		ERROR("ERROR: host_realm_rec_run_attest_rsi failed\n");
		return -1;
	}

	/* Destroy the realm and all related resources */
	(void)host_destroy_realm(&g_realm);

	VERBOSE("RMM: Fake Host execution completed\n");

	return 0;
}
