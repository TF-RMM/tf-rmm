/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

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
	RMM_EL3_IFC_MAKE_VERSION(RMM_EL3_IFC_VERS_MAJOR, 4)
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
void print_help(char *app_name)
{
	rmm_log("Run RMM on the host\n\n");
	rmm_log("Usage: %s [-h|--help] [app_id app_elf [...]]\n\n", app_name);

	rmm_log("Arguments:\n");
	rmm_log("  -h, --help      print this message and exit.\n");
	rmm_log("  app_id          Integer value of app id of the app.\n");
	rmm_log("  app_elf         path to the app's elf file.\n");
}

void process_command_line_arguments(int argc, char *argv[])
{
	int ret __unused;
	int i;
	unsigned int curr_app_index = 0;
	char *end;
	struct app_header *app_header;

	for (i = 1; i < argc; ++i) {
		if (strcmp(argv[i], "--help") == 0 ||
		   strcmp(argv[i], "-h") == 0) {
			print_help(argv[0]);
			exit(0);
		}
		if (curr_app_index >= APP_COUNT) {
			ERROR("Too many apps (more than %d).\n", APP_COUNT);
			exit(1);
		}
		if (i+1 >= argc) {
			ERROR("Invalid number of arguments.\n");
			exit(1);
		}

		ret = app_get_header_ptr_at_index(curr_app_index, &app_header);
		assert(ret == 0);
		app_header->app_id = strtol(argv[i], &end, 0);
		if (end != argv[i] + strlen(argv[i])) {
			ERROR("Invalid app id '%s'.\n", argv[i]);
			exit(1);
		}
		i += 1;
		app_header->app_elf_name = argv[i];
		NOTICE("Registering app at idx %u: id=%lu, filename='%s'\n",
			curr_app_index, app_header->app_id, app_header->app_elf_name);

		/* test opening the image file */
		FILE *f = fopen(app_header->app_elf_name, "rb");

		if (f == NULL) {
			ERROR("Failed to open file '%s'\n", app_header->app_elf_name);
			exit(1);
		}
		size_t bytes_read = fread(&ret, 1U, 1U, f);

		if (bytes_read != 1) {
			ERROR("Failed to read from file '%s'\n", app_header->app_elf_name);
			exit(1);
		}
		ret = fclose(f);
		if (ret != 0) {
			ERROR("Failed to close file during read test'%s'\n",
				app_header->app_elf_name);
			exit(1);
		}
		++curr_app_index;
	}
}

int main(int argc, char *argv[])
{
	int rc;

	process_command_line_arguments(argc, argv);

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
