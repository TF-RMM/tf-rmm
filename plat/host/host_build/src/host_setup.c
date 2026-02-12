/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <app.h>
#include <app_header.h>
#include <arch_helpers.h>
#include <assert.h>
#include <debug.h>
#include <errno.h>
#include <host_realm.h>
#include <host_rmi_wrappers.h>
#include <host_utils.h>
#include <limits.h>
#include <platform_api.h>
#include <rmm_el3_ifc.h>
#include <s2tt.h>
#include <signal.h>
#include <smc-rmi.h>
#include <stdbool.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>

/* Configuration: Enable/disable SPDM responder debug output */
#define ENABLE_SPDM_EMU_DEBUG 0  /* Set to 1 to enable SPDM-EMU debug prints */

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
	unsigned long feat_reg0;
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

	/* Check if DA enabled in RMI features */
	host_rmi_features(RMI_FEATURE_REGISTER_0_INDEX, &result);
	CHECK_RMI_RESULT();
	feat_reg0 = result.x[1];

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

	/* Set Realm flags with DA enabled */
	if (EXTRACT(RMI_FEATURE_REGISTER_0_DA_EN, feat_reg0) ==
	    RMI_FEATURE_TRUE) {
		realm->realm_params->flags0 = INPLACE(RMI_REALM_FLAGS0_DA,
						      RMI_FEATURE_TRUE);
	} else {
		realm->realm_params->flags0 = INPLACE(RMI_REALM_FLAGS0_DA,
						      RMI_FEATURE_FALSE);
	}

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

	for (i = RTT_COUNT - 1; i >= 1; --i) {
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

/* Global PID for SPDM responder process */
static pid_t spdm_responder_pid __unused = -1;

static void launch_spdm_responder_emu(char *base_dir)
{
#ifdef RMM_V1_1
	pid_t pid;
	static const char *rel_bin = "spdm_emu/spdm_responder_emu";
	static const char *rel_keys = "spdm_emu/keys";
	static const char *color_log __unused = "\\033[90m"; /* gray */
	static const char *color_log_reset __unused = "\\033[0m";

	char bin_path[PATH_MAX];
	char keys_path[PATH_MAX];
	char bin_abs[PATH_MAX];
	char keys_abs[PATH_MAX];
	char cmd[PATH_MAX * 2];

	if (snprintf(bin_path, sizeof(bin_path), "%s%s", base_dir, rel_bin) >=
	    (int)sizeof(bin_path)) {
		ERROR("spdm-emu responder path is too long\n");
		exit(1);
	}

	if (snprintf(keys_path, sizeof(keys_path), "%s%s", base_dir, rel_keys) >=
	    (int)sizeof(keys_path)) {
		ERROR("spdm-emu keys path is too long\n");
		exit(1);
	}

	/* Absolute paths are needed for child process */
	if (realpath(bin_path, bin_abs) == NULL) {
		ERROR("SPDM responder realpath for '%s' failed: %s\n", bin_path, strerror(errno));
		exit(1);
	}
	if (realpath(keys_path, keys_abs) == NULL) {
		ERROR("SPDM keys realpath for '%s' failed: %s\n", keys_path, strerror(errno));
		exit(1);
	}

	pid = fork();
	if (pid < 0) {
		ERROR("Failed to fork responder: %s\n", strerror(errno));
		exit(1);
	}

	if (pid == 0) {
#if ENABLE_SPDM_EMU_DEBUG
		if (snprintf(cmd, sizeof(cmd),
			     "cd '%s' && '%s' --trans PCI_DOE 2>&1 | "
			     "awk '{print \"%s[SPDM-EMU] \" $0 \"%s\"; fflush()}'",
			     keys_abs, bin_abs, color_log, color_log_reset) >= (int)sizeof(cmd)) {
			ERROR("Command line too long\n");
			_exit(1);
		}
#else
		if (snprintf(cmd, sizeof(cmd),
			     "cd '%s' && '%s' --trans PCI_DOE > /dev/null 2>&1",
			     keys_abs, bin_abs) >= (int)sizeof(cmd)) {
			ERROR("Command line too long\n");
			_exit(1);
		}
#endif
		execl("/bin/sh", "sh", "-c", cmd, (char *)NULL);
		ERROR("Failed to exec SPDM responder: %s\n", strerror(errno));
		_exit(1);
	}

	INFO("Launched SPDM responder (pid %d)\n", pid);
	spdm_responder_pid = pid;

	/* Give the server more time to start listening and stabilize */
	usleep(1000000); /* 1 second */
#else
	(void)base_dir;
#endif
}

void initialise_app_headers(int argc, char *argv[])
{
	(void)argc;
	int ret __unused;
	struct app_header *app_header;
	char *base_dir, *base_dir_copy, *lastPtr;

	/* Define default apps with their metadata */
	static const struct {
		unsigned long id;
		const char *filename;
	} apps[] = {
		{ RMM_RANDOM_APP_ID, "rmm_app_random.elf" },
		{ ATTESTATION_APP_ID, "rmm_app_attestation.elf" },
		{ RMM_DEV_ASSIGN_APP_ID, "rmm_app_dev_assign.elf" }
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
	for (unsigned int idx = 0; idx < APP_COUNT; idx++) {
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
		(void)snprintf(full_path, path_len, "%s%s", base_dir, apps[idx].filename);

		/* Check if file exists and is readable */
		FILE *test_file = fopen(full_path, "rb");
		if (test_file == NULL) {
			ERROR("App file not found or not readable: %s\n", full_path);
			free(full_path);
			free(base_dir_copy);
			exit(1);
		}
		(void)fclose(test_file);

		app_header->app_id = apps[idx].id;
		app_header->app_elf_name = full_path;

		NOTICE("Registering app: id=%lu, filename='%s'\n",
		       app_header->app_id, full_path);
	}

	launch_spdm_responder_emu(base_dir);
	free(base_dir_copy);
}

uint64_t rmm_main(uint64_t token);
void rmm_arch_init(void);

/*
 * Stop the SPDM responder process if it's running.
 */
static void stop_spdm_responder(void)
{
#ifdef RMM_V1_1
	int status;

	if (spdm_responder_pid > 0) {
		INFO("Stopping SPDM responder (PID: %d)\n", spdm_responder_pid);
		kill(spdm_responder_pid, SIGTERM);

		/* Wait for the process to terminate */
		waitpid(spdm_responder_pid, &status, 0);
		spdm_responder_pid = -1;
	}
#endif
}

int main(int argc, char *argv[])
{
	int host_pdev_id;
	int host_vdev_id = -1;
	int rc;
	bool realm_created = false;

	initialise_app_headers(argc, argv);

	VERBOSE("RMM: Beginning of Fake Host execution\n");

	host_util_set_cpuid(0U);

	host_util_setup_sysreg_and_boot_manifest();

	arch_features_query_el3_support();

	rmm_arch_init();

	plat_setup(0UL,
		   EL3_IFC_ABI_VERSION,
		   RMM_EL3_MAX_CPUS,
		   (uintptr_t)host_util_get_el3_rmm_shared_buffer(),
		   0UL);

	/*
	 * Enable the MMU. This is needed as some initialization code
	 * called by rmm_main() asserts that the mmu is enabled.
	 */
	enable_fake_host_mmu();

	/* Start RMM */
	(void)rmm_main(0UL);

	/*
	 * Find devices (spdm_responder) and if any device exist create a PDEV
	 * instance of the device with RMM and establish a secure session with
	 * the device so that the device is in a assignable state to a Realm.
	 */
	host_pdev_id = host_pdev_probe_and_setup();
	if (host_pdev_id == -1) {
		ERROR("ERROR: host_device_init failed.\n");
		rc = -1;
		goto out_cleanup;
	}

	/* Create a realm and a rec */
	if (host_create_realm_and_activate(&g_realm) != 0) {
		ERROR("ERROR: failed to create realm");
		rc = -1;
		goto out_cleanup;
	}
	realm_created = true;

	/* Run rec to invoke attest related RSIs */
	rc = host_realm_run_attest(&g_realm);
	if (rc != 0) {
		ERROR("ERROR: host_realm_rec_run_attest_rsi failed\n");
		goto out_cleanup;
	}

	/* Create vdev instance and bind with the Realm */
	if (host_pdev_id > 0) {
		INFO("host: Assign vdev_tdi_id 0x%x to rd:\n", host_pdev_id);
		host_vdev_id = host_vdev_assign(&g_realm,
						(unsigned long)host_pdev_id);
		if (host_vdev_id < 0) {
			ERROR("ERROR: host_device_assign_to_realm\n");
			rc = -1;
			goto out_cleanup;
		}

		/* Run rec to invoke DA related RSIs */
		rc = host_realm_run_da(&g_realm);
		if (rc != 0) {
			ERROR("ERROR: host_realm_run_da_rsi failed\n");
			goto out_cleanup;
		}
	}

out_cleanup:
	/* Stop the VDEV and do vdev_destroy */
	if (host_vdev_id >= 0) {
		if (host_vdev_reclaim(&g_realm, host_vdev_id) != 0) {
			ERROR("ERROR: host_vdev_reclaim failed\n");
			rc = -1;
		}
	}

	/*
	 * This calls PDEV STOP and terminate secure session and calls
	 * PDEV DESTROY
	 */
	if (host_pdev_id > 0) {
		if (host_pdev_reclaim(host_pdev_id) != 0) {
			ERROR("ERROR: host_pdev_reclaim failed\n");
			rc = -1;
		}
	}

	/* Stop the SPDM responder process */
	stop_spdm_responder();

	if (realm_created) {
		/* Destroy the realm and all related resources */
		(void)host_destroy_realm(&g_realm);
	}

	VERBOSE("RMM: Fake Host execution completed\n");

	return rc;
}
