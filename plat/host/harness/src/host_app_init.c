/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <app.h>
#include <app_header.h>
#include <assert.h>
#include <debug.h>
#include <errno.h>
#include <limits.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>

/* Configuration: Enable/disable SPDM responder debug output */
#define ENABLE_SPDM_EMU_DEBUG 0  /* Set to 1 to enable SPDM-EMU debug prints */

/* Global PID for SPDM responder process */
static pid_t spdm_responder_pid __unused = -1;

/*
 * Returns a heap-allocated string containing the directory part of path
 * (i.e. argv[0] up to and including the last '/').  The caller must free()
 * the returned pointer.  Returns an empty string when path has no '/'.
 * Calls exit(1) on allocation failure.
 */
char *host_util_get_base_dir(const char *path)
{
	char *copy = strdup(path);
	char *lastPtr;

	if (copy == NULL) {
		ERROR("Failed to allocate memory for base directory\n");
		exit(1);
	}

	lastPtr = strrchr(copy, '/');
	if (lastPtr != NULL) {
		*(lastPtr + 1) = '\0';
	} else {
		copy[0] = '\0';
	}

	return copy;
}

void host_util_launch_spdm_responder_emu(char *base_dir)
{
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

	/* BANNED-API-CHECK[IGNORE] */
	if (snprintf(bin_path, sizeof(bin_path), "%s%s", base_dir, rel_bin) >=
	    (int)sizeof(bin_path)) {
		ERROR("spdm-emu responder path is too long\n");
		exit(1);
	}

	/* BANNED-API-CHECK[IGNORE] */
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
		/* BANNED-API-CHECK[IGNORE] */
		if (snprintf(cmd, sizeof(cmd),
			     "cd '%s' && '%s' --trans PCI_DOE 2>&1 | "
			     "awk '{print \"%s[SPDM-EMU] \" $0 \"%s\"; fflush()}'",
			     keys_abs, bin_abs, color_log, color_log_reset) >= (int)sizeof(cmd)) {
			ERROR("Command line too long\n");
			_exit(1);
		}
#else
		/* BANNED-API-CHECK[IGNORE] */
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
}

void host_util_initialise_app_headers(int argc, char *argv[])
{
	(void)argc;
	int ret __unused;
	struct app_header *app_header;
	char *base_dir;

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

	base_dir = host_util_get_base_dir(argv[0]);

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
			free(base_dir);
			exit(1);
		}

		/* Build full path */
		/* BANNED-API-CHECK[IGNORE] */
		(void) snprintf(full_path, path_len, "%s%s", base_dir, apps[idx].filename);

		/* Check if file exists and is readable */
		FILE *test_file = fopen(full_path, "rb");
		if (test_file == NULL) {
			ERROR("App file not found or not readable: %s\n", full_path);
			free(full_path);
			free(base_dir);
			exit(1);
		}
		(void)fclose(test_file);

		app_header->app_id = apps[idx].id;
		app_header->app_elf_name = full_path;

		NOTICE("Registering app: id=%lu, filename='%s'\n",
		       app_header->app_id, full_path);
	}

	free(base_dir);
}

/*
 * Stop the SPDM responder process if it's running.
 */
void host_util_stop_spdm_responder(void)
{
	int status;

	if (spdm_responder_pid > 0) {
		INFO("Stopping SPDM responder (PID: %d)\n", spdm_responder_pid);
		kill(spdm_responder_pid, SIGTERM);

		/* Wait for the process to terminate */
		waitpid(spdm_responder_pid, &status, 0);
		spdm_responder_pid = -1;
	}
}
