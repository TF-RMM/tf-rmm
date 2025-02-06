/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef APP_FW_STRUCTURES_H
#define APP_FW_STRUCTURES_H

#include <debug.h>
#include <pthread.h>
#include <stdbool.h>
#include <stdlib.h>
#include <unistd.h>
#include <utils_def.h>

struct app_process_data {
	unsigned long app_id;
	int fd_rmm_to_app_process;
	int fd_app_process_to_rmm;
	pid_t pid;
};

struct app_data_cfg {
	unsigned long app_id;
	void *el2_shared_page;
	/* This thread ID is valid in the corresponding app process, not in the
	 * main RMM process!
	 */
	pthread_t thread_id;
};

#endif /* APP_FW_STRUCTURES_H */
