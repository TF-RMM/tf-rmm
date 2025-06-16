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
	/*
	 * This thread ID is valid in the corresponding app process, not in the
	 * main RMM process!
	 */
	pthread_t thread_id;
	/*
	 * Points to a dynamically allocated buffer that will hold a copy of the
	 * app instance's heap. It is used to emulate the RMM EL2 code's direct
	 * access to El0 app heap memory.
	 */
	void *app_heap;
	size_t heap_size;
	uint32_t exit_flag; /* App Exit Flag */
};

#endif /* APP_FW_STRUCTURES_H */
