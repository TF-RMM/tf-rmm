/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <app_common.h>
#include <app_common_arch.h>
#include <assert.h>
#include <debug.h>
#include <el0_app_helpers.h>
#define MINICORO_IMPL
#include "minicoro.h"
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <utils_def.h>

static uint8_t shared_buffer[GRANULE_SIZE] __aligned(GRANULE_SIZE);
static struct app_instance_data_list_t *instance_list;

struct app_instance_data_t {
	/* Process pipe fds — set by run_app_instance() before each resume */
	int read_fd;
	int write_fd;
	void *heap_start;
	size_t heap_size;
};

struct app_instance_data_list_t {
	struct app_instance_data_t data;
	mco_coro *coro;
	struct app_instance_data_list_t *next;
};

/* Logging for RMM Fake Host EL0 apps */
void rmm_log(const char *fmt, ...)
{
	va_list args;

	va_start(args, fmt);
	(void)vprintf(fmt, args);
	va_end(args);

	(void)fflush(stdout);
}

void *get_shared_mem_start(void)
{
	return shared_buffer;
}

size_t get_shared_mem_size(void)
{
	return GRANULE_SIZE;
}

static struct app_instance_data_list_t *get_instance_list_item(mco_coro *coro)
{
	struct app_instance_data_list_t *curr = instance_list;

	while (curr != NULL) {
		if (curr->coro == coro) {
			return curr;
		}
		curr = curr->next;
	}
	return NULL;
}

static struct app_instance_data_t *get_current_instance_data(void)
{
	mco_coro *co = mco_running();

	return (struct app_instance_data_t *)mco_get_user_data(co);
}

void *get_heap_start(void)
{
	struct app_instance_data_t *app_data = get_current_instance_data();

	return app_data->heap_start;
}

static void insert_instance_data(struct app_instance_data_list_t *inst_data)
{
	struct app_instance_data_list_t **tail = &instance_list;

	while (*tail != NULL) {
		tail = &((*tail)->next);
	}
	*tail = inst_data;
}

/* Call a service from the app
 *
 * Write the service call request directly to the process pipe, yield to the
 * main loop, and read back the results when resumed.
 */
unsigned long el0_app_service_call(unsigned long service_index,
				   unsigned long arg0,
				   unsigned long arg1,
				   unsigned long arg2,
				   unsigned long arg3)
{
	struct app_instance_data_t *app_data = get_current_instance_data();

	assert(app_data->read_fd >= 0);
	assert(app_data->write_fd >= 0);

	unsigned long reason = APP_SERVICE_CALL;

	/* Write request directly to the process pipe */
	WRITE_OR_EXIT(app_data->write_fd, &reason, sizeof(reason));
	WRITE_OR_EXIT(app_data->write_fd, &service_index, sizeof(service_index));
	WRITE_OR_EXIT(app_data->write_fd, &arg0, sizeof(arg0));
	WRITE_OR_EXIT(app_data->write_fd, &arg1, sizeof(arg1));
	WRITE_OR_EXIT(app_data->write_fd, &arg2, sizeof(arg2));
	WRITE_OR_EXIT(app_data->write_fd, &arg3, sizeof(arg3));
	WRITE_OR_EXIT(app_data->write_fd, shared_buffer, sizeof(shared_buffer));
	WRITE_OR_EXIT(app_data->write_fd, &app_data->heap_size, sizeof(size_t));
	WRITE_OR_EXIT(app_data->write_fd, app_data->heap_start, app_data->heap_size);

	/* Yield to main loop — framework will process the service call */
	mco_yield(mco_running());

	/* Resumed: read response directly from process pipe */
	unsigned long retval;
	size_t heap_size;

	READ_OR_EXIT(app_data->read_fd, &retval, sizeof(retval));
	READ_OR_EXIT(app_data->read_fd, shared_buffer, sizeof(shared_buffer));
	READ_OR_EXIT(app_data->read_fd, &heap_size, sizeof(size_t));
	assert(heap_size == app_data->heap_size);
	READ_OR_EXIT(app_data->read_fd, app_data->heap_start, app_data->heap_size);
	return retval;
}

void el0_app_yield(void)
{
	struct app_instance_data_t *app_data = get_current_instance_data();

	assert(app_data->read_fd >= 0);
	assert(app_data->write_fd >= 0);

	unsigned long reason = APP_YIELD_CALL;

	/* Write yield request directly to the process pipe */
	WRITE_OR_EXIT(app_data->write_fd, &reason, sizeof(reason));
	WRITE_OR_EXIT(app_data->write_fd, shared_buffer, sizeof(shared_buffer));
	WRITE_OR_EXIT(app_data->write_fd, &app_data->heap_size, sizeof(size_t));
	WRITE_OR_EXIT(app_data->write_fd, app_data->heap_start, app_data->heap_size);

	/* Yield to main loop */
	mco_yield(mco_running());

	/* Resumed: read updated state from process pipe */
	size_t heap_size;

	READ_OR_EXIT(app_data->read_fd, shared_buffer, sizeof(shared_buffer));
	READ_OR_EXIT(app_data->read_fd, &heap_size, sizeof(size_t));
	assert(heap_size == app_data->heap_size);
	READ_OR_EXIT(app_data->read_fd, app_data->heap_start, app_data->heap_size);
}

void app_instance_main(mco_coro *co)
{
	struct app_instance_data_t *app_data =
		(struct app_instance_data_t *)mco_get_user_data(co);

	unsigned long arg0, arg1, arg2, arg3;

	while (true) {
		unsigned long app_func_id;
		size_t heap_size;

		assert(app_data->read_fd >= 0);

		READ_OR_EXIT(app_data->read_fd, &app_func_id, sizeof(app_func_id));

		/* If exiting app instance, coroutine returns (state becomes MCO_DEAD) */
		if (app_func_id == EXIT_APP_INSTANCE) {
			return;
		}

		/*
		 * write_fd is not set in the EXIT path (exit_app_instances
		 * only provides a read pipe), so assert it after the EXIT
		 * check where we actually need it.
		 */
		assert(app_data->write_fd >= 0);

		READ_OR_EXIT(app_data->read_fd, &arg0, sizeof(arg0));
		READ_OR_EXIT(app_data->read_fd, &arg1, sizeof(arg1));
		READ_OR_EXIT(app_data->read_fd, &arg2, sizeof(arg2));
		READ_OR_EXIT(app_data->read_fd, &arg3, sizeof(arg3));
		READ_OR_EXIT(app_data->read_fd, shared_buffer, sizeof(shared_buffer));
		READ_OR_EXIT(app_data->read_fd, &heap_size, sizeof(size_t));
		if (heap_size != 0) {
			assert(heap_size == app_data->heap_size);
			READ_OR_EXIT(app_data->read_fd, app_data->heap_start, app_data->heap_size);
		}

		unsigned long retval = el0_app_entry_func(app_func_id, arg0, arg1, arg2, arg3);
		unsigned long reason = APP_EXIT_CALL;

		/* Write result directly to process pipe */
		WRITE_OR_EXIT(app_data->write_fd, &reason, sizeof(reason));
		WRITE_OR_EXIT(app_data->write_fd, &retval, sizeof(retval));
		WRITE_OR_EXIT(app_data->write_fd, shared_buffer, sizeof(shared_buffer));
		WRITE_OR_EXIT(app_data->write_fd, &app_data->heap_size, sizeof(size_t));
		WRITE_OR_EXIT(app_data->write_fd, app_data->heap_start, app_data->heap_size);

		/* Yield back to main loop */
		mco_yield(co);
	}
}

static mco_coro *create_app_instance(void)
{
	struct app_instance_data_list_t *instance_list_new;
	mco_result res;

	instance_list_new = (struct app_instance_data_list_t *)
		malloc(sizeof(struct app_instance_data_list_t));
	if (instance_list_new == NULL) {
		exit(1);
	}

	instance_list_new->data.heap_size = get_heap_page_count() * GRANULE_SIZE;
	instance_list_new->data.heap_start = malloc(instance_list_new->data.heap_size);
	if (instance_list_new->data.heap_start == NULL) {
		exit(1);
	}

	/* Pipe fds will be set per-call in run_app_instance() */
	instance_list_new->data.read_fd = -1;
	instance_list_new->data.write_fd = -1;

	mco_desc desc = mco_desc_init(app_instance_main, 0);
	desc.user_data = &instance_list_new->data;

	res = mco_create(&instance_list_new->coro, &desc);
	if (res != MCO_SUCCESS) {
		ERROR("Failed to create coroutine: %s\n", mco_result_description(res));
		exit(1);
	}

	insert_instance_data(instance_list_new);

	return instance_list_new->coro;
}

void run_app_instance(int process_read_fd, int process_write_fd, mco_coro *coro)
{
	struct app_instance_data_list_t *instance_data = get_instance_list_item(coro);
	mco_result res;

	/* Set the process pipe fds for this call */
	instance_data->data.read_fd = process_read_fd;
	instance_data->data.write_fd = process_write_fd;

	/* Resume the coroutine — it will read from / write to process pipe */
	res = mco_resume(coro);
	if (res != MCO_SUCCESS) {
		ERROR("Failed to resume coroutine: %s\n", mco_result_description(res));
		exit(1);
	}

	/* Invalidate fds — only valid during coroutine execution */
	instance_data->data.read_fd = -1;
	instance_data->data.write_fd = -1;
}

int exit_app_instances(mco_coro *coro)
{
	struct app_instance_data_list_t *prev = NULL;
	struct app_instance_data_list_t *curr = instance_list;
	unsigned long command = EXIT_APP_INSTANCE;

	while (curr != NULL) {
		if (curr->coro == coro) {
			/*
			 * Use a local pipe to deliver the EXIT command to
			 * the coroutine. The coroutine reads from read_fd,
			 * so we write EXIT to the pipe's write end and
			 * point read_fd at the pipe's read end.
			 */
			int exit_pipe[2];

			if (pipe(exit_pipe) == -1) {
				exit(1);
			}

			curr->data.read_fd = exit_pipe[0];
			WRITE_OR_EXIT(exit_pipe[1], &command, sizeof(command));
			mco_resume(coro);
			close(exit_pipe[0]);
			close(exit_pipe[1]);

			/* Remove from list */
			if (prev == NULL) {
				instance_list = curr->next;
			} else {
				prev->next = curr->next;
			}

			/* Clean up */
			mco_destroy(coro);
			free(curr->data.heap_start);
			free(curr);

			return 0;
		}
		prev = curr;
		curr = curr->next;
	}
	return 1;
}

int main(int argc, char **argv)
{
	char *end;
	int ret;
	int process_read_fd;
	int process_write_fd;

	if (argc != 3) {
		ERROR("argc is %d instead of 3\n", argc);
		return 1;
	}

	process_read_fd = (int)strtol(argv[1], &end, 0);
	if (end != argv[1] + strlen(argv[1])) {
		ERROR("App: Invalid read fd '%s'.\n", argv[1]);
		return 1;
	}

	process_write_fd = (int)strtol(argv[2], &end, 0);

	if (end != argv[2] + strlen(argv[2])) {
		ERROR("App: Invalid write fd '%s'.\n", argv[2]);
		return 1;
	}

	while (true) {
		unsigned long command;

		/* read the command */
		READ_OR_EXIT_NOERROR(process_read_fd, &command, sizeof(command));

		switch (command) {
		case CREATE_NEW_APP_INSTANCE:
		{
			size_t heap_size = 0U;
			mco_coro *coro = create_app_instance();
			struct app_instance_data_t *app_data =
				(struct app_instance_data_t *)mco_get_user_data(coro);

			assert(app_data != NULL);
			heap_size = app_data->heap_size;

			/* Send the coro pointer as the opaque instance handle */
			void *coro_handle = coro;

			WRITE_OR_EXIT(process_write_fd, &coro_handle, sizeof(coro_handle));
			WRITE_OR_EXIT(process_write_fd, &heap_size, sizeof(heap_size));
			break;
		}
		case RUN_APP_INSTANCE:
		{
			void *coro_handle;

			READ_OR_EXIT(process_read_fd, &coro_handle, sizeof(coro_handle));
			run_app_instance(process_read_fd, process_write_fd, coro_handle);
			break;
		}
		case EXIT_APP_INSTANCE:
		{
			void *coro_handle;

			/* Read the coro handle and exit the instance */
			READ_OR_EXIT(process_read_fd, &coro_handle, sizeof(coro_handle));
			ret = exit_app_instances(coro_handle);

			/* Write back status of exiting app instances */
			WRITE_OR_EXIT(process_write_fd, &ret, sizeof(ret));

			break;
		}
		default:
			ERROR("APP - Invalid command %lu (%lx)\n", command, command);
			exit(1);
		}
	}
	return 0;
}
