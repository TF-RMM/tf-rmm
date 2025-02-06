/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <app_common.h>
#include <app_common_arch.h>
#include <assert.h>
#include <debug.h>
#include <el0_app_helpers.h>
#include <pthread.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <utils_def.h>

extern size_t app_heap_page_count;

static uint8_t shared_buffer[GRANULE_SIZE];
static struct app_instance_data_list_t *instance_list;

struct app_instance_data_t {
	int read_from_main_fd;
	int write_to_main_fd;
	void *heap_start;
	size_t heap_size;
};

struct app_instance_data_list_t {
	struct app_instance_data_t data;
	pthread_t thread_id;
	int read_from_instance_fd;
	int write_to_instance_fd;
	struct app_instance_data_list_t *next;
};

void *get_shared_mem_start(void)
{
	return shared_buffer;
}

size_t get_shared_mem_size(void)
{
	return GRANULE_SIZE;
}

static struct app_instance_data_list_t *get_instance_list_item(pthread_t thread_id)
{
	struct app_instance_data_list_t *curr = instance_list;

	while (curr != NULL) {
		if (curr->thread_id == thread_id) {
			return curr;
		}
		curr = curr->next;
	}
	return NULL;
}

static struct app_instance_data_t *get_instance_data(pthread_t thread_id)
{
	struct app_instance_data_list_t *curr =
		get_instance_list_item(thread_id);
	if (curr != NULL) {
		return &curr->data;
	}
	return NULL;
}

void *get_heap_start(void)
{
	pthread_t thread_id = pthread_self();
	struct app_instance_data_t *app_data = get_instance_data(thread_id);

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
 * Write the service call ID and parameters to the RMM, and read back the
 * results.
 */
unsigned long el0_app_service_call(unsigned long service_index,
				   unsigned long arg0,
				   unsigned long arg1,
				   unsigned long arg2,
				   unsigned long arg3)
{

	pthread_t thread_id = pthread_self();
	struct app_instance_data_t *app_data = get_instance_data(thread_id);

	unsigned long reason = APP_SERVICE_CALL;

	unsigned long bytes_to_forward =
		6 * sizeof(unsigned long) +
		sizeof(shared_buffer);

	WRITE_OR_EXIT(app_data->write_to_main_fd, &bytes_to_forward, sizeof(bytes_to_forward));
	WRITE_OR_EXIT(app_data->write_to_main_fd, &reason, sizeof(reason));
	WRITE_OR_EXIT(app_data->write_to_main_fd, &service_index, sizeof(service_index));
	WRITE_OR_EXIT(app_data->write_to_main_fd, &arg0, sizeof(arg0));
	WRITE_OR_EXIT(app_data->write_to_main_fd, &arg1, sizeof(arg1));
	WRITE_OR_EXIT(app_data->write_to_main_fd, &arg2, sizeof(arg2));
	WRITE_OR_EXIT(app_data->write_to_main_fd, &arg3, sizeof(arg3));
	WRITE_OR_EXIT(app_data->write_to_main_fd, shared_buffer, sizeof(shared_buffer));

	unsigned long retval;

	READ_OR_EXIT(app_data->read_from_main_fd, &retval, sizeof(retval));
	READ_OR_EXIT(app_data->read_from_main_fd, shared_buffer, sizeof(shared_buffer));
	return retval;
}

void *app_instance_main(void *args)
{
	struct app_instance_data_t *app_data =
		(struct app_instance_data_t *)args;

	unsigned long arg0, arg1, arg2, arg3;


	while (true) {
		unsigned long app_func_id;

		READ_OR_EXIT(app_data->read_from_main_fd, &app_func_id, sizeof(app_func_id));
		READ_OR_EXIT(app_data->read_from_main_fd, &arg0, sizeof(arg0));
		READ_OR_EXIT(app_data->read_from_main_fd, &arg1, sizeof(arg1));
		READ_OR_EXIT(app_data->read_from_main_fd, &arg2, sizeof(arg2));
		READ_OR_EXIT(app_data->read_from_main_fd, &arg3, sizeof(arg3));
		READ_OR_EXIT(app_data->read_from_main_fd, shared_buffer, sizeof(shared_buffer));

		unsigned long retval = el0_app_entry_func(app_func_id, arg0, arg1, arg2, arg3);
		unsigned long reason = APP_EXIT_CALL;

		unsigned long bytes_to_forward =
			2 * sizeof(unsigned long) +
			sizeof(shared_buffer);

		WRITE_OR_EXIT(app_data->write_to_main_fd, &bytes_to_forward,
			sizeof(bytes_to_forward));
		WRITE_OR_EXIT(app_data->write_to_main_fd, &reason, sizeof(reason));
		WRITE_OR_EXIT(app_data->write_to_main_fd, &retval, sizeof(retval));
		WRITE_OR_EXIT(app_data->write_to_main_fd, shared_buffer, sizeof(shared_buffer));
	}
	return NULL;
}

static pthread_t create_app_instance(void)
{
	/* TODO: The app instances are leaked, because there is no way currently
	 * to get notification of the main process about an app being destroyed.
	 */
	struct app_instance_data_list_t *instance_list_new;
	int ret;

	instance_list_new = (struct app_instance_data_list_t *)
		malloc(sizeof(struct app_instance_data_list_t));
	if (instance_list_new == NULL) {
		exit(1);
	}

	int fds_main_to_instance[2];
	int fds_instance_to_main[2];

	if (pipe(fds_main_to_instance) == -1) {
		exit(1);
	}
	if (pipe(fds_instance_to_main) == -1) {
		exit(1);
	}

	instance_list_new->read_from_instance_fd = fds_instance_to_main[0];
	instance_list_new->write_to_instance_fd = fds_main_to_instance[1];
	instance_list_new->data.read_from_main_fd = fds_main_to_instance[0];
	instance_list_new->data.write_to_main_fd = fds_instance_to_main[1];

	instance_list_new->data.heap_size = app_heap_page_count * GRANULE_SIZE;
	instance_list_new->data.heap_start = malloc(instance_list_new->data.heap_size);
	if (instance_list_new->data.heap_start == NULL) {
		exit(1);
	}

	insert_instance_data(instance_list_new);

	ret = pthread_create(&(instance_list_new->thread_id),
			     NULL,
			     app_instance_main,
			     &(instance_list_new->data));
	if (ret != 0) {
		exit(1);
	}
	return instance_list_new->thread_id;
}

void call_app_instance(int process_read_fd, int process_write_fd, pthread_t thread_id)
{

	struct app_instance_data_list_t *instance_data = get_instance_list_item(thread_id);

	unsigned long num_bytes_to_forward;
	unsigned long bytes_forwarded = 0;
	char copy_buffer[6*1024];

	/* Send the call details */
	READ_OR_EXIT(process_read_fd, &num_bytes_to_forward, sizeof(num_bytes_to_forward));
	while (bytes_forwarded < num_bytes_to_forward) {
		size_t to_forward = min(num_bytes_to_forward, sizeof(copy_buffer));

		READ_OR_EXIT(process_read_fd, copy_buffer, to_forward);
		WRITE_OR_EXIT(instance_data->write_to_instance_fd, copy_buffer, to_forward);
		bytes_forwarded += to_forward;
	}

	/* return the response */
	bytes_forwarded = 0;
	READ_OR_EXIT(instance_data->read_from_instance_fd, &num_bytes_to_forward,
		sizeof(num_bytes_to_forward));
	while (bytes_forwarded < num_bytes_to_forward) {
		size_t to_forward = min(num_bytes_to_forward, sizeof(copy_buffer));

		READ_OR_EXIT(instance_data->read_from_instance_fd, copy_buffer, to_forward);
		WRITE_OR_EXIT(process_write_fd, copy_buffer, to_forward);
		bytes_forwarded += to_forward;
	}
}

int main(int argc, char **argv)
{
	char *end;
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
			pthread_t thread_id = create_app_instance();

			WRITE_OR_EXIT(process_write_fd, &thread_id, sizeof(thread_id));
			break;
		}
		case CALL_APP_INSTANCE:
		{
			pthread_t thread_id;

			READ_OR_EXIT(process_read_fd, &thread_id, sizeof(thread_id));
			call_app_instance(process_read_fd, process_write_fd, thread_id);
			break;
		}
		default:
			ERROR("APP - Invalid command %lu (%lx)\n", command, command);
			exit(1);
		}
	}
	return 0;
}
