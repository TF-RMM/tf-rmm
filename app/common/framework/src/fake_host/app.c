/*
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <app.h>
#include <app_common.h>
#include <app_common_arch.h>
#include <app_header.h>
#include <app_header_private.h>
#include <app_services.h>
#include <assert.h>
#include <debug.h>
#include <errno.h>
#include <stdlib.h>
#include <time.h>
#include <unistd.h>

/*
 * TODO: The host application uses a single shared page that is the same for all
 *       the application instances. The best location for this buffer would be
 *       in struct app_data_cfg, but it doesn't fit there as a size limit on
 *       the `struct rec` size which contains attestation app's data.
 *       Remove this TODO once the aarch64 implementation uses a single shared
 *       page as well.
 */
static char shared_page[GRANULE_SIZE] __aligned(GRANULE_SIZE);

/* In case APP_COUNT is 0 or 1 then set a meaningful array size to prevent array
 * subscript <unknown> is outside array bounds warning
 */
/* NOLINTNEXTLINE(misc-redundant-expression) */
static struct app_process_data app_process_datas[(APP_COUNT < 2U)?(2U):(APP_COUNT)];
static size_t initialised_app_process_data_count;

void int_to_str(int value, char *buf, size_t buf_size)
{
	char digits[] = {'0', '1', '2', '3', '4', '5', '6', '7', '8', '9'};
	char reverse_buf[sizeof(int) * 3 + 2];
	char *c = reverse_buf;
	size_t buf_idx = 0;

	if (buf_size < sizeof(reverse_buf)) {
		if (buf_size > 0U) {
			buf[0] = '\0';
		}
		return;
	}

	if (value < 0) {
		buf[buf_idx++] = '-';
		value = -value;
	}
	do {
		*c = digits[value%10];
		value = value / 10;
		++c;
	} while (value != 0);
	do {
		--c;
		buf[buf_idx] = *c;
		++buf_idx;
	} while (c != reverse_buf);
	buf[buf_idx] = '\0';
}

static void start_app_process(unsigned long app_id, int read_fd, int write_fd)
{
	int ret;
	struct app_header *app_header;

	ret = app_get_header_ptr(app_id, &app_header);
	if (ret != 0) {
		ERROR("-----------------------------------------------------------------------\n");
		ERROR("This error usually happens when no app elf files are provided to the\n");
		ERROR("RMM core elf, or there is a mismatch between the app ID in the RMM core\n");
		ERROR("and the app ID provided in the command line.\n");
		ERROR("See the output with '--help'.\n");
		ERROR("-----------------------------------------------------------------------\n");
		exit(1);
	}

	char s_read_fd[sizeof(int) * 3 + 2];
	char s_write_fd[sizeof(int) * 3 + 2];

	int_to_str(read_fd, s_read_fd, sizeof(s_read_fd));
	int_to_str(write_fd, s_write_fd, sizeof(s_write_fd));
	char *args[] = {app_header->app_elf_name, s_read_fd, s_write_fd, NULL};

	ret = execv(app_header->app_elf_name, args);
	if (ret == -1) {
		perror("Failed to create child process");
		exit(1);
	}
}

static struct app_process_data *create_app_process(unsigned long app_id)
{
	/* To prevent array subscript <unknown> is outside array bounds warning */
	/* cppcheck-suppress unsignedPositive
	 * As initialised_app_process_data_count is unsigned,
	 * initialised_app_process_data_count >= APP_COUNT is always true if
	 * APP_COUNT is zero.
	 */
	if ((initialised_app_process_data_count == 0UL) &&
	    (initialised_app_process_data_count >= APP_COUNT)) {
		return NULL;
	}

	struct app_process_data *ret = &app_process_datas[initialised_app_process_data_count];

	int fds_rmm_to_app_process[2];
	int fds_app_process_to_rmm[2];

	if (pipe(fds_rmm_to_app_process) == -1) {
		return NULL;
	}
	if (pipe(fds_app_process_to_rmm) == -1) {
		return NULL;
	}

	ret->pid = fork();

	if (ret->pid == 0) {
		/* We are in the child process, close the unnecessary fds and
		 * execv into the app.
		 */
		close(fds_rmm_to_app_process[1]);
		close(fds_app_process_to_rmm[0]);
		start_app_process(app_id, fds_rmm_to_app_process[0], fds_app_process_to_rmm[1]);
		/* The function above should never return */
		assert(false);
	}

	close(fds_rmm_to_app_process[0]);
	close(fds_app_process_to_rmm[1]);
	ret->fd_rmm_to_app_process = fds_rmm_to_app_process[1];
	ret->fd_app_process_to_rmm = fds_app_process_to_rmm[0];
	ret->app_id = app_id;

	++initialised_app_process_data_count;
	return ret;
}

static struct app_process_data *get_app_process_data(unsigned long app_id)
{
	size_t i;

	/* To prevent array subscript <unknown> is outside array bounds warning */
	/* cppcheck-suppress unsignedPositive
	 * As initialised_app_process_data_count is unsigned,
	 * initialised_app_process_data_count >= APP_COUNT is always true if
	 * APP_COUNT is zero.
	 */
	if ((initialised_app_process_data_count == 0UL) &&
	    (initialised_app_process_data_count >= APP_COUNT)) {
		return NULL;
	}

	for (i = 0; i < initialised_app_process_data_count; ++i) {
		if (app_process_datas[i].app_id == app_id) {
			return &app_process_datas[i];
		}
	}

	return NULL;
}

void app_framework_setup(void)
{
	/* Not related to app initialisation, but this is a good location for
	 * one time initialisation
	 */
	srand(time(NULL));
}

int app_init_data(struct app_data_cfg *app_data,
		      unsigned long app_id,
		      uintptr_t granule_pas[],
		      size_t granule_count,
		      void *granule_va_start)
{
	struct app_process_data *app_process_data;
	unsigned long command;

	(void)granule_pas;
	(void)granule_count;
	(void)granule_va_start;

	app_process_data = get_app_process_data(app_id);
	if (app_process_data == NULL) {
		app_process_data = create_app_process(app_id);
		if (app_process_data == NULL) {
			return -EINVAL;
		}
	}

	/* Create the thread for this app instance */
	command = CREATE_NEW_APP_INSTANCE;

	WRITE_OR_EXIT(app_process_data->fd_rmm_to_app_process, &command, sizeof(command));
	READ_OR_EXIT(app_process_data->fd_app_process_to_rmm, &app_data->thread_id,
		sizeof(app_data->thread_id));
	app_data->el2_shared_page = NULL;
	app_data->app_id = app_id;
	app_data->app_heap = NULL;
	app_data->heap_size = 0;
	return 0;
}

void app_map_shared_page(struct app_data_cfg *app_data)
{
	assert(app_data->el2_shared_page == NULL);
	app_data->el2_shared_page = shared_page;
}

void app_unmap_shared_page(struct app_data_cfg *app_data)
{
	assert(app_data->el2_shared_page != NULL);
	app_data->el2_shared_page = NULL;
}

static unsigned long app_run_internal(struct app_data_cfg *app_data,
	struct app_process_data *app_process_data)
{
	unsigned long retval = 0x0F0F0F0FU;

	WRITE_OR_EXIT(app_process_data->fd_rmm_to_app_process,
		shared_page, GRANULE_SIZE);
	WRITE_OR_EXIT(app_process_data->fd_rmm_to_app_process,
		&(app_data->heap_size), sizeof(app_data->heap_size));
	if (app_data->heap_size > 0) {
		WRITE_OR_EXIT(app_process_data->fd_rmm_to_app_process,
			app_data->app_heap, app_data->heap_size);
	}

	unsigned long reason;
	size_t app_heap_size;

	while (true) {
		READ_OR_EXIT(app_process_data->fd_app_process_to_rmm, &reason, sizeof(reason));
		if (reason == APP_EXIT_CALL) {
			READ_OR_EXIT(app_process_data->fd_app_process_to_rmm,
				&retval, sizeof(retval));
			app_data->exit_flag = (uint32_t)APP_EXIT_SVC_EXIT_FLAG;
			break;
		} else if (reason == APP_YIELD_CALL) {
			app_data->exit_flag = (uint32_t)APP_EXIT_SVC_YIELD_FLAG;
			break;
		} else if (reason == APP_SERVICE_CALL) {

			unsigned long service_index;
			unsigned long arg0;
			unsigned long arg1;
			unsigned long arg2;
			unsigned long arg3;

			READ_OR_EXIT(app_process_data->fd_app_process_to_rmm, &service_index,
				sizeof(service_index));
			READ_OR_EXIT(app_process_data->fd_app_process_to_rmm, &arg0, sizeof(arg0));
			READ_OR_EXIT(app_process_data->fd_app_process_to_rmm, &arg1, sizeof(arg1));
			READ_OR_EXIT(app_process_data->fd_app_process_to_rmm, &arg2, sizeof(arg2));
			READ_OR_EXIT(app_process_data->fd_app_process_to_rmm, &arg3, sizeof(arg3));
			READ_OR_EXIT(app_process_data->fd_app_process_to_rmm,
				shared_page, GRANULE_SIZE);
			READ_OR_EXIT(app_process_data->fd_app_process_to_rmm,
				&app_heap_size, sizeof(app_heap_size));
			if (app_data->heap_size == 0) {
				app_data->app_heap = malloc(app_heap_size);
				app_data->heap_size = app_heap_size;
			} else {
				assert(app_data->heap_size == app_heap_size);
			}
			READ_OR_EXIT(app_process_data->fd_app_process_to_rmm,
				app_data->app_heap, app_heap_size);

			retval = call_app_service(service_index, app_data, arg0, arg1, arg2, arg3);

			unsigned long bytes_to_forward =
				sizeof(unsigned long) +
				sizeof(shared_page) +
				sizeof(unsigned long) +
				app_data->heap_size;

			const unsigned long command = RUN_APP_INSTANCE;

			WRITE_OR_EXIT(app_process_data->fd_rmm_to_app_process,
				&command, sizeof(command));
			WRITE_OR_EXIT(app_process_data->fd_rmm_to_app_process, &app_data->thread_id,
				sizeof(app_data->thread_id));
			WRITE_OR_EXIT(app_process_data->fd_rmm_to_app_process, &bytes_to_forward,
				sizeof(bytes_to_forward));

			WRITE_OR_EXIT(app_process_data->fd_rmm_to_app_process,
				&retval, sizeof(retval));
			WRITE_OR_EXIT(app_process_data->fd_rmm_to_app_process,
				shared_page, GRANULE_SIZE);
			WRITE_OR_EXIT(app_process_data->fd_rmm_to_app_process,
				&(app_data->heap_size), sizeof(app_data->heap_size));
			assert(app_data->heap_size > 0);
			WRITE_OR_EXIT(app_process_data->fd_rmm_to_app_process,
				app_data->app_heap, app_data->heap_size);

			continue;
		}

		ERROR("ERROR: Invalid exit reason %lu\n", reason);
		exit(1);

	}
	READ_OR_EXIT(app_process_data->fd_app_process_to_rmm, shared_page, GRANULE_SIZE);
	READ_OR_EXIT(app_process_data->fd_app_process_to_rmm,
		&app_heap_size, sizeof(app_heap_size));
	if (app_data->heap_size == 0) {
		app_data->app_heap = malloc(app_heap_size);
		app_data->heap_size = app_heap_size;
	} else {
		assert(app_data->heap_size == app_heap_size);
	}
	READ_OR_EXIT(app_process_data->fd_app_process_to_rmm, app_data->app_heap, app_heap_size);

	return retval;
}

unsigned long app_run(struct app_data_cfg *app_data,
		      unsigned long app_func_id,
		      unsigned long arg0,
		      unsigned long arg1,
		      unsigned long arg2,
		      unsigned long arg3)
{
	struct app_process_data *app_process_data;

	app_process_data = get_app_process_data(app_data->app_id);
	if (app_process_data == NULL) {
		exit(1);
	}

	/* This function should not be called if the EL0 app was yielded */
	assert(app_data->exit_flag != APP_EXIT_SVC_YIELD_FLAG);

	const unsigned long command = RUN_APP_INSTANCE;

	WRITE_OR_EXIT(app_process_data->fd_rmm_to_app_process, &command, sizeof(command));
	WRITE_OR_EXIT(app_process_data->fd_rmm_to_app_process, &app_data->thread_id,
		sizeof(app_data->thread_id));

	unsigned long bytes_to_forward =
		5 * sizeof(unsigned long) +
		sizeof(shared_page) +
		sizeof(unsigned long) +
		app_data->heap_size;

	WRITE_OR_EXIT(app_process_data->fd_rmm_to_app_process, &bytes_to_forward,
		sizeof(bytes_to_forward));
	WRITE_OR_EXIT(app_process_data->fd_rmm_to_app_process, &app_func_id, sizeof(app_func_id));
	WRITE_OR_EXIT(app_process_data->fd_rmm_to_app_process, &arg0, sizeof(arg0));
	WRITE_OR_EXIT(app_process_data->fd_rmm_to_app_process, &arg1, sizeof(arg1));
	WRITE_OR_EXIT(app_process_data->fd_rmm_to_app_process, &arg2, sizeof(arg2));
	WRITE_OR_EXIT(app_process_data->fd_rmm_to_app_process, &arg3, sizeof(arg3));

	return app_run_internal(app_data, app_process_data);
}

unsigned long app_resume(struct app_data_cfg *app_data)
{
	struct app_process_data *app_process_data;

	app_process_data = get_app_process_data(app_data->app_id);
	if (app_process_data == NULL) {
		exit(1);
	}

	/* This function should only be called if the EL0 app was yielded */
	assert(app_data->exit_flag == APP_EXIT_SVC_YIELD_FLAG);

	const unsigned long command = RUN_APP_INSTANCE;

	WRITE_OR_EXIT(app_process_data->fd_rmm_to_app_process, &command, sizeof(command));
	WRITE_OR_EXIT(app_process_data->fd_rmm_to_app_process, &app_data->thread_id,
		sizeof(app_data->thread_id));

	unsigned long bytes_to_forward =
		sizeof(shared_page) +
		sizeof(unsigned long) +
		app_data->heap_size;

	WRITE_OR_EXIT(app_process_data->fd_rmm_to_app_process, &bytes_to_forward,
		sizeof(bytes_to_forward));

	return app_run_internal(app_data, app_process_data);
}

void app_abort(struct app_data_cfg *app_data)
{
	(void)app_data;

	/* TODO: Add implementation */
	assert(false);
}

void *app_get_heap_ptr(struct app_data_cfg *app_data)
{
	return app_data->app_heap;
}

size_t app_get_required_granule_count(unsigned long app_id)
{
	(void)app_id;
	return 0U;
}

/* Used by the Mbed TLS library in case EL3 token signing is active when
 * emulating EL3 signing.
 */
int32_t mbedtls_psa_external_get_random(
	void *context,
	uint8_t *output, size_t output_size, size_t *output_length)
{
	size_t i;

	(void)context;

	for (i = 0; i < output_size; ++i) {
		/* Using pseudo-random generation as mbedtls library might
		 * return with error if not enough entropy.
		 */
		output[i] = (uint8_t)(unsigned int)rand();
	}

	*output_length = output_size;

	return 0;
}
