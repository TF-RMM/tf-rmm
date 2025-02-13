/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <app.h>
#include <app_common.h>
#include <app_services.h>
#include <assert.h>
#include <console.h>

typedef uint64_t (*app_service_func)(struct app_data_cfg *app_data,
			  unsigned long arg0,
			  unsigned long arg1,
			  unsigned long arg2,
			  unsigned long arg3);

static uint64_t app_service_print(struct app_data_cfg *app_data,
			  unsigned long arg0,
			  unsigned long arg1,
			  unsigned long arg2,
			  unsigned long arg3)
{
	size_t len = arg0;
	size_t i;
	size_t offset = 0;
	char print_buf[4];

	(void)arg1;
	(void)arg2;
	(void)arg3;

	while (len > 0U) {
		char *shared_page;
		size_t to_print = len;

		if (to_print > sizeof(print_buf)) {
			to_print = sizeof(print_buf);
		}
		shared_page = app_data->el2_shared_page;
		assert(shared_page != NULL);
		(void)memcpy(print_buf, &shared_page[offset], to_print);
		for (i = 0; i < to_print; ++i) {
			(void)console_putc((int)print_buf[i]);
		}
		offset += to_print;
		len -= to_print;
	}
	return 0;
}

static app_service_func service_functions[APP_SERVICE_COUNT] = {
	[APP_SERVICE_PRINT] = app_service_print};

uint64_t call_app_service(unsigned long service_id,
			  struct app_data_cfg *app_data,
			  unsigned long arg0,
			  unsigned long arg1,
			  unsigned long arg2,
			  unsigned long arg3)
{
	(void)arg0;
	(void)arg1;
	(void)arg2;
	(void)arg3;

	assert(service_id < APP_SERVICE_COUNT);
	assert(service_functions[service_id] != NULL);

	return service_functions[service_id](app_data, arg0, arg1, arg2, arg3);
}

