/*
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <app.h>
#include <app_header.h>
#include <assert.h>
#include <debug.h>
#include <errno.h>
#include <stddef.h>

static struct app_header app_headers[APP_COUNT];

void app_info_setup(void)
{
}

uint64_t app_get_rmm_start(void)
{
	return 0UL;
}

int app_get_index(unsigned long app_id, size_t *app_index)
{
	size_t i;

	for (i = 0; i < APP_COUNT; ++i) {
		if (app_headers[i].app_id == app_id) {
			*app_index = i;
			return 0;
		}
	}
	ERROR("Failed to get index of app id %lu\n", app_id);
	return -EINVAL;
}

int app_get_header_ptr_at_index(unsigned long app_index, struct app_header **app_header)
{
	if (app_index >= APP_COUNT) {
		return -EINVAL;
	}
	*app_header = &app_headers[app_index];
	return 0;
}

int app_get_header_ptr(unsigned long app_id, struct app_header **app_header)
{

	size_t app_index = 0;

	if (app_get_index(app_id, &app_index) != 0) {
		return -EINVAL;
	}

	*app_header = &app_headers[app_index];

	return 0;
}

size_t app_get_required_granule_count_from_header(struct app_header *app_header)
{
	(void)app_header;
	/* Require at least 1 granule to satisfy sanity checks in PDEV create */
	return 1U;
}
