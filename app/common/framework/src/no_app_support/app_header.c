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

void app_info_setup(void)
{
}

uint64_t app_get_rmm_start(void)
{
	return 0UL;
}

int app_get_index(unsigned long app_id, size_t *app_index)
{
	(void)app_id;
	(void)app_index;
	return -EINVAL;
}

int app_get_header_ptr_at_index(unsigned long app_index, struct app_header **app_header)
{
	(void)app_index;
	(void)app_header;
	return -EINVAL;
}

int app_get_header_ptr(unsigned long app_id, struct app_header **app_header)
{
	(void)app_id;
	(void)app_header;
	return -EINVAL;
}

size_t app_get_required_granule_count_from_header(struct app_header *app_header)
{
	(void)app_header;
	return 0;
}
