/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <random_app.h>


int random_app_prng_get_random(struct app_data_cfg *app_data, uint8_t *buf, size_t output_size)
{
	(void)app_data;
	(void)buf;
	(void)output_size;
	return 0;
}

void random_app_init_prng(void)
{
}

struct app_data_cfg *random_app_get_data_cfg(void)
{
	return NULL;
}

