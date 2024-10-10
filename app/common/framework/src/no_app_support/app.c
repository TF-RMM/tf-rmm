/*
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <app.h>
#include <app_header.h>
#include <app_services.h>
#include <assert.h>
#include <debug.h>
#include <errno.h>
#include <unistd.h>

void app_framework_setup(void)
{
}

int app_init_data(struct app_data_cfg *app_data,
		      unsigned long app_id,
		      uintptr_t granule_pas[],
		      size_t granule_count,
		      void *granule_va_start){
	(void)app_data;
	(void)app_id;
	(void)granule_pas;
	(void)granule_count;
	(void)granule_va_start;
	return 0;
}

unsigned long app_run(struct app_data_cfg *app_data,
		      unsigned long app_func_id,
		      unsigned long arg0,
		      unsigned long arg1,
		      unsigned long arg2,
		      unsigned long arg3)
{
	(void)app_data;
	(void)app_func_id;
	(void)arg0;
	(void)arg1;
	(void)arg2;
	(void)arg3;
	return 0;
}

void app_map_shared_page(struct app_data_cfg *app_data)
{
	(void)app_data;
}

void app_unmap_shared_page(struct app_data_cfg *app_data)
{
	(void)app_data;
}

/* Used by the Mbed TLS library in case EL3 token signing is active when
 * emulating EL3 signing.
 */
int32_t mbedtls_psa_external_get_random(
	void *context,
	uint8_t *output, size_t output_size, size_t *output_length)
{
	static uint8_t val;
	size_t i;

	(void)context;

	for (i = 0; i < output_size; ++i) {
		output[i] = val;
	}

	*output_length = output_size;

	return 0;
}

size_t app_get_required_granule_count(unsigned long app_id)
{
	(void)app_id;
	return 0U;
}
