/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <app_common.h>
#include <assert.h>
#include <attest_app.h>
#include <attest_defs.h>
#include <cpuid.h>
#include <debug.h>
#include <errno.h>
#include <simd.h>

/*
 * The number of pages that is allocated in the .bss for each per-cpu attest app
 * instance. This number must be at least the the number of per-instance pages
 * necessary for initiate an attestation app.
 */
#define ATTESTATION_APP_PAGE_COUNT 8U

/*
 * This array will hold the pages for the instance specific memory for all the
 * per-cpu instances of the attestation app. These instances are used for
 * measurement related operations when Aux granule is not available.
 */
static unsigned char rmm_attest_app_pages
	[MAX_CPUS][ATTESTATION_APP_PAGE_COUNT][GRANULE_SIZE] __aligned(GRANULE_SIZE) = {0};
/* The app config data for the per-cpu instances */
static struct app_data_cfg rmm_attest_app_datas[MAX_CPUS] __aligned(GRANULE_SIZE) = {0};
static bool attest_app_init_done[MAX_CPUS];

static unsigned long init_attest_app(struct app_data_cfg *app_data)
{
	assert(SIMD_IS_FPU_ALLOWED());

	return app_run(app_data, ATTESTATION_APP_FUNC_ID_INIT, 0, 0, 0, 0);
}

int attest_app_init(
	struct app_data_cfg *app_data,
	uintptr_t granule_pas[],
	size_t granule_pa_count)
{
	int ret = 0;

	ret = init_app_data(app_data,
				ATTESTATION_APP_ID,
				granule_pas,
				granule_pa_count);
	if (ret != 0) {
		return ret;
	}

	return init_attest_app(app_data);
}

/* Forward declare function to prevent static checker warning */
void attest_app_get_bss(uintptr_t *bss_pa, size_t *bss_size);

void attest_app_get_bss(uintptr_t *bss_pa, size_t *bss_size)
{
	static char attest_app_bss[2U * GRANULE_SIZE] __aligned(GRANULE_SIZE);
	*bss_pa = (uintptr_t)attest_app_bss;
	*bss_size = sizeof(attest_app_bss);
}

void init_rmm_app_helpers_applications(void)
{
	unsigned int cpuid;

	assert(!attest_app_init_done);
	/* Initialise the attestation applications for all the CPUs */
	for (cpuid = 0; cpuid < MAX_CPUS; ++cpuid) {
		int ret;
		uintptr_t granule_pas[ATTESTATION_APP_PAGE_COUNT];

		for (size_t i = 0; i < ATTESTATION_APP_PAGE_COUNT; ++i) {
			granule_pas[i] = (uintptr_t)&rmm_attest_app_pages[cpuid][i][0];
		}

		ret = attest_app_init(&rmm_attest_app_datas[cpuid],
				granule_pas,
				ATTESTATION_APP_PAGE_COUNT);
		if (ret != 0) {
			panic();
		}
	}
	attest_app_init_done = true;
}

void attest_do_hash(unsigned int algorithm,
		    void *data,
		    size_t size,
		    unsigned char *out)
{
	size_t hash_size;
	struct app_data_cfg *app_data;

	if (size > GRANULE_SIZE) {
		panic();
	}

	assert(attest_app_init_done[my_cpuid()]);
	app_data = &rmm_attest_app_datas[my_cpuid()];

	app_map_shared_page(app_data);
	(void)memcpy(app_data->el2_shared_page, data, size);

	SIMD_FPU_ALLOW(
		hash_size = app_run(app_data,
			ATTESTATION_APP_FUNC_ID_DO_HASH,
			algorithm, size, 0, 0));

	(void)memcpy((void *)out, app_data->el2_shared_page, hash_size);
	app_unmap_shared_page(app_data);
}


void attest_do_extend(struct app_data_cfg *app_data,
		      enum hash_algo algorithm,
		      void *current_measurement,
		      void *extend_measurement,
		      size_t extend_measurement_size,
		      unsigned char *out,
		      size_t out_size)
{
	size_t hash_size;
	struct attest_extend_measurement_buffers *shared_page;
	struct attest_extend_measurement_return_buffer *shared_page_ret;

	(void)out_size;

	if (app_data == NULL) {
		assert(attest_app_init_done[my_cpuid()]);
		app_data = &rmm_attest_app_datas[my_cpuid()];
	}

	app_map_shared_page(app_data);
	shared_page = app_data->el2_shared_page;
	shared_page->current_measurement_buf_offset = 0;
	shared_page->current_measurement_buf_size = MAX_MEASUREMENT_SIZE;
	(void)memcpy((void *)&(shared_page->buf[shared_page->current_measurement_buf_offset]),
	       current_measurement,
	       shared_page->current_measurement_buf_size);
	shared_page->extend_measurement_buf_offset = MAX_MEASUREMENT_SIZE;
	shared_page->extend_measurement_buf_size = MAX_MEASUREMENT_SIZE;
	(void)memcpy((void *)&(shared_page->buf[shared_page->extend_measurement_buf_offset]),
	       extend_measurement,
	       shared_page->extend_measurement_buf_size);

	SIMD_FPU_ALLOW(
		hash_size = app_run(app_data,
				ATTESTATION_APP_FUNC_ID_EXTEND_MEASUREMENT,
				(unsigned long)algorithm,
				extend_measurement_size, 0, 0));

	shared_page_ret = (struct attest_extend_measurement_return_buffer *)
		app_data->el2_shared_page;
	assert(hash_size == shared_page_ret->measurement_size);
	assert(hash_size <= out_size);
	(void)memcpy(out, &(shared_page_ret->measurement_buf), hash_size);
	app_unmap_shared_page(app_data);
}
