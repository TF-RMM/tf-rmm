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
#include <limits.h>
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

static unsigned long global_init_attest_app(struct app_data_cfg *app_data)
{
	unsigned long ret;

	app_map_shared_page(app_data);
	SIMD_FPU_ALLOW(
		ret = app_run(app_data, ATTESTATION_APP_FUNC_ID_GLOBAL_INIT, 0, 0, 0, 0));
	assert(app_data->exit_flag != APP_EXIT_SVC_YIELD_FLAG);
	app_unmap_shared_page(app_data);
	return ret;
}

int attest_app_init(
	struct app_data_cfg *app_data,
	uintptr_t granule_pas[],
	size_t granule_pa_count,
	void *granule_va_start)
{
	return app_init_data(app_data,
				ATTESTATION_APP_ID,
				granule_pas,
				granule_pa_count,
				granule_va_start);
}

int attest_app_global_init(void)
{
	struct app_data_cfg app_data;
	uintptr_t granule_pas[ATTESTATION_APP_PAGE_COUNT];
	int ret = 0;
	unsigned long uret = 0;
	unsigned int cpuid = my_cpuid();

	/*
	 * Reuse the pages that were allocated for the per-cpu instances.
	 * This function is run before any other instance is run, so this is
	 * safe.
	 */
	for (unsigned int i = 0 ; i < ATTESTATION_APP_PAGE_COUNT; ++i) {
		granule_pas[i] = (uintptr_t)rmm_attest_app_pages[cpuid][i];
	}

	ret = app_init_data(&app_data,
				ATTESTATION_APP_ID,
				granule_pas,
				ARRAY_SIZE(granule_pas),
				rmm_attest_app_pages[cpuid][0]);
	if (ret != 0) {
		return ret;
	}

	uret = global_init_attest_app(&app_data);

	/* Restore the per-cpu instance pages to the state they were */
	(void)memset((void *)&(rmm_attest_app_pages[cpuid][0]), 0,
		ATTESTATION_APP_PAGE_COUNT * GRANULE_SIZE);

	if (uret > (unsigned long)INT_MAX) {
		return -EINVAL;
	} else {
		return (int)uret;
	}

}

/* Forward declare function to prevent static checker warning */
void attest_app_get_bss(uintptr_t *bss_pa, size_t *bss_size);

void attest_app_get_bss(uintptr_t *bss_pa, size_t *bss_size)
{
	static char attest_app_bss[3U * GRANULE_SIZE] __aligned(GRANULE_SIZE);
	*bss_pa = (uintptr_t)attest_app_bss;
	*bss_size = sizeof(attest_app_bss);
}

void attest_app_init_per_cpu_instance(void)
{
	unsigned int cpuid = my_cpuid();

	/* Only need to be initialised during coldboot */
	if (attest_app_init_done[cpuid]) {
		return;
	}

	/* Initialise the attestation applications for this CPU */
	int ret;
	uintptr_t granule_pas[ATTESTATION_APP_PAGE_COUNT];

	for (size_t i = 0; i < ATTESTATION_APP_PAGE_COUNT; ++i) {
		granule_pas[i] = (uintptr_t)&rmm_attest_app_pages[cpuid][i][0];
	}

	ret = attest_app_init(&rmm_attest_app_datas[cpuid],
			granule_pas,
			ATTESTATION_APP_PAGE_COUNT,
			&rmm_attest_app_pages[cpuid][0][0]);
	if (ret != 0) {
		panic();
	}
	attest_app_init_done[cpuid] = true;
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
	assert(app_data->el2_shared_page != NULL);
	(void)memcpy(app_data->el2_shared_page, data, size);

	SIMD_FPU_ALLOW(
		hash_size = app_run(app_data,
			ATTESTATION_APP_FUNC_ID_DO_HASH,
			algorithm, size, 0, 0));
	assert(app_data->exit_flag != APP_EXIT_SVC_YIELD_FLAG);
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
	assert(app_data->el2_shared_page != NULL);
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
	assert(app_data->exit_flag != APP_EXIT_SVC_YIELD_FLAG);
	shared_page_ret = (struct attest_extend_measurement_return_buffer *)
		app_data->el2_shared_page;
	assert(hash_size == shared_page_ret->measurement_size);
	assert(hash_size <= out_size);
	(void)memcpy(out, &(shared_page_ret->measurement_buf), hash_size);
	app_unmap_shared_page(app_data);
}

enum attest_token_err_t attest_realm_token_sign(
			struct app_data_cfg *app_data,
			size_t *realm_token_len)
{
	unsigned long retval;

	app_map_shared_page(app_data);
	SIMD_FPU_ALLOW(
		retval = app_run(app_data,
			    ATTESTATION_APP_FUNC_ID_TOKEN_SIGN,
			    0, 0, 0, 0));
	assert(app_data->exit_flag != APP_EXIT_SVC_YIELD_FLAG);
	assert(app_data->el2_shared_page != NULL);
	*realm_token_len = *(size_t *)app_data->el2_shared_page;
	app_unmap_shared_page(app_data);
	return (enum attest_token_err_t)retval;
}

enum attest_token_err_t attest_cca_token_create(
				struct app_data_cfg *app_data,
				size_t *attest_token_len)
{
	/* Call the actual token creation */
	unsigned long ret;

	app_map_shared_page(app_data);
	SIMD_FPU_ALLOW(
		ret = app_run(app_data,
			ATTESTATION_APP_FUNC_ID_DO_CCA_TOKEN_CREATION,
			0, 0, 0, 0));

	assert(app_data->exit_flag != APP_EXIT_SVC_YIELD_FLAG);
	if (ret != (unsigned long)ATTEST_TOKEN_ERR_SUCCESS) {
		app_unmap_shared_page(app_data);
		return (enum attest_token_err_t)ret;
	}

	assert(app_data->el2_shared_page != NULL);
	*attest_token_len = *(size_t *)app_data->el2_shared_page;
	app_unmap_shared_page(app_data);
	return (enum attest_token_err_t)ret;
}

enum attest_token_err_t attest_token_sign_ctx_init(struct app_data_cfg *app_data, uintptr_t cookie)
{
	enum attest_token_err_t ret;

	ret = (enum attest_token_err_t)app_run(app_data,
		ATTESTATION_APP_FUNC_ID_TOKEN_CTX_INIT,
			cookie, 0, 0, 0);
	assert(app_data->exit_flag != APP_EXIT_SVC_YIELD_FLAG);
	return ret;
}

enum attest_token_err_t attest_realm_token_create(struct app_data_cfg *app_data,
			     enum hash_algo algorithm,
			     unsigned char measurements[][MAX_MEASUREMENT_SIZE],
			     bool is_pvt_mecid,
			     const void *rpv_buf,
			     const void *challenge_buf)
{
	struct attest_realm_token_create_params *shared_page;
	enum attest_token_err_t ret;

	app_map_shared_page(app_data);
	assert(app_data->el2_shared_page != NULL);
	shared_page = app_data->el2_shared_page;
	(void)memcpy(&(shared_page->measurements),
	       measurements,
	       (size_t)(MEASUREMENT_SLOT_NR * MAX_MEASUREMENT_SIZE));
	(void)memcpy((void *)&(shared_page->rpv),
	       rpv_buf,
	       RPV_SIZE);
	(void)memcpy((void *)&(shared_page->challenge),
	       challenge_buf,
	       ATTEST_CHALLENGE_SIZE);
	shared_page->is_pvt_mecid = is_pvt_mecid;
	ret = (enum attest_token_err_t)app_run(app_data,
		ATTESTATION_APP_FUNC_ID_REALM_TOKEN_CREATE,
			(unsigned long)algorithm, 0, 0, 0);
	assert(app_data->exit_flag != APP_EXIT_SVC_YIELD_FLAG);
	app_unmap_shared_page(app_data);
	return ret;
}

#if ATTEST_EL3_TOKEN_SIGN
int attest_app_el3_token_write_response_to_ctx(struct app_data_cfg *app_data,
					       uint64_t req_ticket,
					       size_t signature_buf_len,
					       uint8_t signature_buf[])
{
	unsigned long ret;

	app_map_shared_page(app_data);
	assert(signature_buf_len <= GRANULE_SIZE);
	memcpy(app_data->el2_shared_page, signature_buf, signature_buf_len);
	SIMD_FPU_ALLOW(
		ret = app_run(app_data,
			EL3_TOKEN_WRITE_RESPONSE_TO_CTX,
			req_ticket, signature_buf_len, 0, 0));
	assert(app_data->exit_flag != APP_EXIT_SVC_YIELD_FLAG);
	app_unmap_shared_page(app_data);
	return ret;
}
#endif
