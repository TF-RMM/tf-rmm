/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <app.h>
#include <app_common.h>
#include <app_services.h>
#include <assert.h>
#include <attest_services.h>
#include <console.h>
#include <errno.h>
#include <random_app.h>
#include <rmm_el3_ifc.h>

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
	char *shared_page;

	(void)arg1;
	(void)arg2;
	(void)arg3;

	if (len >= GRANULE_SIZE) {
		return (uint64_t)(-EINVAL);
	}

	shared_page = app_data->el2_shared_page;
	for (i = 0U; i < len; ++i) {
		(void)console_putc((int)shared_page[i]);
	}
	return 0;
}

static uint64_t app_service_get_random(struct app_data_cfg *app_data,
			  unsigned long arg0,
			  unsigned long arg1,
			  unsigned long arg2,
			  unsigned long arg3)
{
	size_t len = arg0;
	uint8_t buf[GRANULE_SIZE];
	int ret;
	void *shared_page;

	(void)arg1;
	(void)arg2;
	(void)arg3;

	if (len >= GRANULE_SIZE) {
		return (uint64_t)(-EINVAL);
	}

	/* TODO: The random app generates the random values to the shared memory between
	 * RMM and random app. that gets copied to buf. That's gets copied to the shared
	 * memory between RMM and calling app. This should be optimised.
	 */

	struct app_data_cfg *random_app_data = random_app_get_data_cfg();

	ret = random_app_prng_get_random(random_app_data, buf, len);
	if (ret != 0) {
		return (uint64_t)ret;
	}

	shared_page = app_data->el2_shared_page;
	assert(shared_page != NULL);
	/* coverity[misra_c_2012_rule_9_1_violation:SUPPRESS] */
	(void)memcpy(shared_page, (void *)buf, len);
	return 0;
}

static uint64_t app_service_get_realm_attestation_key(struct app_data_cfg *app_data,
			  unsigned long arg0,
			  unsigned long arg1,
			  unsigned long arg2,
			  unsigned long arg3)
{
	uintptr_t buf;
	size_t attest_key_size;
	struct service_get_realm_attestation_key_struct *shared_page;

	(void)arg0;
	(void)arg1;
	(void)arg2;
	(void)arg3;

	/*
	 * Get the realm attestation key. The key is retrieved in raw format.
	 */
	buf = rmm_el3_ifc_get_shared_buf_locked();

	if (rmm_el3_ifc_get_realm_attest_key(buf,
				rmm_el3_ifc_get_shared_buf_size(),
				&attest_key_size,
				ATTEST_KEY_CURVE_ECC_SECP384R1) != 0) {
		rmm_el3_ifc_release_shared_buf();
		return (uint64_t)(-EINVAL);
	}

	if (attest_key_size >= APP_MAX_ATTEST_KEY_SIZE) {
		return (uint64_t)(-EINVAL);
	}

	shared_page = app_data->el2_shared_page;
	assert(shared_page != NULL);
	shared_page->attest_key_buf_size = attest_key_size;
	(void)memcpy((void *)shared_page->attest_key_buf,
		     (void *)buf, shared_page->attest_key_buf_size);

	/* Clear the private key from the buffer */
	(void)memset((uint8_t *)buf, 0, attest_key_size);

	rmm_el3_ifc_release_shared_buf();

	return 0;
}

static uint64_t app_service_get_platform_token(struct app_data_cfg *app_data,
			  unsigned long arg0,
			  unsigned long arg1,
			  unsigned long arg2,
			  unsigned long arg3)
{
	size_t current_hunk_len = 0;
	size_t bytes_remaining = 0;
	size_t hash_size = arg0;
	int ret;
	uintptr_t shared_buf;
	void *shared_page_void;
	struct service_get_platform_token_struct *shared_page_get_plat_token;

	size_t service_token_buf_len = sizeof(shared_page_get_plat_token->token_hunk_buf);

	(void)arg1;
	(void)arg2;
	(void)arg3;

	if (hash_size >= GRANULE_SIZE) {
		return (uint64_t)(-EINVAL);
	}

	shared_buf = rmm_el3_ifc_get_shared_buf_locked();

	shared_page_void = app_data->el2_shared_page;
	assert(shared_page_void != NULL);
	(void)memcpy((void *)shared_buf, shared_page_void, hash_size);

	do {
		ret = rmm_el3_ifc_get_platform_token(
			shared_buf,
			service_token_buf_len,
			hash_size,
			&current_hunk_len,
			&bytes_remaining);
	} while (ret == E_RMM_AGAIN);

	if (ret != E_RMM_OK) {
		assert(ret != 0);
		rmm_el3_ifc_release_shared_buf();
		return (uint64_t)ret;
	}

	shared_page_get_plat_token = app_data->el2_shared_page;
	assert(shared_page_get_plat_token != NULL);
	assert(current_hunk_len <= GRANULE_SIZE);
	assert(current_hunk_len <= sizeof(shared_page_get_plat_token->token_hunk_buf));
	/* coverity[misra_c_2012_rule_21_18_violation:SUPPRESS] */
	(void)memcpy((void *)shared_page_get_plat_token->token_hunk_buf, (void *)shared_buf, current_hunk_len);
	rmm_el3_ifc_release_shared_buf();

	shared_page_get_plat_token->token_hunk_len = current_hunk_len;
	shared_page_get_plat_token->remaining_len = bytes_remaining;

	return 0;
}

#if ATTEST_EL3_TOKEN_SIGN
static uint64_t app_service_get_realm_attest_pub_key_from_el3(struct app_data_cfg *app_data,
			  unsigned long arg0,
			  unsigned long arg1,
			  unsigned long arg2,
			  unsigned long arg3)
{
	uintptr_t buf;
	size_t attest_key_size;
	struct service_get_realm_attestation_pub_key_struct *shared_page;

	(void)arg0;
	(void)arg1;
	(void)arg2;
	(void)arg3;

	/*
	 * Get the realm attestation key. The key is retrieved in raw format.
	 */
	buf = rmm_el3_ifc_get_shared_buf_locked();

	/* When EL3 service is used for attestation, EL3 returns public key in raw format */
	if (rmm_el3_ifc_get_realm_attest_pub_key_from_el3(buf,
			rmm_el3_ifc_get_shared_buf_size(),
			&attest_key_size,
			ATTEST_KEY_CURVE_ECC_SECP384R1) != 0) {
		rmm_el3_ifc_release_shared_buf();
		return -EINVAL;
	}

	shared_page = app_data->el2_shared_page;
	assert(attest_key_size <= sizeof(shared_page->attest_pub_key_buf));
	shared_page->attest_pub_key_buf_size = attest_key_size;
	memcpy((void *)&(shared_page->attest_pub_key_buf), (const void *)buf, attest_key_size);
	rmm_el3_ifc_release_shared_buf();
	return 0;
}

static uint64_t app_service_el3_token_sign_queue_try_enqueue(struct app_data_cfg *app_data,
			  unsigned long arg0,
			  unsigned long arg1,
			  unsigned long arg2,
			  unsigned long arg3)
{
	uint64_t ret;
	struct service_el3_token_sign_request *request = app_data->el2_shared_page;

	(void)arg0;
	(void)arg1;
	(void)arg2;
	(void)arg3;

	ret = el3_token_sign_queue_try_enqueue(request);
	return ret;
}

static uint64_t app_service_el3_ifc_el3_token_sign_supported(struct app_data_cfg *app_data,
			  unsigned long arg0,
			  unsigned long arg1,
			  unsigned long arg2,
			  unsigned long arg3)
{
	(void)app_data;
	(void)arg0;
	(void)arg1;
	(void)arg2;
	(void)arg3;

	return rmm_el3_ifc_el3_token_sign_supported();
}
#endif

static app_service_func service_functions[APP_SERVICE_COUNT] = {
	[APP_SERVICE_PRINT] = app_service_print,
	[APP_SERVICE_RANDOM] = app_service_get_random,
	[APP_SERVICE_GET_REALM_ATTESTATION_KEY] = app_service_get_realm_attestation_key,
	[APP_SERVICE_GET_PLATFORM_TOKEN] = app_service_get_platform_token,
#if ATTEST_EL3_TOKEN_SIGN
	[APP_SERVICE_GET_REALM_ATTEST_PUB_KEY_FROM_EL3] = app_service_get_realm_attest_pub_key_from_el3,
	[APP_SERVICE_EL3_TOKEN_SIGN_QUEUE_TRY_ENQUEUE] = app_service_el3_token_sign_queue_try_enqueue,
	[APP_SERVICE_EL3_IFC_EL3_TOKEN_SIGN_SUPPORTED] = app_service_el3_ifc_el3_token_sign_supported,
#endif /* ATTEST_EL3_TOKEN_SIGN */
	};

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

