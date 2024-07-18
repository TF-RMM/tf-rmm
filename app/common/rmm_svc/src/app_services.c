/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <app.h>
#include <app_common.h>
#include <app_services.h>
#include <assert.h>
#include <attest_services.h>
#include <buffer.h>
#include <console.h>
#include <debug.h>
#include <errno.h>
#include <random_app.h>
#include <rmm_el3_ifc.h>

typedef uint64_t (*app_service_func)(struct app_data_cfg *app_data,
			  unsigned long arg0,
			  unsigned long arg1,
			  unsigned long arg2,
			  unsigned long arg3);

struct ns_rw_data {
	uintptr_t app_buf;
	struct granule *ns_granule;
};

static uint64_t app_service_print(struct app_data_cfg *app_data,
			  unsigned long arg0,
			  unsigned long arg1,
			  unsigned long arg2,
			  unsigned long arg3)
{
	int character = (int)arg0;

	(void)app_data;
	(void)arg1;
	(void)arg2;
	(void)arg3;

	(void)console_putc(character);
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

static struct ns_rw_data validate_and_get_ns_rw_data(struct app_data_cfg *app_data,
	unsigned long app_buf_id,
	unsigned long app_buf_offset,
	unsigned long ns_addr,
	unsigned long buf_len)
{
	struct ns_rw_data rw_data = {0, NULL};
	uintptr_t app_buf = 0;

	if ((app_buf_id != APP_SERVICE_RW_NS_BUF_SHARED) &&
	    (app_buf_id != APP_SERVICE_RW_NS_BUF_HEAP)) {
		ERROR("%s called with invalid app_buf_id 0x%lx\n", __func__, app_buf_id);
		return rw_data;
	}

	/* Based on app_buf_id, work out the size of app buffer */
	unsigned long app_buf_size = (app_buf_id == APP_SERVICE_RW_NS_BUF_SHARED) ?
		GRANULE_SIZE : app_data->heap_size;

	if ((app_buf_offset > app_buf_size) ||
	    ((app_buf_size - app_buf_offset) < buf_len) ||
	    (!ALIGNED(buf_len, 8U)) ||
	    (!ALIGNED(app_buf_offset, 8U))) {
		ERROR("%s called with invalid buf offset 0x%lx or len 0x%lx\n",
				__func__, app_buf_offset, buf_len);
		return rw_data;
	}

	if (app_buf_id == APP_SERVICE_RW_NS_BUF_SHARED) {
		app_buf = (uintptr_t)app_data->el2_shared_page + app_buf_offset;
	} else {
		app_buf = (uintptr_t)app_get_heap_ptr(app_data) + app_buf_offset;
	}

	unsigned long ns_addr_offset = ns_addr & ~GRANULE_MASK;

	/* The data rw should not cross page boundary as only the single NS page
	 * is mapped.
	 */
	if (((ns_addr_offset + buf_len) > SZ_4K) || (!ALIGNED(ns_addr_offset, 8U))) {
		ERROR("%s called with invalid ns addr 0x%lx.\n",
				__func__, ns_addr);
		return rw_data;
	}

	/* Copy the data from NS buffer */
	rw_data.ns_granule = find_granule(ns_addr & GRANULE_MASK);
	if ((rw_data.ns_granule == NULL) ||
		(granule_unlocked_state(rw_data.ns_granule) != GRANULE_STATE_NS)) {
		ERROR("%s ns granule not found or invalid state for ns addr 0x%lx\n",
				__func__, ns_addr);
		return rw_data;
	}

	rw_data.app_buf = app_buf;
	return rw_data;
}

/*
 * Service to write to NS Address from app shared page or shared heap
 * with specified offset and length.
 *
 * Arguments:
 *	arg0 - App Buffer identifier (one of APP_SERVICE_RW_NS_BUF_*)
 *	arg1 - App Buffer offset (must be 8 byte aligned).
 *	arg2 - NS buf physical address (must be 8 byte aligned)
 *	arg3 - Length to write (must be 8 byte aligned)
 *
 * The App buffer offset + Length must be either less that PAGE_SIZE or heap_size,
 * depending on App Buffer identifier. This is a sanity check to ensure that
 * buffer is in App VA space. Similarly the NS Address write must be within the
 * page. It is assumed that app buffer is already mapped in RMM S1 MMU.
 *
 * Return:
 *	0	- Success
 *	-EINVAL	- Failure
 */
static uint64_t app_service_write_to_ns_buf(struct app_data_cfg *app_data,
	unsigned long app_buf_id,
	unsigned long app_buf_offset,
	unsigned long ns_addr,
	unsigned long buf_len)
{
	bool ns_access_ok;
	struct ns_rw_data rw_data = validate_and_get_ns_rw_data(app_data, app_buf_id,
		app_buf_offset, ns_addr, buf_len);

	if (rw_data.ns_granule == NULL) {
		return (uint64_t)(-EINVAL);
	}

	ns_access_ok = ns_buffer_write(SLOT_NS, rw_data.ns_granule, 0, buf_len,
		(void *)rw_data.app_buf);
	if (!ns_access_ok) {
		ERROR("%s ns buffer read failed for ns addr 0x%lx and app_buf 0x%lx\n",
				__func__, ns_addr, rw_data.app_buf);
		return (uint64_t)(-EINVAL);
	}

	return 0;
}

/*
 * Service to read from NS Address to app shared page or shared heap
 * with specified offset and length.
 *
 * Arguments:
 *	arg0 - App Buffer identifier (one of APP_SERVICE_RW_NS_BUF_*)
 *	arg1 - App Buffer offset (must be 8 byte aligned).
 *	arg2 - NS buf physical address (must be 8 byte aligned)
 *	arg3 - Length to read (must be 8 byte aligned)
 *
 * The App buffer offset + Length must be either less that PAGE_SIZE or heap_size,
 * depending on App Buffer identifier. This is a sanity check to ensure that
 * buffer is in App VA space. Similarly the NS Address read must be within the
 * page. It is assumed that app buffer is already mapped in RMM S1 MMU.
 *
 * Return:
 *	0	- Success
 *	-EINVAL	- Failure
 */
static uint64_t app_service_read_from_ns_buf(struct app_data_cfg *app_data,
	unsigned long app_buf_id,
	unsigned long app_buf_offset,
	unsigned long ns_addr,
	unsigned long buf_len)
{
	bool ns_access_ok;
	struct ns_rw_data rw_data = validate_and_get_ns_rw_data(app_data, app_buf_id,
		app_buf_offset, ns_addr, buf_len);

	if (rw_data.ns_granule == NULL) {
		return (uint64_t)(-EINVAL);
	}

	ns_access_ok = ns_buffer_read(SLOT_NS, rw_data.ns_granule, 0, buf_len,
		(void *)rw_data.app_buf);
	if (!ns_access_ok) {
		ERROR("%s ns buffer read failed for ns addr 0x%lx and app_buf 0x%lx\n",
				__func__, ns_addr, rw_data.app_buf);
		return (uint64_t)(-EINVAL);
	}

	return 0;
}

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
	[APP_SERVICE_WRITE_TO_NS_BUF] = app_service_write_to_ns_buf,
	[APP_SERVICE_READ_FROM_NS_BUF] = app_service_read_from_ns_buf,
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

