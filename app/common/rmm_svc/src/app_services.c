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
	int ret;
	bool unmap_shared_page = false;

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

	if (app_data->el2_shared_page == NULL) {
		app_map_shared_page(app_data);
		unmap_shared_page = true;
	}

	/* Pass the caller app's shared page as buf to the random app stub. */
	assert(app_data->el2_shared_page != NULL);
	ret = random_app_prng_get_random(random_app_data, app_data->el2_shared_page, len);
	if (ret != 0) {
		return (uint64_t)ret;
	}

	if (unmap_shared_page) {
		app_unmap_shared_page(app_data);
	}

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
	unsigned long buf_len,
	bool force_alignment)
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
	    ((app_buf_size - app_buf_offset) < buf_len)) {
		ERROR("%s called with invalid buf offset 0x%lx or len 0x%lx\n",
				__func__, app_buf_offset, buf_len);
		return rw_data;
	}

	if (force_alignment) {
		if ((!ALIGNED(buf_len, 8U)) ||
		    (!ALIGNED(app_buf_offset, 8U))) {
			ERROR("%s called with unaligned buf offset 0x%lx or len 0x%lx\n",
					__func__, app_buf_offset, buf_len);
			return rw_data;
		}
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

	/* Find the ns_granule and populate it in rw_data */
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
 *	arg1 - App Buffer offset.
 *	arg2 - NS buf physical address (must be 8 byte aligned)
 *	arg3 - Length to write
 *
 * The App buffer offset + Length must be either less that PAGE_SIZE or heap_size,
 * depending on App Buffer identifier. This is a sanity check to ensure that
 * buffer is in App VA space. Similarly the NS Address write must be within the
 * page. It is assumed that app buffer is already mapped in RMM S1 MMU.
 * The aligned offset is returned back to the caller in the shared page.
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
	size_t gr_offset;
	size_t *shared_page;
	struct ns_rw_data rw_data = validate_and_get_ns_rw_data(app_data, app_buf_id,
		app_buf_offset, ns_addr, buf_len, false);

	if (rw_data.ns_granule == NULL) {
		return (uint64_t)(-EINVAL);
	}

	ns_access_ok = ns_buffer_write_unaligned(SLOT_NS, rw_data.ns_granule, 0, buf_len,
		(void *)rw_data.app_buf, &gr_offset);
	if (!ns_access_ok) {
		ERROR("%s ns buffer read failed for ns addr 0x%lx and app_buf 0x%lx\n",
				__func__, ns_addr, rw_data.app_buf);
		return (uint64_t)(-EINVAL);
	}
	shared_page = (size_t *)app_data->el2_shared_page;
	assert(shared_page != NULL);
	/* coverity[misra_c_2012_rule_9_1_violation:SUPPRESS] */
	*shared_page = gr_offset;

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
static uint64_t app_service_read_from_ns_buf_aligned(struct app_data_cfg *app_data,
	unsigned long app_buf_id,
	unsigned long app_buf_offset,
	unsigned long ns_addr,
	unsigned long buf_len)
{
	bool ns_access_ok;
	struct ns_rw_data rw_data = validate_and_get_ns_rw_data(app_data, app_buf_id,
		app_buf_offset, ns_addr, buf_len, true);

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

static uint64_t app_service_rp_ide_key_program(struct app_data_cfg *app_data,
				      unsigned long kslot,
				      unsigned long is_rx,
				      unsigned long sub_stream,
				      unsigned long arg3)
{
	unsigned long stream_info;
	struct service_rp_ide_op_struct *params;
	struct el3_ifc_rp_ide_iv iv;
	uint32_t retry = 0;
	int rc;

	(void)arg3;

	assert(app_data->el2_shared_page != NULL);
	params = (struct service_rp_ide_op_struct *)app_data->el2_shared_page;

	/* pci_ide_km_aes_256_gcm_key_buffer_t uses 8 bytes for IV */
	iv.iq_w0 = (unsigned long)params->iv[0] |
		  ((unsigned long)params->iv[1] << 32U);
	iv.iq_w1 = 0U;

	stream_info = EL3_IFC_IDE_MAKE_STREAM_INFO((uint8_t)kslot, ((is_rx != 0U) ? 1U : 0U),
						   (uint8_t)sub_stream, params->ide_sid);

	do {
		assert(sizeof(params->key) == sizeof(struct el3_ifc_rp_ide_key));
		rc = rmm_el3_ifc_rp_ide_key_prog(params->ecam_addr, params->rp_id,
						 stream_info,
						 (struct el3_ifc_rp_ide_key *)&params->key,
						 &iv);
		if (rc != E_RMM_AGAIN) {
			/* TODO: This could return to the app in case of
			 * E_RMM_AGAIN as well and then let the APP decide.
			 * This will naturally add some delay and also allow
			 * pre-emption/yield to NS in a natural way.
			 */
			return (uint64_t)rc;
		}

		/* todo: add DSM wait to exit to Host */

		/* TODO: Handle E_RMM_IN_PROGRESS error code */

		INFO("DSM_IDE: rp_ide_key_prog retry: %d\n", retry);
	} while (++retry < EL3_IFC_IDE_KM_RETRY_COUNT_MAX);

	return (uint64_t)rc;

}

static uint64_t app_service_rp_ide_key_set_go(struct app_data_cfg *app_data,
				      unsigned long kslot,
				      unsigned long is_rx,
				      unsigned long sub_stream,
				      unsigned long arg3)
{
	unsigned long stream_info;
	struct service_rp_ide_op_struct *params;
	uint32_t retry = 0;
	int rc;

	(void)arg3;

	assert(app_data->el2_shared_page != NULL);
	params = (struct service_rp_ide_op_struct *)app_data->el2_shared_page;

	stream_info = EL3_IFC_IDE_MAKE_STREAM_INFO((uint8_t)kslot, ((is_rx != 0U) ? 1U : 0U),
						   (uint8_t)sub_stream, params->ide_sid);

	do {
		rc = rmm_el3_ifc_rp_ide_key_set_go(params->ecam_addr, params->rp_id,
						   stream_info);
		if (rc != E_RMM_AGAIN) {
			return (uint64_t)rc;
		}

		/* todo: add DSM wait to exit to Host */

		/* TODO: Handle E_RMM_IN_PROGRESS error code */

		INFO("DSM_IDE: rp_ide_key_set_go retry: %d\n", retry);
	} while (++retry < EL3_IFC_IDE_KM_RETRY_COUNT_MAX);

	return (uint64_t)rc;
}

static uint64_t app_service_rp_ide_key_set_stop(struct app_data_cfg *app_data,
				      unsigned long kslot,
				      unsigned long is_rx,
				      unsigned long sub_stream,
				      unsigned long arg3)
{
	unsigned long stream_info;
	struct service_rp_ide_op_struct *params;
	uint32_t retry = 0;
	int rc;

	(void)arg3;

	assert(app_data->el2_shared_page != NULL);
	params = (struct service_rp_ide_op_struct *)app_data->el2_shared_page;

	stream_info = EL3_IFC_IDE_MAKE_STREAM_INFO((uint8_t)kslot, ((is_rx != 0U) ? 1U : 0U),
						   (uint8_t)sub_stream, params->ide_sid);

	do {
		rc = rmm_el3_ifc_rp_ide_key_set_stop(params->ecam_addr, params->rp_id,
						     stream_info);
		if (rc != E_RMM_AGAIN) {
			return (uint64_t)rc;
		}

		/* todo: add DSM wait to exit to Host */

		/* TODO: Handle E_RMM_IN_PROGRESS error code */

		INFO("DSM_IDE: rp_ide_key_set_go retry: %d\n", retry);
	} while (++retry < EL3_IFC_IDE_KM_RETRY_COUNT_MAX);

	return (uint64_t)rc;
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
	[APP_SERVICE_READ_FROM_NS_BUF_ALIGNED] = app_service_read_from_ns_buf_aligned,
	[APP_SERVICE_RP_IDE_KEY_PROGRAM] = app_service_rp_ide_key_program,
	[APP_SERVICE_RP_IDE_KEY_SET_GO] = app_service_rp_ide_key_set_go,
	[APP_SERVICE_RP_IDE_KEY_SET_STOP] = app_service_rp_ide_key_set_stop,
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

