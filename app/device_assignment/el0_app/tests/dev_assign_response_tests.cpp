/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <CppUTest/CommandLineTestRunner.h>
#include <CppUTest/TestHarness.h>

extern "C" {
#include <app_common.h>
#include <debug.h>
#include <dev_assign_private.h>
#include <el0_app_helpers.h>
#include <industry_standard/pci_tdisp.h>
#include <industry_standard/pcidoe.h>
#include <internal/libspdm_common_lib.h>
#include <internal/libspdm_secured_message_lib.h>
#include <smc-rmi.h>
#include <string.h>

extern const libspdm_secured_message_callbacks_t cma_spdm_sec_msg_cbs;
}

static unsigned char app_heap[HEAP_PAGE_COUNT * GRANULE_SIZE] __aligned(GRANULE_SIZE);
static unsigned char shared_buf[GRANULE_SIZE] __aligned(GRANULE_SIZE);
static unsigned char cached_request[GRANULE_SIZE];
static unsigned char cached_response[GRANULE_SIZE];
static struct dev_comm_exit_shared cache_exit;
static unsigned int cache_writes;
static unsigned int cache_yields;

static struct dev_assign_info *info;
static libspdm_context_t *context;
static libspdm_secured_message_context_t *secured;
static unsigned char response[1024];
static unsigned char request[MAX_SPDM_REQUEST_SIZE];
static size_t request_len;

/* Malformed input tests deliberately trigger app error logging. */
extern "C" void rmm_log(const char *fmt, ...)
{
	(void)fmt;
}

/* Supply the instance heap to the production app and its Mbed TLS allocator. */
extern "C" void *get_heap_start(void)
{
	return app_heap;
}

/* Supply the shared parameters used by the app's public entry point. */
extern "C" void *get_shared_mem_start(void)
{
	return shared_buf;
}

/*
 * Model successful cache copyout through the app service interface. Reject
 * unexpected services or buffers so an invalid response cannot silently cache.
 */
extern "C" unsigned long el0_app_service_call(unsigned long service,
		unsigned long source, unsigned long offset, unsigned long destination,
		unsigned long length)
{
	UNSIGNED_LONGS_EQUAL(APP_SERVICE_WRITE_TO_NS_BUF, service);
	UNSIGNED_LONGS_EQUAL(APP_SERVICE_RW_NS_BUF_HEAP, source);
	CHECK_TRUE(offset <= sizeof(app_heap));
	CHECK_TRUE(length <= sizeof(app_heap) - offset);
	CHECK_TRUE((destination == (uintptr_t)cached_request) ||
		   (destination == (uintptr_t)cached_response));
	CHECK_TRUE(length <= sizeof(cached_response));
	(void)memcpy((void *)destination, app_heap + offset, length);
	*(size_t *)shared_buf = 0U;
	cache_writes++;
	return 0UL;
}

/* Capture the cache request, then resume with empty communication parameters. */
extern "C" void el0_app_yield(void)
{
	cache_exit = *(struct dev_comm_exit_shared *)shared_buf;
	cache_yields++;
	(void)memset(shared_buf, 0, sizeof(shared_buf));
}


/* Start a fresh exchange, including the running VCA hash where required. */
static void reset_cache(void)
{
	LONGS_EQUAL(PSA_SUCCESS, psa_hash_abort(&info->psa_hash_op));
	LONGS_EQUAL(PSA_SUCCESS, psa_hash_abort(&info->spdm_cert_chain_hash_op));
	LONGS_EQUAL(PSA_SUCCESS, psa_hash_setup(&info->psa_hash_op, PSA_ALG_SHA_384));
	info->cached_digest_type = CACHE_TYPE_NONE;
	info->cached_digest.len = 0U;
	info->spdm_request_len = 0U;
	info->spdm_cert_chain_len = 0U;
	info->cache_tdisp_if_report = false;
	info->enter_args.req_addr = (uintptr_t)cached_request;
	info->enter_args.resp_addr = (uintptr_t)cached_response;
	(void)memset(&info->exit_args, 0, sizeof(info->exit_args));
	(void)memset(&cache_exit, 0, sizeof(cache_exit));
	(void)memset(cached_response, 0xcc, sizeof(cached_response));
	(void)memset(response, 0, sizeof(response));
	(void)memset(request, 0, sizeof(request));
	cache_writes = 0U;
	cache_yields = 0U;
	request_len = 0U;
}

/* Encode a saved request through the production callback, without sending it. */
static void save_request(void)
{
	size_t size = sizeof(cached_request);
	void *message = info->send_recv_buffer;

	LONGS_EQUAL(PSA_SUCCESS, psa_hash_abort(&info->psa_hash_op));
	UNSIGNED_LONGS_EQUAL(LIBSPDM_STATUS_SUCCESS,
		context->transport_encode_message(context, NULL, false, true,
			request_len, request, &size, &message));
}

/*
 * Encrypt the supplied plaintext with a matching responder session. The
 * transport is deliberately larger than its plaintext, as in the regression.
 */
static libspdm_return_t decode(size_t length, bool encrypted = true)
{
	unsigned char plaintext[sizeof(response) + 64U];
	libspdm_secured_message_context_t responder = *secured;
	void *transport = info->send_recv_buffer;
	size_t transport_size = PRIV_LIBSPDM_SEND_RECV_BUF_SIZE;
	void *message = info->scratch_buffer;
	size_t message_size = PRIV_LIBSPDM_SCRATCH_BUF_SIZE;
	uint32_t *session_id = NULL;
	bool is_app = false;
	libspdm_return_t status;

	CHECK_TRUE(length <= sizeof(response));
	info->is_msg_sspdm = encrypted;
	if (encrypted) {
		/* libspdm writes a cipher header immediately before the plaintext. */
		(void)memcpy(plaintext + 64U, response, length);
		UNSIGNED_LONGS_EQUAL(LIBSPDM_STATUS_SUCCESS,
			libspdm_encode_secured_message(&responder, info->session_id, false,
				length, plaintext + 64U, &transport_size, transport,
				&cma_spdm_sec_msg_cbs));
		CHECK_TRUE(transport_size > length);
	} else {
		(void)memcpy(transport, response, length);
		transport_size = length;
	}
	status = context->transport_decode_message(context, &session_id, &is_app,
			false, transport_size, transport, &message_size, &message);
	if (cache_yields == 0U) {
		cache_exit.rmi_dev_comm_exit = info->exit_args;
		cache_exit.cached_digest = info->cached_digest;
	}
	return status;
}

/* Malformed responses must fail before publishing or copying cached bytes. */
static void expect_rejected(size_t length, bool encrypted = true)
{
	UNSIGNED_LONGS_EQUAL(LIBSPDM_STATUS_RECEIVE_FAIL, decode(length, encrypted));
	UNSIGNED_LONGS_EQUAL(0U, cache_writes);
	UNSIGNED_LONGS_EQUAL(0U, cache_yields);
	UNSIGNED_LONGS_EQUAL(0UL, info->exit_args.flags);
	UNSIGNED_LONGS_EQUAL(CACHE_TYPE_NONE, info->cached_digest_type);
}

/* Build a response with records, nonce, opaque data, and optional signature. */
static size_t measurements(bool signed_response, uint8_t version)
{
	spdm_message_header_t *req = (spdm_message_header_t *)request;
	spdm_measurements_response_t *rsp = (spdm_measurements_response_t *)response;
	size_t length = sizeof(*rsp) + 3U + SPDM_NONCE_SIZE;

	req->spdm_version = version;
	req->request_response_code = SPDM_GET_MEASUREMENTS;
	req->param2 = SPDM_GET_MEASUREMENTS_REQUEST_MEASUREMENT_OPERATION_ALL_MEASUREMENTS;
	request_len = sizeof(*req);
	if (signed_response) {
		req->param1 = SPDM_GET_MEASUREMENTS_REQUEST_ATTRIBUTES_GENERATE_SIGNATURE;
		request_len = sizeof(spdm_get_measurements_request_t);
	}
	if (version >= SPDM_MESSAGE_VERSION_13) {
		request_len += SPDM_REQ_CONTEXT_SIZE;
	}
	save_request();
	rsp->header.spdm_version = version;
	rsp->header.request_response_code = SPDM_MEASUREMENTS;
	rsp->number_of_blocks = 1U;
	libspdm_write_uint24(rsp->measurement_record_length, 3U);
	libspdm_write_uint16(response + length, 5U);
	length += sizeof(uint16_t) + 5U;
	if (version >= SPDM_MESSAGE_VERSION_13) {
		length += SPDM_REQ_CONTEXT_SIZE;
	}
	if (signed_response) {
		length += 96U;
	}
	return length;
}

/* Build the PCI-SIG vendor header and an interface report portion. */
static size_t interface_report(uint16_t portion_length)
{
	pci_doe_spdm_vendor_defined_response_t *vdm =
		(pci_doe_spdm_vendor_defined_response_t *)response;
	pci_tdisp_device_interface_report_response_t *report =
		(pci_tdisp_device_interface_report_response_t *)(response + sizeof(*vdm));

	vdm->spdm_header.request_response_code = SPDM_VENDOR_DEFINED_RESPONSE;
	vdm->pci_doe_vendor_header.standard_id = SPDM_STANDARD_ID_PCISIG;
	vdm->pci_doe_vendor_header.vendor_id = SPDM_VENDOR_ID_PCISIG;
	vdm->pci_doe_vendor_header.pci_protocol.protocol_id = PCI_PROTOCOL_ID_TDISP;
	report->header.message_type = PCI_TDISP_DEVICE_INTERFACE_REPORT;
	report->portion_length = portion_length;
	return sizeof(*vdm) + sizeof(*report) + portion_length;
}

/*
 * Exercise the callbacks registered by the real app initialization. Only EL2
 * services are replaced; SPDM encoding, decoding, and hashing use production
 * code. The fixture supplies a deterministic session without a device handshake.
 */
TEST_GROUP(dev_assign_response_tests) {
	/* Initialize the app and an established session with fixed test keys. */
	TEST_SETUP()
	{
		struct dev_assign_params *params = (struct dev_assign_params *)shared_buf;

		(void)memset(app_heap, 0, sizeof(app_heap));
		(void)memset(shared_buf, 0, sizeof(shared_buf));
		params->rmi_hash_algo = RMI_HASH_SHA_384;
		UNSIGNED_LONGS_EQUAL(DEV_ASSIGN_STATUS_SUCCESS,
			el0_app_entry_func(DEVICE_ASSIGN_APP_FUNC_ID_INIT,
					   sizeof(app_heap), 0UL, 0UL, 0UL));
		info = heap_start_to_dev_assign_info((uintptr_t)app_heap);
		context = (libspdm_context_t *)info->libspdm_ctx;
		context->connection_info.version = SPDM_MESSAGE_VERSION_12 <<
			SPDM_VERSION_NUMBER_SHIFT_BIT;
		context->connection_info.secured_message_version = SECURED_SPDM_VERSION_11 <<
			SPDM_VERSION_NUMBER_SHIFT_BIT;
		context->connection_info.capability.flags = context->local_context.capability.flags;
		context->connection_info.algorithm.base_hash_algo =
			SPDM_ALGORITHMS_BASE_HASH_ALGO_TPM_ALG_SHA_384;
		context->connection_info.algorithm.base_asym_algo =
			SPDM_ALGORITHMS_BASE_ASYM_ALGO_TPM_ALG_ECDSA_ECC_NIST_P384;
		context->connection_info.algorithm.dhe_named_group =
			SPDM_ALGORITHMS_DHE_NAMED_GROUP_SECP_384_R1;
		context->connection_info.algorithm.aead_cipher_suite =
			SPDM_ALGORITHMS_AEAD_CIPHER_SUITE_AES_256_GCM;
		context->connection_info.algorithm.key_schedule =
			SPDM_ALGORITHMS_KEY_SCHEDULE_HMAC_HASH;
		info->session_id = 0x12345678U;
		CHECK_TRUE(libspdm_assign_session_id(context, info->session_id, false) != NULL);
		secured = (libspdm_secured_message_context_t *)
			libspdm_get_secured_message_context_via_session_id(context, info->session_id);
		CHECK_TRUE(secured != NULL);
		libspdm_secured_message_set_session_state(secured,
						LIBSPDM_SESSION_STATE_ESTABLISHED);
		libspdm_secured_message_set_session_type(secured, LIBSPDM_SESSION_TYPE_ENC_MAC);
		reset_cache();
	}

	/* Release pending hashes before destroying the app's private allocator. */
	TEST_TEARDOWN()
	{
		LONGS_EQUAL(PSA_SUCCESS, psa_hash_abort(&info->psa_hash_op));
		LONGS_EQUAL(PSA_SUCCESS, psa_hash_abort(&info->spdm_cert_chain_hash_op));
		UNSIGNED_LONGS_EQUAL(DEV_ASSIGN_STATUS_SUCCESS,
			el0_app_entry_func(DEVICE_ASSIGN_APP_FUNC_ID_DEINIT, 0UL, 0UL, 0UL, 0UL));
		mbedtls_memory_buffer_alloc_free();
	}
};

/*
 * TC1: Reject incomplete SPDM headers in both transport forms.
 *
 * Public APIs tested:
 *   el0_app_entry_func() and the transport_decode_message callback it registers.
 *
 * Aim:
 *   Validate the decoded plaintext length even when the encrypted transport
 *   is large enough to contain an SPDM header.
 *
 * Method:
 *   Use the fixture's established ENC_MAC session. For each plaintext length
 *   from 0 to 3 bytes, reset the cache state and invoke the decode callback
 *   with both unsecured and encrypted responses.
 *
 * Expected results:
 *   Every decode returns LIBSPDM_STATUS_RECEIVE_FAIL. No cache writes or
 *   yields occur, exit flags remain zero, and cached_digest_type remains
 *   CACHE_TYPE_NONE.
 */
TEST(dev_assign_response_tests, short_spdm_headers)
{
	for (unsigned int encrypted = 0U; encrypted < 2U; encrypted++) {
		for (size_t length = 0U; length < sizeof(spdm_message_header_t); length++) {
			reset_cache();
			expect_rejected(length, encrypted != 0U);
		}
	}
}

/*
 * TC2: Reject incomplete secured-message headers.
 *
 * Public APIs tested:
 *   el0_app_entry_func() and the transport_decode_message callback it registers.
 *
 * Aim:
 *   Reject a secured message before accessing an incomplete session-ID field.
 *
 * Method:
 *   Mark the incoming message as secured and invoke the decode callback
 *   directly with transport lengths from 0 through
 *   sizeof(spdm_secured_message_a_data_header1_t) - 1.
 *
 * Expected results:
 *   Every decode returns LIBSPDM_STATUS_RECEIVE_FAIL, and no cache writes occur.
 */
TEST(dev_assign_response_tests, short_secured_headers)
{
	for (size_t length = 0U; length < sizeof(spdm_secured_message_a_data_header1_t);
	     length++) {
		uint32_t *session_id = NULL;
		bool is_app = false;
		void *message = info->scratch_buffer;
		size_t message_size = PRIV_LIBSPDM_SCRATCH_BUF_SIZE;

		info->is_msg_sspdm = true;
		UNSIGNED_LONGS_EQUAL(LIBSPDM_STATUS_RECEIVE_FAIL,
			context->transport_decode_message(context, &session_id, &is_app, false,
				length, response, &message_size, &message));
	}
	UNSIGNED_LONGS_EQUAL(0U, cache_writes);
}

/*
 * TC3: Reject incomplete outgoing SPDM headers.
 *
 * Public APIs tested:
 *   el0_app_entry_func() and the transport_encode_message callback it registers.
 *
 * Aim:
 *   Reject an outgoing request before accessing an incomplete SPDM header.
 *
 * Method:
 *   Invoke the encode callback with no session and request lengths from
 *   0 to 3 bytes, using the app's send/receive buffer for transport output.
 *
 * Expected results:
 *   Every encode returns LIBSPDM_STATUS_INVALID_PARAMETER, and
 *   spdm_request_len remains zero.
 */
TEST(dev_assign_response_tests, short_request_headers)
{
	for (size_t length = 0U; length < sizeof(spdm_message_header_t); length++) {
		void *transport = info->send_recv_buffer;
		size_t transport_size = PRIV_LIBSPDM_SEND_RECV_BUF_SIZE;

		UNSIGNED_LONGS_EQUAL(LIBSPDM_STATUS_INVALID_PARAMETER,
			context->transport_encode_message(context, NULL, false, true,
				length, request, &transport_size, &transport));
	}
	UNSIGNED_LONGS_EQUAL(0U, info->spdm_request_len);
}

/*
 * TC4: Validate the fixed fields and declared entries of VERSION responses.
 *
 * Public APIs tested:
 *   el0_app_entry_func() and the transport_decode_message callback it registers.
 *
 * Aim:
 *   Require the VERSION response to contain every declared version entry
 *   before publishing cache metadata.
 *
 * Method:
 *   Declare one version entry and decode unsecured responses with lengths
 *   from four bytes through the fixed response size plus one version entry.
 *   Reset cache state before each decode.
 *
 * Expected results:
 *   Truncated responses return LIBSPDM_STATUS_RECEIVE_FAIL without cache
 *   writes or yields; exit flags stay zero and the digest type stays
 *   CACHE_TYPE_NONE.
 *   The complete response returns LIBSPDM_STATUS_SUCCESS and reports the
 *   fixed response size plus one entry as cache_rsp_len.
 */
TEST(dev_assign_response_tests, version_lengths)
{
	const size_t complete = sizeof(spdm_version_response_t) + sizeof(spdm_version_number_t);

	for (size_t length = sizeof(spdm_message_header_t); length <= complete; length++) {
		spdm_version_response_t *rsp = (spdm_version_response_t *)response;

		reset_cache();
		rsp->header.request_response_code = SPDM_VERSION;
		rsp->version_number_entry_count = 1U;
		if (length < complete) {
			expect_rejected(length, false);
		} else {
			UNSIGNED_LONGS_EQUAL(LIBSPDM_STATUS_SUCCESS, decode(length, false));
			UNSIGNED_LONGS_EQUAL(complete, cache_exit.rmi_dev_comm_exit.cache_rsp_len);
		}
	}
}

/*
 * TC5: Require the full SPDM 1.2 CAPABILITIES response layout.
 *
 * Public APIs tested:
 *   el0_app_entry_func() and the transport_decode_message callback it registers.
 *
 * Aim:
 *   Include both transfer-size fields when validating the response length.
 *
 * Method:
 *   Decode unsecured CAPABILITIES responses with lengths from four bytes
 *   through sizeof(spdm_capabilities_response_t), resetting cache state
 *   before each decode.
 *
 * Expected results:
 *   Short responses return LIBSPDM_STATUS_RECEIVE_FAIL without cache writes
 *   or yields; exit flags stay zero and the digest type stays CACHE_TYPE_NONE.
 *   The full response returns LIBSPDM_STATUS_SUCCESS with cache_rsp_len equal to
 *   sizeof(spdm_capabilities_response_t).
 */
TEST(dev_assign_response_tests, capabilities_lengths)
{
	for (size_t length = sizeof(spdm_message_header_t);
	     length <= sizeof(spdm_capabilities_response_t); length++) {
		reset_cache();
		((spdm_message_header_t *)response)->request_response_code = SPDM_CAPABILITIES;
		if (length < sizeof(spdm_capabilities_response_t)) {
			expect_rejected(length, false);
		} else {
			UNSIGNED_LONGS_EQUAL(LIBSPDM_STATUS_SUCCESS, decode(length, false));
			UNSIGNED_LONGS_EQUAL(length, cache_exit.rmi_dev_comm_exit.cache_rsp_len);
		}
	}
}

/*
 * TC6: Validate the declared ALGORITHMS response length.
 *
 * Public APIs tested:
 *   el0_app_entry_func() and the transport_decode_message callback it registers.
 *
 * Aim:
 *   Require the fixed header and all bytes declared by the length field.
 *
 * Method:
 *   Declare sizeof(spdm_algorithms_response_t) + 12 bytes and decode unsecured
 *   buffers from four bytes through that length. Reset cache state for each
 *   decode. Also supply a full buffer with a declared length one byte smaller
 *   than sizeof(spdm_algorithms_response_t).
 *
 * Expected results:
 *   Truncated buffers and the undersized declared length return
 *   LIBSPDM_STATUS_RECEIVE_FAIL without cache writes or yields; exit flags
 *   stay zero and the digest type stays CACHE_TYPE_NONE. The complete response
 *   returns LIBSPDM_STATUS_SUCCESS with cache_rsp_len equal to the declared
 *   length.
 */
TEST(dev_assign_response_tests, algorithms_lengths)
{
	const size_t complete = sizeof(spdm_algorithms_response_t) + 12U;

	for (size_t length = sizeof(spdm_message_header_t); length <= complete; length++) {
		spdm_algorithms_response_t *rsp = (spdm_algorithms_response_t *)response;

		reset_cache();
		rsp->header.request_response_code = SPDM_ALGORITHMS;
		rsp->length = (uint16_t)complete;
		if (length < complete) {
			expect_rejected(length, false);
		} else {
			UNSIGNED_LONGS_EQUAL(LIBSPDM_STATUS_SUCCESS, decode(length, false));
			UNSIGNED_LONGS_EQUAL(complete, cache_exit.rmi_dev_comm_exit.cache_rsp_len);
		}
	}
	reset_cache();
	((spdm_algorithms_response_t *)response)->header.request_response_code = SPDM_ALGORITHMS;
	((spdm_algorithms_response_t *)response)->length = sizeof(spdm_algorithms_response_t) - 1U;
	expect_rejected(complete, false);
}

/*
 * TC7: Validate CERTIFICATE portions against the decoded plaintext length.
 *
 * Public APIs tested:
 *   el0_app_entry_func() and the transport_decode_message callback it registers.
 *
 * Aim:
 *   Prevent encrypted transport overhead from satisfying certificate length
 *   checks, and reject a first portion with no certificate bytes to cache.
 *
 * Method:
 *   Build a first portion containing spdm_cert_chain_t, a 48-byte root hash
 *   and three certificate bytes. Encrypt and decode each prefix from four
 *   bytes through the full response, resetting cache state each time. Also
 *   decode a portion containing only the chain header and root hash.
 *
 * Expected results:
 *   The complete response returns LIBSPDM_STATUS_SUCCESS, performs one cache
 *   write and reports three cached bytes. Truncated responses and the portion
 *   without certificate bytes return LIBSPDM_STATUS_RECEIVE_FAIL with no
 *   cache writes or yields, zero exit flags and digest type CACHE_TYPE_NONE.
 */
TEST(dev_assign_response_tests, certificate_plaintext_lengths)
{
	const size_t chain_header = sizeof(spdm_cert_chain_t) + 48U;
	const size_t complete = sizeof(spdm_certificate_response_t) + chain_header + 3U;

	for (size_t length = sizeof(spdm_message_header_t); length <= complete; length++) {
		spdm_certificate_response_t *rsp = (spdm_certificate_response_t *)response;

		reset_cache();
		rsp->header.request_response_code = SPDM_CERTIFICATE;
		rsp->portion_length = (uint16_t)(chain_header + 3U);
		if (length < complete) {
			expect_rejected(length);
		} else {
			UNSIGNED_LONGS_EQUAL(LIBSPDM_STATUS_SUCCESS, decode(length));
			UNSIGNED_LONGS_EQUAL(3U, cache_exit.rmi_dev_comm_exit.cache_rsp_len);
			UNSIGNED_LONGS_EQUAL(1U, cache_writes);
		}
	}
	reset_cache();
	((spdm_certificate_response_t *)response)->header.request_response_code = SPDM_CERTIFICATE;
	((spdm_certificate_response_t *)response)->portion_length = (uint16_t)chain_header;
	expect_rejected(sizeof(spdm_certificate_response_t) + chain_header);
}

/*
 * TC8: Validate TDISP interface-report headers and portion length.
 *
 * Public APIs tested:
 *   el0_app_entry_func() and the transport_decode_message callback it registers.
 *
 * Aim:
 *   Require complete vendor, TDISP and report headers and a nonempty report
 *   portion within the decoded plaintext.
 *
 * Method:
 *   Build a PCI-SIG TDISP interface-report response with an eight-byte portion.
 *   Encrypt and decode each prefix from four bytes through the full response,
 *   resetting cache state each time. Also decode a zero-length portion.
 *
 * Expected results:
 *   The full response returns LIBSPDM_STATUS_SUCCESS, performs one cache write
 *   and reports eight cached bytes. Truncated responses and the empty portion
 *   return LIBSPDM_STATUS_RECEIVE_FAIL with no cache writes or yields, zero
 *   exit flags and digest type CACHE_TYPE_NONE. Truncation leaves
 *   cache_tdisp_if_report false.
 */
TEST(dev_assign_response_tests, interface_report_plaintext_lengths)
{
	const size_t complete = interface_report(8U);

	for (size_t length = sizeof(spdm_message_header_t); length <= complete; length++) {
		reset_cache();
		(void)interface_report(8U);
		if (length < complete) {
			expect_rejected(length);
			CHECK_FALSE(info->cache_tdisp_if_report);
		} else {
			UNSIGNED_LONGS_EQUAL(LIBSPDM_STATUS_SUCCESS, decode(length));
			UNSIGNED_LONGS_EQUAL(8U, cache_exit.rmi_dev_comm_exit.cache_rsp_len);
			UNSIGNED_LONGS_EQUAL(1U, cache_writes);
		}
	}
	reset_cache();
	expect_rejected(interface_report(0U));
}

/*
 * TC9: Reject truncated signed and unsigned MEASUREMENTS responses.
 *
 * Public APIs tested:
 *   el0_app_entry_func() and the transport_encode_message and
 *   transport_decode_message callbacks it registers.
 *
 * Aim:
 *   Require all response fields selected by the saved request's version
 *   and signature attribute.
 *
 * Method:
 *   For SPDM 1.2 and 1.3, save GET_MEASUREMENTS requests with and without
 *   signatures. Build responses with three record bytes, a 32-byte nonce,
 *   five opaque bytes, RequesterContext for 1.3 and a 96-byte signature when
 *   requested. Encrypt and decode every prefix from four bytes to one byte
 *   short of completion, resetting cache state and saving the request again.
 *
 * Expected results:
 *   Every decode returns LIBSPDM_STATUS_RECEIVE_FAIL. No cache writes or
 *   yields occur, exit flags remain zero, and cached_digest_type remains
 *   CACHE_TYPE_NONE.
 */
TEST(dev_assign_response_tests, measurements_truncated)
{
	for (uint8_t version = SPDM_MESSAGE_VERSION_12; version <= SPDM_MESSAGE_VERSION_13;
	     version++) {
		for (unsigned int sign = 0U; sign < 2U; sign++) {
			size_t complete;

			reset_cache();
			complete = measurements(sign != 0U, version);
			for (size_t length = sizeof(spdm_message_header_t); length < complete;
			     length++) {
				reset_cache();
				(void)measurements(sign != 0U, version);
				expect_rejected(length);
			}
		}
	}
}

/*
 * TC10: Cache and hash only the complete MEASUREMENTS exchange.
 *
 * Public APIs tested:
 *   el0_app_entry_func() and the transport_encode_message and
 *   transport_decode_message callbacks it registers.
 *
 * Aim:
 *   Exclude trailing plaintext bytes from the cached response and transcript
 *   digest for SPDM 1.2 and 1.3 responses, with and without signatures.
 *
 * Method:
 *   Save each request and build a response with three record bytes, a 32-byte
 *   nonce, five opaque bytes and the applicable context and signature fields.
 *   Compute a reference SHA-384 digest of the request and complete response.
 *   Append zero through seven bytes of 0xa5, then encrypt and decode the
 *   response. Reset cache state before each exchange.
 *
 * Expected results:
 *   Every decode returns LIBSPDM_STATUS_SUCCESS with exactly two cache writes
 *   and one yield. Cached request and response lengths and contents match the
 *   complete messages. The byte after the cached response remains 0xcc, and
 *   the cached digest length and value match the reference SHA-384 digest.
 */
TEST(dev_assign_response_tests, measurements_cache_exact_response)
{
	for (uint8_t version = SPDM_MESSAGE_VERSION_12; version <= SPDM_MESSAGE_VERSION_13;
	     version++) {
		for (unsigned int sign = 0U; sign < 2U; sign++) {
			for (size_t padding = 0U; padding < 8U; padding++) {
				unsigned char transcript[sizeof(request) + sizeof(response)];
				unsigned char digest[48];
				size_t digest_len;
				size_t complete;

				reset_cache();
				complete = measurements(sign != 0U, version);
				(void)memcpy(transcript, request, request_len);
				(void)memcpy(transcript + request_len, response, complete);
				LONGS_EQUAL(PSA_SUCCESS, psa_hash_compute(PSA_ALG_SHA_384, transcript,
					request_len + complete, digest, sizeof(digest), &digest_len));
				(void)memset(response + complete, 0xa5, padding);
				UNSIGNED_LONGS_EQUAL(LIBSPDM_STATUS_SUCCESS, decode(complete + padding));
				UNSIGNED_LONGS_EQUAL(complete, cache_exit.rmi_dev_comm_exit.cache_rsp_len);
				UNSIGNED_LONGS_EQUAL(request_len, cache_exit.rmi_dev_comm_exit.cache_req_len);
				UNSIGNED_LONGS_EQUAL(2U, cache_writes);
				UNSIGNED_LONGS_EQUAL(1U, cache_yields);
				MEMCMP_EQUAL(response, cached_response, complete);
				MEMCMP_EQUAL(request, cached_request, request_len);
				UNSIGNED_LONGS_EQUAL(0xccU, cached_response[complete]);
				UNSIGNED_LONGS_EQUAL(digest_len, cache_exit.cached_digest.len);
				MEMCMP_EQUAL(digest, cache_exit.cached_digest.value, digest_len);
			}
		}
	}
}

/*
 * TC11: Reject invalid MEASUREMENTS lengths and saved-request metadata.
 *
 * Public APIs tested:
 *   el0_app_entry_func() and the transport_encode_message and
 *   transport_decode_message callbacks it registers.
 *
 * Aim:
 *   Reject impossible response lengths and missing or inconsistent request
 *   metadata before publishing cached data.
 *
 * Method:
 *   For each case, reset cache state, save a signed SPDM 1.2 GET_MEASUREMENTS
 *   request and build its response. Independently set the record length to
 *   0xffffff, set the opaque length to SPDM_MAX_OPAQUE_DATA_SIZE + 1, clear
 *   spdm_request_len, change the saved request code to SPDM_GET_VERSION, or
 *   change the response version to 1.3. Encrypt and decode the full response.
 *
 * Expected results:
 *   Every decode returns LIBSPDM_STATUS_RECEIVE_FAIL. No cache writes or
 *   yields occur, exit flags remain zero, and cached_digest_type remains
 *   CACHE_TYPE_NONE.
 */
TEST(dev_assign_response_tests, measurements_invalid_fields)
{
	for (unsigned int invalid = 0U; invalid < 5U; invalid++) {
		spdm_measurements_response_t *rsp = (spdm_measurements_response_t *)response;
		size_t complete;

		reset_cache();
		complete = measurements(true, SPDM_MESSAGE_VERSION_12);
		switch (invalid) {
		case 0U:
			libspdm_write_uint24(rsp->measurement_record_length, 0xffffffU);
			break;
		case 1U:
			libspdm_write_uint16(response + sizeof(*rsp) + 3U + SPDM_NONCE_SIZE,
				SPDM_MAX_OPAQUE_DATA_SIZE + 1U);
			break;
		case 2U:
			info->spdm_request_len = 0U;
			break;
		case 3U:
			((spdm_message_header_t *)info->spdm_request)->request_response_code =
				SPDM_GET_VERSION;
			break;
		default:
			rsp->header.spdm_version = SPDM_MESSAGE_VERSION_13;
			break;
		}
		expect_rejected(complete);
	}
}

/* Run independently of the RMM executable and its app service implementation. */
int main(int argc, char *argv[])
{
	return CommandLineTestRunner::RunAllTests(argc, argv);
}
