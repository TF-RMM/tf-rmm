/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <app_common.h>
#include <debug.h>
#include <dev_assign_helper.h>
#include <dev_assign_private.h>
#include <el0_app_helpers.h>
#include <library/spdm_crypt_lib.h>
#include <mbedtls/memory_buffer_alloc.h>
#include <psa/crypto.h>
#include <psa/crypto_struct.h>
#include <smc-rmi.h>
#include <string.h>

static void copy_back_exit_args_to_shared(struct dev_assign_info *info)
{
	struct dev_comm_exit_shared *shared;

	assert(info->shared_buf != NULL);
	shared = (struct dev_comm_exit_shared *)info->shared_buf;
	shared->rmi_dev_comm_exit = info->exit_args;
	shared->cached_digest.len = info->cached_digest.len;

	if (info->cached_digest.len != 0U) {
		(void)memcpy(shared->cached_digest.value, info->cached_digest.value,
			     info->cached_digest.len);
		info->cached_digest.len = 0;
	}
}

static libspdm_return_t spdm_send_message(void *spdm_context,
					      size_t request_size,
					      const void *request,
					      uint64_t timeout)
{
	struct dev_assign_info *info;
	int rc;
	uintptr_t buf_offset;

	info = spdm_to_dev_assign_info(spdm_context);
	assert(info->shared_buf != NULL);

	if ((uintptr_t)info->send_recv_buffer > (uintptr_t)request) {
		return LIBSPDM_STATUS_SEND_FAIL;
	}

	/*
	 * The request buffer can be allocated from either send_recv buffer or
	 * scratch buffer. Since both these buffers are next to each other,
	 * we can perform a sanity check.
	 */
	buf_offset = (uintptr_t)request - (uintptr_t)info->send_recv_buffer;

	size_t request_size_align = round_up(request_size, 8U);

	if ((buf_offset + request_size_align)
		> (PRIV_LIBSPDM_SEND_RECV_BUF_SIZE + PRIV_LIBSPDM_SCRATCH_BUF_SIZE)) {
		return LIBSPDM_STATUS_SEND_FAIL;
	}

	/* Clear out any extra bytes due to rounding up of request_size */
	(void)memset((void *)((uintptr_t)request + request_size),
		0, request_size_align - request_size);

	/*
	 * Sending the message. Device communication request is written to the
	 * NS buffer.
	 */
	rc = (int)el0_app_service_call(APP_SERVICE_WRITE_TO_NS_BUF,
		APP_SERVICE_RW_NS_BUF_HEAP, (unsigned long)buf_offset,
		info->enter_args.req_addr, request_size_align);
	/* NS start offset is expected to be 0. */
	assert(*((size_t *)info->shared_buf) == 0U);

	if (rc != 0) {
		return LIBSPDM_STATUS_SEND_FAIL;
	}

	info->exit_args.flags |= RMI_DEV_COMM_EXIT_FLAGS_SEND_BIT;
	info->exit_args.timeout = timeout;
	if (!info->is_msg_sspdm) {
		info->exit_args.protocol = (unsigned char)RMI_DEV_COMM_PROTOCOL_SPDM;
	} else {
		info->exit_args.protocol = (unsigned char)RMI_DEV_COMM_PROTOCOL_SECURE_SPDM;
	}
	info->exit_args.req_len = request_size;

	/* Copy back the exit args to shared buf */
	copy_back_exit_args_to_shared(info);

	el0_app_yield();

	info->enter_args = *((struct rmi_dev_comm_enter *)info->shared_buf);
	(void)memset(&info->exit_args, 0, sizeof(info->exit_args));

	if (info->enter_args.status == RMI_DEV_COMM_ENTER_STATUS_ERROR) {
		return LIBSPDM_STATUS_SEND_FAIL;
	}

	return LIBSPDM_STATUS_SUCCESS;
}

static libspdm_return_t spdm_receive_message(void *spdm_context,
						 size_t *response_size,
						 void **response,
						 uint64_t timeout)
{
	struct dev_assign_info *info = spdm_to_dev_assign_info(spdm_context);
	int rc;
	uintptr_t buf_offset;
	unsigned long resp_len = info->enter_args.resp_len;

	(void)timeout;

	info = spdm_to_dev_assign_info(spdm_context);

	if ((uintptr_t)info->send_recv_buffer > (uintptr_t)*response) {
		return LIBSPDM_STATUS_RECEIVE_FAIL;
	}

	buf_offset = (uintptr_t)*response - (uintptr_t)info->send_recv_buffer;

	size_t resp_len_align = round_up(resp_len, 8U);

	if ((buf_offset + resp_len_align)
			> (PRIV_LIBSPDM_SEND_RECV_BUF_SIZE + PRIV_LIBSPDM_SCRATCH_BUF_SIZE)) {
		return LIBSPDM_STATUS_RECEIVE_FAIL;
	}

	assert(info->enter_args.status == RMI_DEV_COMM_ENTER_STATUS_RESPONSE);

	/*
	 * Sending the message. Device communication request is written to the
	 * NS buffer.
	 */
	rc = (int)el0_app_service_call(APP_SERVICE_READ_FROM_NS_BUF_ALIGNED,
		APP_SERVICE_RW_NS_BUF_HEAP, (unsigned long)buf_offset,
		info->enter_args.resp_addr, resp_len_align);

	if (rc != 0) {
		return LIBSPDM_STATUS_RECEIVE_FAIL;
	}

	*response_size = resp_len;

	return LIBSPDM_STATUS_SUCCESS;
}

/* Get sequence number in an SPDM secure message. */
static uint8_t cma_spdm_get_sequence_number(uint64_t sequence_number,
					    uint8_t *sequence_number_buffer)
{
	/* Sequence number not required as no transport is used */
	(void)sequence_number;
	(void)sequence_number_buffer;
	return 0U;
}

/* Return max random number count in an SPDM secure message. */
static uint32_t cma_spdm_get_max_rand_num_cnt(void)
{
	/* Sequence number not required as no transport is used */
	return 0U;
}

/*
 * This function translates the negotiated secured_message_version to a DSP0277
 * version.
 */
static spdm_version_number_t cma_spdm_get_secured_spdm_version(
	spdm_version_number_t secured_message_version)
{
	/*
	 * In the currently used version of libspdm the caller is doing the
	 * translation, so returning the version parameter without change here.
	 */
	return secured_message_version;
}

/* cppcheck-suppress [misra-c2012-8.4] */
/* coverity[misra_c_2012_rule_8_4_violation:SUPPRESS] */
const libspdm_secured_message_callbacks_t cma_spdm_sec_msg_cbs = {
	.version = LIBSPDM_SECURED_MESSAGE_CALLBACKS_VERSION,
	.get_sequence_number = cma_spdm_get_sequence_number,
	.get_max_random_number_count = cma_spdm_get_max_rand_num_cnt,
	.get_secured_spdm_version = cma_spdm_get_secured_spdm_version,
};

static libspdm_return_t
spdm_transport_encode_message(void *spdm_context, const uint32_t *session_id,
				  bool is_app_message, bool is_request_message,
				  size_t message_size, void *message,
				  size_t *transport_message_size,
				  void **transport_message)
{
	libspdm_return_t status;
	struct dev_assign_info *info;
	uint8_t *sec_msg;
	size_t sec_msg_size;
	void *sec_msg_ctx;

	(void)is_app_message;
	info = spdm_to_dev_assign_info(spdm_context);

	/* Message send outside the secure session */
	if (session_id == NULL) {
		info->is_msg_sspdm = false;

		*transport_message_size = message_size;
		*transport_message = message;
		return LIBSPDM_STATUS_SUCCESS;
	}

	sec_msg_ctx = libspdm_get_secured_message_context_via_session_id(
		spdm_context, *session_id);
	if (sec_msg_ctx == NULL) {
		return LIBSPDM_STATUS_UNSUPPORTED_CAP;
	}

	/* convert message to secured message */
	sec_msg = (uint8_t *)*transport_message;
	sec_msg_size = *transport_message_size;
	status = libspdm_encode_secured_message(sec_msg_ctx, *session_id,
						is_request_message,
						message_size, message,
						&sec_msg_size, sec_msg,
						&cma_spdm_sec_msg_cbs);
	if (status != LIBSPDM_STATUS_SUCCESS) {
		INFO("cma_spdm: encode_secured_message failed\n");
		return status;
	}

	info->is_msg_sspdm = true;

	/* No transport header are used */
	*transport_message_size = sec_msg_size;
	*transport_message = (void *)sec_msg;

	return LIBSPDM_STATUS_SUCCESS;
}

/*
 * Set cache flags in DevCommExit and compute digest of cached data.
 */
static int dev_assign_dev_comm_set_cache(struct dev_assign_info *info, void *cache_buf,
				  size_t cache_offset, size_t cache_len,
				  uint8_t cache_type, uint8_t hash_op_flags)
{
	const size_t digest_size = DEV_OBJ_DIGEST_MAX;
	size_t ns_buf_cache_offset;
	void *cache_src;
	int rc;

	cache_src = (void *)((unsigned long)cache_buf + cache_offset);

	/*
	 * If 'is_msg_sspdm' is true, then overwrite the NS response buffer with the
	 * decrypted data. Else use the existing content to be cached by the
	 * NS host.
	 */
	if (info->is_msg_sspdm) {

		/*
		 * In case of secure message the NS buffer is overwritten with
		 * the decrypted data.
		 */
		rc = (int)el0_app_service_call(APP_SERVICE_WRITE_TO_NS_BUF,
			APP_SERVICE_RW_NS_BUF_HEAP, (uintptr_t)cache_src -
				(uintptr_t)(info->send_recv_buffer),
			info->enter_args.resp_addr, cache_len);
		assert(info->shared_buf != NULL);
		ns_buf_cache_offset = *((size_t *)info->shared_buf);
		assert(ns_buf_cache_offset < 8U);
		if (rc != 0) {
			return -1;
		}
	} else {
		/*
		 * In case of non-secure message the existing content in the NS
		 * buffer is used for caching.
		 */
		ns_buf_cache_offset = cache_offset;
	}

	assert(info->cached_digest.len == 0U);

	rc = dev_assign_hash_extend(info->psa_hash_algo, &info->psa_hash_op,
				    hash_op_flags, cache_src, cache_len,
				    info->cached_digest.value, digest_size,
				    &info->cached_digest.len);
	if (rc != 0) {
		return -1;
	}

	info->exit_args.flags |= RMI_DEV_COMM_EXIT_FLAGS_CACHE_RSP_BIT;
	info->exit_args.cache_rsp_offset = ns_buf_cache_offset;
	info->exit_args.cache_rsp_len = cache_len;
	if (cache_type == CACHE_TYPE_CERT) {
		info->exit_args.cache_obj_id = (unsigned char)RMI_DEV_COMM_OBJECT_CERTIFICATE;
	} else if (cache_type == CACHE_TYPE_MEAS) {
		info->exit_args.cache_obj_id = (unsigned char)RMI_DEV_COMM_OBJECT_MEASUREMENTS;
	}

	return 0;
}

static psa_algorithm_t spdm_to_psa_hash_algo(uint32_t spdm_hash_algo)
{
	if (spdm_hash_algo ==
	    (uint32_t)SPDM_ALGORITHMS_BASE_HASH_ALGO_TPM_ALG_SHA_256) {
		return PSA_ALG_SHA_256;
	} else if (spdm_hash_algo ==
		   (uint32_t)SPDM_ALGORITHMS_BASE_HASH_ALGO_TPM_ALG_SHA_384) {
		return PSA_ALG_SHA_384;
	}

	return PSA_ALG_NONE;
}

/* Cache spdm certificate response */
static int cma_spdm_cache_certificate(struct dev_assign_info *info,
				      spdm_certificate_response_t *cert_rsp)
{
	size_t cache_offset, cache_len;
	uint8_t hash_op_flags = 0;
	uint8_t *hash_src;
	int rc;

	/* Start of certificate chain */
	if (info->spdm_cert_chain_len == 0U) {
		libspdm_return_t status;
		libspdm_data_parameter_t param;
		size_t cert_chain_offset;
		uint32_t spdm_hash_algo = 0U;
		size_t data_sz;
		psa_algorithm_t spdm_cert_chain_algo;

		(void)memset(&param, 0, sizeof(libspdm_data_parameter_t));
		param.location = LIBSPDM_DATA_LOCATION_CONNECTION;
		data_sz = sizeof(uint32_t);
		status = libspdm_get_data(info->libspdm_ctx,
					  LIBSPDM_DATA_BASE_HASH_ALGO,
					  &param, &spdm_hash_algo,
					  &data_sz);
		if (status != LIBSPDM_STATUS_SUCCESS) {
			return -1;
		}

		spdm_cert_chain_algo = spdm_to_psa_hash_algo(spdm_hash_algo);
		if (spdm_cert_chain_algo == PSA_ALG_NONE) {
			return -1;
		}

		/* Set SPDM cert_chain hash algo */
		info->spdm_cert_chain_algo = spdm_cert_chain_algo;
		hash_op_flags = HASH_OP_FLAG_SETUP;
		info->spdm_cert_chain_hash_op = psa_hash_operation_init();
		info->psa_hash_op = psa_hash_operation_init();

		/*
		 * For the start of the certificate chain ignore the hash of
		 * root certificate included in the response buffer.
		 */
		cert_chain_offset = sizeof(spdm_cert_chain_t) +
			libspdm_get_hash_size(spdm_hash_algo);
		cache_offset = sizeof(spdm_certificate_response_t) +
			cert_chain_offset;
		if (cert_chain_offset > cert_rsp->portion_length) {
			return -1;
		}
		cache_len = cert_rsp->portion_length - cert_chain_offset;
	} else {
		cache_offset = sizeof(spdm_certificate_response_t);
		cache_len = cert_rsp->portion_length;
	}

	hash_op_flags |= HASH_OP_FLAG_UPDATE;
	if (cert_rsp->remainder_length == 0U) {
		hash_op_flags |= HASH_OP_FLAG_FINISH;
	}

	/*
	 * Compute the hash for the entire spdm_certificate_response. This hash
	 * will be later used to set it in SPDM connection. It need to be set
	 * instead of letting libspdm calculate it, because the whole
	 * certificate chain is not stored in RMM memory.
	 */
	hash_src = (uint8_t *)((unsigned long)cert_rsp +
			       sizeof(spdm_certificate_response_t));
	rc = dev_assign_hash_extend(info->spdm_cert_chain_algo,
				 &info->spdm_cert_chain_hash_op, hash_op_flags,
				 hash_src, cert_rsp->portion_length,
				 info->spdm_cert_chain_digest,
				 sizeof(info->spdm_cert_chain_digest),
				 &info->spdm_cert_chain_digest_length);
	if (rc != 0) {
		return -1;
	}

	/*
	 * As certificate is received (in parts or whole) invoke cache callback
	 * to let NS Host to cache device certificate.
	 */
	rc = dev_assign_dev_comm_set_cache(info, cert_rsp, cache_offset,
				  cache_len, (uint8_t)CACHE_TYPE_CERT, hash_op_flags);

	info->spdm_cert_chain_len += cert_rsp->portion_length;

	return rc;
}

/* Process device measurements response */
static int dev_assign_cache_measurements(struct dev_assign_info *info,
					 spdm_measurements_response_t *meas_rsp)
{
	size_t cache_offset, cache_len;
	uint8_t hash_op_flags;
	int rc;

	/*
	 * Measurement length is a three byte wide integer represented as a 3
	 * bytes array, index 0 being the least significant byte. Reconstruct
	 * the value cache_len.
	 */
	/* coverity[misra_c_2012_rule_12_2_violation:SUPPRESS] */
	cache_len = ((size_t)meas_rsp->measurement_record_length[0]) |
		    ((size_t)meas_rsp->measurement_record_length[1] << 8U) |
		    ((size_t)meas_rsp->measurement_record_length[2] << 16U);
	if (cache_len > (size_t)LIBSPDM_MAX_MEASUREMENT_RECORD_SIZE) {
		return -1;
	}

	cache_offset = sizeof(spdm_measurements_response_t);
	hash_op_flags = (HASH_OP_FLAG_SETUP | HASH_OP_FLAG_UPDATE |
			 HASH_OP_FLAG_FINISH);
	info->psa_hash_op = psa_hash_operation_init();

	rc = dev_assign_dev_comm_set_cache(info, meas_rsp, cache_offset,
				  cache_len, (uint8_t)CACHE_TYPE_MEAS, hash_op_flags);

	return rc;
}

static libspdm_return_t
spdm_transport_decode_secured_message(struct dev_assign_info *info,
				      void *spdm_context, uint32_t **session_id,
				      bool is_request_message,
				      size_t transport_message_size,
				      void *transport_message,
				      size_t *message_size, void **message)
{
	libspdm_return_t status;
	spdm_secured_message_a_data_header1_t *sec_msg_hdr1;
	libspdm_error_struct_t spdm_error;
	void *sec_msg_ctx;
	uint8_t *sec_msg;
	size_t sec_msg_size;

	/* No transport headers, set secured message and its size */
	sec_msg = transport_message;
	sec_msg_size = transport_message_size;

	/*
	 * Last message was sent inside session, get session ID from the
	 * encrpyted message received and check against the session id in CMA
	 * SPDM context.
	 */
	sec_msg_hdr1 = (spdm_secured_message_a_data_header1_t *)sec_msg;
	if (sec_msg_hdr1->session_id != info->session_id) {
		return LIBSPDM_STATUS_UNSUPPORTED_CAP;
	}

	/* Get secured message context from session id */
	sec_msg_ctx = libspdm_get_secured_message_context_via_session_id(
		spdm_context,  info->session_id);
	if (sec_msg_ctx == NULL) {
		spdm_error.error_code = SPDM_ERROR_CODE_INVALID_SESSION;
		spdm_error.session_id = info->session_id;
		libspdm_set_last_spdm_error_struct(spdm_context, &spdm_error);
		return LIBSPDM_STATUS_UNSUPPORTED_CAP;
	}

	/* Convert secured mssage to normal message */
	status = libspdm_decode_secured_message(sec_msg_ctx, info->session_id,
						is_request_message,
						sec_msg_size, sec_msg,
						message_size, message,
						&cma_spdm_sec_msg_cbs);
	if (status != LIBSPDM_STATUS_SUCCESS) {
		libspdm_secured_message_get_last_spdm_error_struct(
			sec_msg_ctx, &spdm_error);
		libspdm_set_last_spdm_error_struct(spdm_context, &spdm_error);
		return status;
	}

	*session_id = &info->session_id;

	return LIBSPDM_STATUS_SUCCESS;
}

static libspdm_return_t
spdm_transport_decode_message(void *spdm_context, uint32_t **session_id,
			      bool *is_app_message, bool is_request_message,
			      size_t transport_message_size,
			      void *transport_message,
			      size_t *message_size, void **message)
{
	struct dev_assign_info *info;
	spdm_message_header_t *spdm_hdr;
	int rc;

	(void)is_app_message;
	info = spdm_to_dev_assign_info(spdm_context);

	/*
	 * As no transport headers are available, the type of the received
	 * message is SPDM or SECURED_SPDM based on last sent request type.
	 */
	if (!info->is_msg_sspdm) {
		*session_id = NULL;
		*message_size = transport_message_size;
		*message = transport_message;
	} else {
		libspdm_return_t status;

		status = spdm_transport_decode_secured_message(info, spdm_context, session_id,
				is_request_message, transport_message_size, transport_message,
				message_size, message);
		if (status != LIBSPDM_STATUS_SUCCESS) {
			return status;
		}
	}

	if (transport_message_size < sizeof(spdm_message_header_t)) {
		return LIBSPDM_STATUS_RECEIVE_FAIL;
	}
	spdm_hdr = (spdm_message_header_t *)*message;

	/*
	 * Cache device objects like certificate, interface_report, measurements
	 * once the message is decrypted.
	 */
	if (spdm_hdr->request_response_code == (uint8_t)SPDM_CERTIFICATE) {
		spdm_certificate_response_t *cert_rsp;

		if (transport_message_size < sizeof(spdm_certificate_response_t)) {
			return LIBSPDM_STATUS_RECEIVE_FAIL;
		}
		cert_rsp = (spdm_certificate_response_t *)spdm_hdr;

		/* Make sure portion length is in bounds of the message size. */
		if (cert_rsp->portion_length  >
			(transport_message_size - sizeof(spdm_certificate_response_t))) {
			return LIBSPDM_STATUS_RECEIVE_FAIL;
		}

		rc = cma_spdm_cache_certificate(info, cert_rsp);
		if (rc != 0) {
			return LIBSPDM_STATUS_RECEIVE_FAIL;
		}
	} else if (spdm_hdr->request_response_code ==
		   (uint8_t)SPDM_MEASUREMENTS) {
		spdm_measurements_response_t *meas_rsp;

		meas_rsp = (spdm_measurements_response_t *)spdm_hdr;
		rc = dev_assign_cache_measurements(info, meas_rsp);
		if (rc != 0) {
			return LIBSPDM_STATUS_RECEIVE_FAIL;
		}
	}

	return LIBSPDM_STATUS_SUCCESS;
}

static libspdm_return_t spdm_acquire_sender_buffer(void *spdm_context,
						       void **msg_buf_ptr)
{
	struct dev_assign_info *info __unused;

	info = spdm_to_dev_assign_info(spdm_context);
	*msg_buf_ptr = info->send_recv_buffer;

	return LIBSPDM_STATUS_SUCCESS;
}

static void spdm_release_sender_buffer(void *spdm_context,
					   const void *msg_buf_ptr)
{
	struct dev_assign_info *info __unused;

	(void)msg_buf_ptr;
	info = spdm_to_dev_assign_info(spdm_context);
	assert(info->send_recv_buffer == msg_buf_ptr);
	/* Nothing to do */
}

static libspdm_return_t spdm_acquire_receiver_buffer(void *spdm_context,
							 void **msg_buf_ptr)
{
	struct dev_assign_info *info;

	info = spdm_to_dev_assign_info(spdm_context);
	*msg_buf_ptr = info->send_recv_buffer;

	return LIBSPDM_STATUS_SUCCESS;
}

static void spdm_release_receiver_buffer(void *spdm_context,
					     const void *msg_buf_ptr)
{
	struct dev_assign_info *info __unused;

	(void)msg_buf_ptr;
	info = spdm_to_dev_assign_info(spdm_context);
	assert(info->send_recv_buffer == msg_buf_ptr);
	/* Nothing to do */
}

static bool cma_spdm_verify_cert_chain(void *spdm_context, uint8_t slot_id,
				       size_t cert_chain_size,
				       const void *cert_chain,
				       const void **trust_anchor,
				       size_t *trust_anchor_size)
{
	(void)spdm_context;
	(void)slot_id;
	(void)cert_chain_size;
	(void)cert_chain;
	(void)trust_anchor;
	(void)trust_anchor_size;
	assert(cert_chain == NULL);

	/*
	 * The certificate is not stored by RMM, so this function is
	 * intentionally left empty.
	 *
	 * Certificate verification is the responsibility of the realm the
	 * device is assigned to.
	 */
	return true;
}

void dev_assign_unset_pubkey(struct dev_assign_info *info)
{
	libspdm_data_parameter_t parameter;
	void *data_ptr;

	if (info->pk_ctx.initialised) {
		if ((info->key_sig_algo == RMI_SIGNATURE_ALGORITHM_ECDSA_P256) ||
		    (info->key_sig_algo == RMI_SIGNATURE_ALGORITHM_ECDSA_P384)) {
			mbedtls_ecdh_free(&info->pk_ctx.ecdh);
		} else {
			assert(info->key_sig_algo == RMI_SIGNATURE_ALGORITHM_RSASSA_3072);
			mbedtls_rsa_free(&info->pk_ctx.rsa);
		}
		info->pk_ctx.initialised = false;
	}

	/* Set LIBSPDM_DATA_PEER_USED_CERT_CHAIN_PUBLIC_KEY in spdm connection */
	(void)memset(&parameter, 0, sizeof(parameter));
	parameter.location = LIBSPDM_DATA_LOCATION_CONNECTION;
	parameter.additional_data[0] = info->cert_slot_id;
	data_ptr = NULL;
	(void)libspdm_set_data(info->libspdm_ctx,
			       LIBSPDM_DATA_PEER_USED_CERT_CHAIN_PUBLIC_KEY,
			       &parameter, (void *)&data_ptr, sizeof(data_ptr));
}

/*
 * Set public key context in libspdm connection
 */
static int dev_assign_set_pubkey(uintptr_t heap,
				     unsigned long key_sig_algo)
{
	libspdm_data_parameter_t parameter;
	libspdm_return_t status;
	struct dev_assign_info *info;
	void *data_ptr;
	int rc;

	info = heap_start_to_dev_assign_info(heap);

	struct rmi_public_key_params *params =
		(struct rmi_public_key_params *)get_shared_mem_start();

	if ((key_sig_algo == RMI_SIGNATURE_ALGORITHM_ECDSA_P256) ||
	    (key_sig_algo == RMI_SIGNATURE_ALGORITHM_ECDSA_P384)) {
		mbedtls_ecdh_context *ecdh;
		mbedtls_ecp_keypair kp;
		mbedtls_ecp_group grp;
		mbedtls_ecp_point pt;

		ecdh = &info->pk_ctx.ecdh;

		mbedtls_ecdh_init(ecdh);
		mbedtls_ecp_keypair_init(&kp);
		mbedtls_ecp_group_init(&grp);
		mbedtls_ecp_point_init(&pt);

		/* todo: call keypair/group/point_free upon mbedtls_error */
		if (key_sig_algo == RMI_SIGNATURE_ALGORITHM_ECDSA_P256) {
			VERBOSE("PDEV_SET_PUBKEY called with ECDSAP256 Algo\n");
			rc = mbedtls_ecp_group_load(&grp,
						    MBEDTLS_ECP_DP_SECP256R1);
		} else {
			VERBOSE("PDEV_SET_PUBKEY called with ECDSAP384 Algo\n");
			rc = mbedtls_ecp_group_load(&grp,
						    MBEDTLS_ECP_DP_SECP384R1);
		}
		if (rc != 0) {
			goto end_ecdsa;
		}

		rc = mbedtls_ecp_point_read_binary(&grp, &pt, params->key, params->key_len);
		if (rc != 0) {
			goto end_ecdsa;
		}

		/*
		 * grp.id will be populated as part of read_binary, ignore
		 * coverity uninitialized value
		 */
		/* coverity[uninit_use_in_call:SUPPRESS] */
		rc = mbedtls_ecp_set_public_key(grp.id, &kp, &pt);
		if (rc != 0) {
			goto end_ecdsa;
		}

		rc = mbedtls_ecdh_get_params(ecdh, &kp, MBEDTLS_ECDH_OURS);
		if (rc != 0) {
			goto end_ecdsa;
		}

end_ecdsa:
		mbedtls_ecp_keypair_free(&kp);
		mbedtls_ecp_group_free(&grp);
		mbedtls_ecp_point_free(&pt);
		if (rc != 0) {
			mbedtls_ecdh_free(ecdh);
			return DEV_ASSIGN_STATUS_ERROR;
		}
	} else if (key_sig_algo == RMI_SIGNATURE_ALGORITHM_RSASSA_3072) {
		mbedtls_rsa_context *ctx = &info->pk_ctx.rsa;

		mbedtls_rsa_init(ctx);

		/* Public exponent of RSA3072 key is held in metadata */
		rc = mbedtls_rsa_import_raw(ctx, params->key, params->key_len, NULL, 0, NULL, 0,
					    NULL, 0, params->metadata, params->metadata_len);
		if (rc != 0) {
			mbedtls_rsa_free(ctx);
			return DEV_ASSIGN_STATUS_ERROR;
		}
	} else {
		ERROR("PDEV_SET_PUBKEY: Invalid Signature algorithm: %lu\n", key_sig_algo);
		return DEV_ASSIGN_STATUS_ERROR;
	}

	info->key_sig_algo = (uint32_t)key_sig_algo;
	info->pk_ctx.initialised = true;

	/* Set LIBSPDM_DATA_PEER_USED_CERT_CHAIN_PUBLIC_KEY in spdm connection */
	(void)memset(&parameter, 0, sizeof(parameter));
	parameter.location = LIBSPDM_DATA_LOCATION_CONNECTION;
	parameter.additional_data[0] = info->cert_slot_id;
	data_ptr = (void *)&info->pk_ctx;
	status = libspdm_set_data(info->libspdm_ctx,
				  LIBSPDM_DATA_PEER_USED_CERT_CHAIN_PUBLIC_KEY,
				  &parameter, (void *)&data_ptr, sizeof(data_ptr));
	if (status != LIBSPDM_STATUS_SUCCESS) {
		dev_assign_unset_pubkey(info);
		return DEV_ASSIGN_STATUS_ERROR;
	}

	return DEV_ASSIGN_STATUS_SUCCESS;
}

/*
 * Returns the min heap size. This include libspdm context, libspdm secured
 * message context, libspdm scratch space, libspdm send recv buffer and
 * MbedTLS heap.
 */
static size_t get_min_heap_size(void)
{
	size_t total;

	/*
	 * As libspdm public headers do not export the type of libsdpm_context.
	 * RMM reserves 8192 bytes and check at runtime if the size is enough.
	 */
	assert(libspdm_get_context_size() <= PRIV_LIBSPDM_CONTEXT_SIZE);

	total = sizeof(struct dev_assign_info) +
		PRIV_LIBSPDM_SEND_RECV_BUF_SIZE +
		PRIV_LIBSPDM_CONTEXT_SIZE +
		PRIV_LIBSPDM_SCRATCH_BUF_SIZE +
		PRIV_LIBSPDM_MBEDTLS_HEAP_SIZE;

	return total;
}

static inline psa_algorithm_t rmi_to_psa_hash_algo(uint8_t rmi_hash_algo)
{
	if (rmi_hash_algo == RMI_HASH_SHA_256) {
		return PSA_ALG_SHA_256;
	} else if (rmi_hash_algo == RMI_HASH_SHA_512) {
		return PSA_ALG_SHA_512;
	}

	return PSA_ALG_NONE;
}

/* coverity[misra_c_2012_rule_5_8_violation:SUPPRESS] */
void *mbedtls_app_get_heap(void)
{
	struct dev_assign_info *info;

	info = heap_start_to_dev_assign_info((uintptr_t)get_heap_start());
	return &(info->mbedtls_heap_ctx);
}

/*
 * Clear all assigned buffers address that are used by CMA SPDM and call
 * libspdm_deinit_context to freeup the memory of contexts within the SPDM
 * context.
 */
static int dev_assign_deinit(uintptr_t heap)
{
	void *spdm_ctx;
	struct dev_assign_info *info;

	info = heap_start_to_dev_assign_info(heap);

	info->send_recv_buffer = NULL;
	info->scratch_buffer = NULL;
	info->mbedtls_heap_buf = NULL;

	/* Connection state related cleanup is handled by connection_deinit */
	spdm_ctx = info->libspdm_ctx;
	libspdm_deinit_context(spdm_ctx);
	return DEV_ASSIGN_STATUS_SUCCESS;
}

/*
 * Assigns buffers to various objects as mentioned in the below mapping starting
 * from start of EL0 heap. Note that send_recv_buffer must be first and
 * libspdm_context must be just before struct dsm as this is assumed in
 * spdm_to_dev_assign_info() macro.
 *
 *       --------------------------------
 *      |      send_recv_buffer          | PRIV_LIBSPDM_SEND_RECV_BUF_SIZE
 *      |--------------------------------|
 *      |    libspdm scratch_buffer      | PRIV_LIBSPDM_SCRATCH_BUF_SIZE
 *      |--------------------------------|
 *      |      MbedTLS heap buffer       | PRIV_LIBSPDM_MBEDTLS_HEAP_SIZE
 *      |--------------------------------|
 *      |  |     libspdm_context     |   | PRIV_DATA_LIBSPMD_CONTEXT_SIZE
 *      |--|                         |---|
 *      |  | struct dev_assign_info  |   | sizeof(struct dev_assign_info)
 *       --------------------------------
 *
 * Inits libspdm context using libspdm helper routines and registers send/recv
 * buffer acquire/release routines. Registers device send/recv callback handlers.
 *
 * This function suppresses few MISRA rule 10.1 violations, as the macros that
 * causes these violations are not declared as unsigned type and these macros
 * are from libspdm header files.
 */
static int dev_assign_init(uintptr_t el0_heap, size_t heap_size, struct dev_assign_params *params)
{
	libspdm_return_t status __unused;
	spdm_version_number_t cma_spdm_version;
	spdm_version_number_t cma_sspdm_version;
	libspdm_data_parameter_t parameter;
	struct dev_assign_info *info;
	void *spdm_ctx;
	uint32_t data32;
	uint16_t data16;
	uint8_t data8;
	size_t sb_size;

	if (heap_size < get_min_heap_size()) {
		ERROR("Min heap size 0x%lx expected. Current heap size = 0x%lx\n",
			get_min_heap_size(), heap_size);
		return DEV_ASSIGN_STATUS_ERROR;
	}

	if (params->cert_slot_id >= (uint8_t)SPDM_MAX_SLOT_COUNT) {
		return DEV_ASSIGN_STATUS_ERROR;
	}

	info = heap_start_to_dev_assign_info(el0_heap);

	info->send_recv_buffer = (void *)el0_heap;
	info->scratch_buffer =  (void *)((uintptr_t)info->send_recv_buffer +
			PRIV_LIBSPDM_SEND_RECV_BUF_SIZE);
	info->mbedtls_heap_buf = (void *)((uintptr_t)info->scratch_buffer +
			PRIV_LIBSPDM_SCRATCH_BUF_SIZE);
	info->libspdm_ctx = (void *)((uintptr_t)info->mbedtls_heap_buf +
			PRIV_LIBSPDM_MBEDTLS_HEAP_SIZE);
	info->cached_digest.len = 0U;

	assert((uintptr_t)spdm_to_dev_assign_info(info->libspdm_ctx) == (uintptr_t)info);

	VERBOSE("dev assign send_recv buf: 0x%p\n", info->send_recv_buffer);
	VERBOSE("dev assign scratch_buffer: 0x%p\n", info->scratch_buffer);
	VERBOSE("dev assign libspdm_ctx: 0x%p\n", info->libspdm_ctx);
	VERBOSE("dev assign info: 0x%p\n", (void *)info);


	/* Initialize the mbedTLS heap */
	mbedtls_memory_buffer_alloc_init(info->mbedtls_heap_buf, PRIV_LIBSPDM_MBEDTLS_HEAP_SIZE);

	/* Initialize DSM */
	info->dev_handle = params->dev_handle;
	info->cert_slot_id = params->cert_slot_id;
	info->has_ide = params->has_ide;
	if (info->has_ide) {
		info->ecam_addr = params->ecam_addr;
		info->rp_id = params->rp_id;
		info->ide_sid = params->ide_sid;
	}
	info->spdm_cert_chain_digest_length = 0;
	info->pk_ctx.initialised = false;
	info->session_id = 0U;

	info->psa_hash_algo = rmi_to_psa_hash_algo(params->rmi_hash_algo);

	/*
	 * Initialize SPDM and Secure SPDM context. 'spdm_ctx' is a combination
	 * of both SPDM context and secured message context.
	 */
	spdm_ctx = info->libspdm_ctx;
	status = libspdm_init_context(spdm_ctx);
	assert(status == LIBSPDM_STATUS_SUCCESS);

	/* Register device send/recv handlers */
	libspdm_register_device_io_func(spdm_ctx, spdm_send_message,
					spdm_receive_message);

	/*
	 * No transport encodings used as this is handled by NS host. So the
	 * transport_header_size and transport_tail_size are passed as 0.
	 */
	libspdm_register_transport_layer_func(spdm_ctx,
					      (uint32_t)CMA_MAX_SPDM_MSG_SIZE,
					      0U, /* transport_header_size */
					      0U, /* transport_tail_size */
					      spdm_transport_encode_message,
					      spdm_transport_decode_message);

	/* Register send/recv buffer acquire/release functions */
	libspdm_register_device_buffer_func(spdm_ctx,
					    (uint32_t)CMA_SENDER_BUFFER_SIZE,
					    (uint32_t)CMA_RECEIVER_BUFFER_SIZE,
					    spdm_acquire_sender_buffer,
					    spdm_release_sender_buffer,
					    spdm_acquire_receiver_buffer,
					    spdm_release_receiver_buffer);

	/* Set scratch buffer size */
	sb_size = libspdm_get_sizeof_required_scratch_buffer(spdm_ctx);

	VERBOSE("libspdm_context_size: 0x%lx\n", libspdm_get_context_size());
	VERBOSE("libspdm_scratch_buffer_size: 0x%lx\n", sb_size);
	VERBOSE("struct dev_assign_info size: 0x%lx\n", sizeof(struct dev_assign_info));

	assert(sb_size <= PRIV_LIBSPDM_SCRATCH_BUF_SIZE);
	libspdm_set_scratch_buffer(spdm_ctx, info->scratch_buffer, sb_size);

	/* Check libspdm context */
	if (!libspdm_check_context(spdm_ctx)) {
		assert(false);
	}

	/* Set SPDM version */
	(void)memset(&parameter, 0, sizeof(parameter));
	parameter.location = LIBSPDM_DATA_LOCATION_LOCAL;
	cma_spdm_version = (spdm_version_number_t)CMA_SPDM_VERSION <<
		SPDM_VERSION_NUMBER_SHIFT_BIT;
	status = libspdm_set_data(spdm_ctx, LIBSPDM_DATA_SPDM_VERSION,
				  &parameter, &cma_spdm_version,
				  sizeof(cma_spdm_version));
	assert(status == LIBSPDM_STATUS_SUCCESS);

	/* Set secured message version */
	(void)memset(&parameter, 0, sizeof(parameter));
	parameter.location = LIBSPDM_DATA_LOCATION_LOCAL;
	cma_sspdm_version = (spdm_version_number_t)CMA_SECURED_SPDM_VERSION <<
		SPDM_VERSION_NUMBER_SHIFT_BIT;
	status = libspdm_set_data(spdm_ctx, LIBSPDM_DATA_SECURED_MESSAGE_VERSION,
				  &parameter, &cma_sspdm_version,
				  sizeof(cma_sspdm_version));
	assert(status == LIBSPDM_STATUS_SUCCESS);

	/*
	 * Set GET_CAPABILITY fields
	 * Note: DataTransferSize and MaxSPDMmsgSize is automatically set by
	 * libspdm during init connection based on CMA_SPDM_SENDER_BUFFER_SIZE
	 * and CMA_SPDM_MSG_SIZE_MAX respectivelky.
	 */
	(void)memset(&parameter, 0, sizeof(parameter));
	parameter.location = LIBSPDM_DATA_LOCATION_LOCAL;
	data8 = CMA_SPDM_GET_CAPABILITY_CT_EXPONENT;
	status = libspdm_set_data(spdm_ctx, LIBSPDM_DATA_CAPABILITY_CT_EXPONENT,
				  &parameter, &data8, sizeof(data8));
	assert(status == LIBSPDM_STATUS_SUCCESS);

	/* coverity[misra_c_2012_rule_10_1_violation:SUPPRESS] */
	data32 = CMA_SPDM_GET_CAPABILITIES_REQUEST_FLAGS;
	status = libspdm_set_data(spdm_ctx, LIBSPDM_DATA_CAPABILITY_FLAGS,
				  &parameter, &data32, sizeof(data32));
	assert(status == LIBSPDM_STATUS_SUCCESS);

	/* Set NEGOTIATE_ALGORITHMS fields */
	/* coverity[misra_c_2012_rule_10_1_violation:SUPPRESS] */
	data8 = CMA_SPDM_ALGORITHMS_MEASUREMENT_SPEC;
	status = libspdm_set_data(spdm_ctx, LIBSPDM_DATA_MEASUREMENT_SPEC,
				  &parameter, &data8, sizeof(data8));
	assert(status == LIBSPDM_STATUS_SUCCESS);

	/* coverity[misra_c_2012_rule_10_1_violation:SUPPRESS] */
	data8 = CMA_SPDM_ALGORITHMS_OTHER_PARAMS_SUPPORT;
	status = libspdm_set_data(spdm_ctx, LIBSPDM_DATA_OTHER_PARAMS_SUPPORT,
				  &parameter, &data8, sizeof(data8));
	assert(status == LIBSPDM_STATUS_SUCCESS);

	/* coverity[misra_c_2012_rule_10_1_violation:SUPPRESS] */
	data32 = CMA_SPDM_ALGORITHMS_BASE_ASYM_ALGOS;
	status = libspdm_set_data(spdm_ctx, LIBSPDM_DATA_BASE_ASYM_ALGO,
				  &parameter, &data32, sizeof(data32));
	assert(status == LIBSPDM_STATUS_SUCCESS);

	/* coverity[misra_c_2012_rule_10_1_violation:SUPPRESS] */
	data32 = CMA_SPDM_ALGORITHMS_BASE_HASH_ALGOS;
	status = libspdm_set_data(spdm_ctx, LIBSPDM_DATA_BASE_HASH_ALGO,
				  &parameter, &data32, sizeof(data32));
	assert(status == LIBSPDM_STATUS_SUCCESS);

	/* coverity[misra_c_2012_rule_10_1_violation:SUPPRESS] */
	data16 = CMA_SPDM_ALGORITHMS_DHE_GROUPS;
	status = libspdm_set_data(spdm_ctx, LIBSPDM_DATA_DHE_NAME_GROUP,
				  &parameter, &data16, sizeof(data16));
	assert(status == LIBSPDM_STATUS_SUCCESS);

	/* coverity[misra_c_2012_rule_10_1_violation:SUPPRESS] */
	data16 = CMA_SPDM_ALGORITHMS_AEAD_CIPHER_SUITES;
	status = libspdm_set_data(spdm_ctx, LIBSPDM_DATA_AEAD_CIPHER_SUITE,
				  &parameter, &data16, sizeof(data16));
	assert(status == LIBSPDM_STATUS_SUCCESS);

	/* coverity[misra_c_2012_rule_10_1_violation:SUPPRESS] */
	data16 = CMA_SPDM_ALGORITHMS_KEY_SCHEDULE;
	status = libspdm_set_data(spdm_ctx, LIBSPDM_DATA_KEY_SCHEDULE,
				  &parameter, &data16, sizeof(data16));
	assert(status == LIBSPDM_STATUS_SUCCESS);

	/* coverity[misra_c_2012_rule_10_1_violation:SUPPRESS] */
	data16 = CMA_SPDM_ALGORITHMS_REQ_BASE_ASYM_ALGOS;
	status = libspdm_set_data(spdm_ctx, LIBSPDM_DATA_REQ_BASE_ASYM_ALG,
				  &parameter, &data16, sizeof(data16));
	assert(status == LIBSPDM_STATUS_SUCCESS);

	/*
	 * RMM does not maintain full certificate chain. Register function
	 * handler to skip certificate verification.
	 */
	libspdm_register_verify_spdm_cert_chain_func(spdm_ctx,
						     cma_spdm_verify_cert_chain);

	/* Assign the shared_buf. This serves as a marker that init is done. */
	info->shared_buf = (void *)params;

	return DEV_ASSIGN_STATUS_SUCCESS;
}

static unsigned long dev_assign_communicate_cmd_cmn(unsigned long func_id, uintptr_t heap)
{
	struct dev_assign_info *info = heap_start_to_dev_assign_info(heap);
	int ret;

	void *shared_buf = info->shared_buf;

	if (shared_buf == NULL) {
		ERROR("Dev_assign cmds called without init\n");
		return INT_TO_ULONG(DEV_ASSIGN_STATUS_ERROR);
	}

	/* Initialize the entry and exit args */
	info->enter_args = *(struct rmi_dev_comm_enter *)shared_buf;
	(void)memset(&info->exit_args, 0, sizeof(info->exit_args));

	switch (func_id) {
	case DEVICE_ASSIGN_APP_FUNC_ID_CONNECT_INIT:
		ret = dev_assign_cmd_init_connection_main(info);
		break;
	case DEVICE_ASSIGN_APP_FUNC_ID_SECURE_SESSION:
		ret = dev_assign_cmd_start_session_main(info);
		break;
	case DEVICE_ASSIGN_APP_FUNC_ID_STOP_CONNECTION:
		ret = dev_assign_cmd_stop_connection_main(info);
		break;
	case DEVICE_ASSIGN_APP_FUNC_ID_GET_MEASUREMENTS:
		ret = dev_assign_cmd_get_measurements_main(info);
		break;
	default:
		assert(false);
		return INT_TO_ULONG(DEV_ASSIGN_STATUS_ERROR);
	}

	/* Reset the exit flag on error */
	if (ret != 0) {
		info->exit_args.flags = 0;
	}

	/* Copy back the exit args to shared buf */
	copy_back_exit_args_to_shared(info);
	return INT_TO_ULONG(ret);
}

/* coverity[misra_c_2012_rule_5_8_violation:SUPPRESS] */
unsigned long el0_app_entry_func(
	unsigned long func_id,
	unsigned long arg_0,
	unsigned long arg_1,
	unsigned long arg_2,
	unsigned long arg_3)
{
	uintptr_t heap = (uintptr_t)get_heap_start();

	(void)arg_1;
	(void)arg_2;
	(void)arg_3;

	switch (func_id) {
	case DEVICE_ASSIGN_APP_FUNC_ID_INIT:
	{
		uintptr_t shared = (uintptr_t)get_shared_mem_start();

		return (unsigned long)dev_assign_init(heap, arg_0,
			(struct dev_assign_params *)shared);
	}
	case DEVICE_ASSIGN_APP_FUNC_ID_CONNECT_INIT:
	case DEVICE_ASSIGN_APP_FUNC_ID_SECURE_SESSION:
	case DEVICE_ASSIGN_APP_FUNC_ID_STOP_CONNECTION:
	case DEVICE_ASSIGN_APP_FUNC_ID_GET_MEASUREMENTS:
		return dev_assign_communicate_cmd_cmn(func_id, heap);
	case DEVICE_ASSIGN_APP_FUNC_SET_PUBLIC_KEY:
		return (unsigned long)dev_assign_set_pubkey(heap, arg_0);
	case DEVICE_ASSIGN_APP_FUNC_ID_DEINIT:
		return (unsigned long)dev_assign_deinit(heap);
	default:
		assert(false);
		return (unsigned long)DEV_ASSIGN_STATUS_ERROR;
	}
}
