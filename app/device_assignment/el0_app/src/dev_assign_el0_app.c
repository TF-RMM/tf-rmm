/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <app_common.h>
#include <debug.h>
#include <dev_assign_private.h>
#include <el0_app_helpers.h>
#include <mbedtls/memory_buffer_alloc.h>
#include <psa/crypto.h>
#include <psa/crypto_struct.h>
#include <string.h>

static libspdm_return_t spdm_send_message(void *spdm_context,
					      size_t request_size,
					      const void *request,
					      uint64_t timeout)
{
	(void)spdm_context;
	(void)request_size;
	(void)request;
	(void)timeout;
	return LIBSPDM_STATUS_SUCCESS;
}

static libspdm_return_t spdm_receive_message(void *spdm_context,
						 size_t *response_size,
						 void **response,
						 uint64_t timeout)
{
	(void)spdm_context;
	(void)response_size;
	(void)response;
	(void)timeout;
	return LIBSPDM_STATUS_SUCCESS;
}

static libspdm_return_t
spdm_transport_encode_message(void *spdm_context, const uint32_t *session_id,
				  bool is_app_message, bool is_request_message,
				  size_t message_size, void *message,
				  size_t *transport_message_size,
				  void **transport_message)
{
	(void)spdm_context;
	(void)session_id;
	(void)is_app_message;
	(void)is_request_message;
	(void)message_size;
	(void)message;
	(void)transport_message_size;
	(void)transport_message;
	return LIBSPDM_STATUS_SUCCESS;
}

static libspdm_return_t
spdm_transport_decode_message(void *spdm_context, uint32_t **session_id,
				  bool *is_app_message, bool is_request_message,
				  size_t transport_message_size,
				  void *transport_message,
				  size_t *message_size, void **message)
{
	(void)spdm_context;
	(void)session_id;
	(void)is_app_message;
	(void)is_request_message;
	(void)transport_message_size;
	(void)transport_message;
	(void)message_size;
	(void)message;
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
}

static libspdm_return_t spdm_acquire_receiver_buffer(void *spdm_context,
							 void **msg_buf_ptr)
{
	struct dev_assign_info *info __unused;

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

	/* Assign the shared_buf. This serves as a marker that init is done. */
	info->shared_buf = (void *)params;

	return DEV_ASSIGN_STATUS_SUCCESS;
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
	case DEVICE_ASSIGN_APP_FUNC_ID_DEINIT:
		return (unsigned long)dev_assign_deinit(heap);
	default:
		assert(false);
		return (unsigned long)DEV_ASSIGN_STATUS_ERROR;
	}
}
