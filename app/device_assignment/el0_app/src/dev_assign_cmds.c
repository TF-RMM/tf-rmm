/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <debug.h>
#include <dev_assign_private.h>
#include <string.h>

/*
 * Process the libspdm connection state. Check if the responder (DSM) supports
 * the required capabilities in the connection state
 */
static int process_spdm_init_connection(void *spdm_context)
{
	libspdm_data_parameter_t parameter;
	libspdm_return_t status;
	uint32_t data32 = 0;
	size_t data_size;

	/*
	 * Check the responder transmit buffer size. RMM retrives device
	 * certificate in parts. The maximum size of a single part is controlled
	 * by config LIBSPDM_MAX_CERT_CHAIN_BLOCK_LEN. Check if responder data
	 * transfer size is less than requester's MAX_CERT_CHAIN_BLOCK_LEN. Each
	 * part of a certificate can in turn be retrieved in CHUNKS but this
	 * requires RMM and responder to support CHUNK.
	 */
	(void)memset(&parameter, 0, sizeof(parameter));
	parameter.location = LIBSPDM_DATA_LOCATION_CONNECTION;
	data_size = sizeof(uint32_t);
	status = libspdm_get_data(spdm_context,
				  LIBSPDM_DATA_CAPABILITY_DATA_TRANSFER_SIZE,
				  &parameter, &data32, &data_size);
	if (status != LIBSPDM_STATUS_SUCCESS) {
		return DEV_ASSIGN_STATUS_ERROR;
	}

	if (data32 < (uint32_t)LIBSPDM_MAX_CERT_CHAIN_BLOCK_LEN) {
		ERROR("Responder data transfer size %d < %d\n", data32,
		      LIBSPDM_MAX_CERT_CHAIN_BLOCK_LEN);
		return DEV_ASSIGN_STATUS_ERROR;
	}

	return DEV_ASSIGN_STATUS_SUCCESS;
}

static void init_connection_cleanup(struct dev_assign_info *info, bool scrub_cert_chain_hash)
{
	libspdm_data_parameter_t parameter;

	info->spdm_cert_chain_algo = PSA_ALG_NONE;
	info->spdm_cert_chain_len = 0U;

	if (scrub_cert_chain_hash) {
		/* Clean up the CERT_CHAIN_HASH in the context */
		(void)memset(&info->spdm_cert_chain_digest, 0,
			     info->spdm_cert_chain_digest_length);

		/* Clean up the CERT_CHAIN_HASH in the connection */
		(void)memset(&parameter, 0, sizeof(parameter));
		parameter.location = LIBSPDM_DATA_LOCATION_CONNECTION;
		parameter.additional_data[0] = info->cert_slot_id;
		(void)libspdm_set_data(info->libspdm_ctx,
				       LIBSPDM_DATA_PEER_USED_CERT_CHAIN_HASH,
				       &parameter, &info->spdm_cert_chain_digest,
				       info->spdm_cert_chain_digest_length);
		info->spdm_cert_chain_digest_length = 0;
	}
}

/* dev_assign_cmd_init_connection_main */
/* cppcheck-suppress misra-c2012-8.7 */
int dev_assign_cmd_init_connection_main(struct dev_assign_info *info)
{
	size_t cert_chain_size;
	libspdm_data_parameter_t parameter;
	void *spdm_context = info->libspdm_ctx;
	libspdm_return_t status;

	assert(spdm_context != NULL);

	/*
	 * Below are list of SPDM requester commands send to the device to
	 * init connection and get certificate. These commands will result in
	 * multiple async IO from libspdm layer which will yield the app.
	 */

	/*
	 * Initialize the connection. This does GET_VERSION, GET_CAPABILITIES
	 * NEGOTIATE_ALGORITHMS
	 */
	status = libspdm_init_connection(spdm_context, false);
	if (status != LIBSPDM_STATUS_SUCCESS) {
		return DEV_ASSIGN_STATUS_ERROR;
	}

	if (process_spdm_init_connection(spdm_context) !=
			DEV_ASSIGN_STATUS_SUCCESS) {
		return DEV_ASSIGN_STATUS_ERROR;
	}

	/*
	 * Get device certificate. The certificate is not kept in RMM instead
	 * RMM retrieves the certificates in parts and asks the NS Host to
	 * cache the certificate during retrieval. Due to this the buffer
	 * allocated to cache the certificate chain is not known to RMM. So set
	 * cert_chain_size to the max value limited by SPDM spec which is 64kb.
	 */
	cert_chain_size = SPDM_MAX_CERTIFICATE_CHAIN_SIZE;
	status = libspdm_get_certificate(spdm_context,
					 NULL, /* session_id */
					 info->cert_slot_id,
					 &cert_chain_size,
					 NULL /* cert_chain */);
	if (status != LIBSPDM_STATUS_SUCCESS) {
		init_connection_cleanup(info, false);
		return DEV_ASSIGN_STATUS_ERROR;
	}

	/*
	 * Set libspdm data LIBSPDM_DATA_PEER_USED_CERT_CHAIN_HASH.
	 * As part of the certificate retrieval, RMM calculates the
	 * spdm_cert_chain digest based on the SPDM negotiated hash algorithm.
	 * This should be completed at this point and update the same to libspdm
	 * context.
	 */
	assert(info->spdm_cert_chain_digest_length != 0U);
	(void)memset(&parameter, 0, sizeof(parameter));
	parameter.location = LIBSPDM_DATA_LOCATION_CONNECTION;
	parameter.additional_data[0] = info->cert_slot_id;
	status = libspdm_set_data(spdm_context,
				  LIBSPDM_DATA_PEER_USED_CERT_CHAIN_HASH,
				  &parameter, &info->spdm_cert_chain_digest,
				  info->spdm_cert_chain_digest_length);

	if (status != LIBSPDM_STATUS_SUCCESS) {
		init_connection_cleanup(info, false);
		return DEV_ASSIGN_STATUS_ERROR;
	}

	return (int)LIBSPDM_STATUS_SUCCESS;
}

/* dev_assign_cmd_start_session_main */
/* cppcheck-suppress misra-c2012-8.7 */
int dev_assign_cmd_start_session_main(struct dev_assign_info *info)
{
	uint32_t session_id = 0U;
	libspdm_return_t status;

	/*
	 * Call libspdm_challenge() as it helps to validate spdm_cert_chain_hash
	 * and public key before key_exchange call. Useful for debugging.
	 */
#if LOG_LEVEL >= LOG_LEVEL_VERBOSE
	status = libspdm_challenge(info->libspdm_ctx, NULL, 0,
			SPDM_CHALLENGE_REQUEST_NO_MEASUREMENT_SUMMARY_HASH,
				NULL, NULL);
	VERBOSE("libspdm_challenge: 0x%x\n", status);
	if (status != LIBSPDM_STATUS_SUCCESS) {
		return DEV_ASSIGN_STATUS_ERROR;
	}
#endif

	/*
	 * Start SPDM session. Set session policy to 0, this terminates the
	 * session upon device firmware or configuration update.
	 */
	status = libspdm_start_session(info->libspdm_ctx,
				       false, /* use_psk */
				       NULL, /* psk_hint */
				       0, /* psk_hint size */
	       SPDM_REQUEST_NO_MEASUREMENT_SUMMARY_HASH, /* meas hash type */
				       info->cert_slot_id, /* slot id */
				       0, /* session policy */
				       &session_id,
				       NULL, /* hbeat period */
				       NULL /* measurement_hash */);
	if (status != LIBSPDM_STATUS_SUCCESS) {
		ERROR("Creating secure session failed with status 0x%x\n", status);
		return DEV_ASSIGN_STATUS_ERROR;
	}

	info->session_id = session_id;
	VERBOSE("SPDM secure session id: 0x%x\n", info->session_id);

	/* If DSM has IDE, do IDE key programming to RootPort and at EndPoint */
	if (info->has_ide) {
		status = dev_assign_ide_setup(info);
		if (status != LIBSPDM_STATUS_SUCCESS) {
			ERROR("IDE setup failed with status 0x%x for session id %u\n",
				status, session_id);
			return DEV_ASSIGN_STATUS_ERROR;
		}
		info->ide_active = true;
	}

	return DEV_ASSIGN_STATUS_SUCCESS;
}

static libspdm_return_t get_measurements(
	struct dev_assign_info *info,
	uint8_t measurement_operation,
	uint8_t request_attribute)
{
	uint32_t meas_length;
	uint8_t number_of_blocks;

	/*
	 * RMM does not store measurement response in CMA SPDM context, instead
	 * the content is cached by NS host and a digest is computed by RMM.
	 * Limit the max meas_length to be 4096 bytes, this can be removed once
	 * CHUNK support is enabled.
	 */
	meas_length = LIBSPDM_MAX_MEASUREMENT_RECORD_SIZE;

	/*
	 * Request measurement(s). The output values of meas_length and number
	 * of blocks and the actual measurement records are ignored as RMM does
	 * not have a copy of the measurements. As part of get_measurements
	 * callback RMM inform the Host to cache measurements.
	 */
	return libspdm_get_measurement_ex(info->libspdm_ctx,
					  &info->session_id, /* session_id */
					  request_attribute, /* request_attribute */
					  measurement_operation,
					  info->cert_slot_id, /* slot id */
					  NULL, /* content_changed */
					  &number_of_blocks,
					  &meas_length,
					  NULL, /* measurement_record */
					  info->dev_assign_op_params.meas_params.nonce,
					  NULL, /* requester_nonce */
					  NULL, /* responder_nonce */
					  NULL, /* opaque_data */
					  NULL);  /* opaque_data_size */
}

/* cppcheck-suppress misra-c2012-8.7 */
/* dev_assign_cmd_get_measurements_main */
int dev_assign_cmd_get_measurements_main(struct dev_assign_info *info)
{
	libspdm_return_t status;
	uint8_t request_attribute = 0U;

	assert(info->dev_assign_op_params.param_type == DEV_ASSIGN_OP_PARAMS_MEAS);

	if (info->dev_assign_op_params.meas_params.sign) {
		request_attribute |=
			(uint8_t)SPDM_GET_MEASUREMENTS_REQUEST_ATTRIBUTES_GENERATE_SIGNATURE;
	}

	if (info->dev_assign_op_params.meas_params.raw) {
		request_attribute |=
			(uint8_t)SPDM_GET_MEASUREMENTS_REQUEST_ATTRIBUTES_RAW_BIT_STREAM_REQUESTED;
	}

	/* cppcheck-suppress misra-c2012-7.3 */
	if (info->dev_assign_op_params.meas_params.all) {
		/* Request all measurements. */
		status = get_measurements(info, 0xFFU, request_attribute);

		if (status != LIBSPDM_STATUS_SUCCESS) {
			return DEV_ASSIGN_STATUS_ERROR;
		}
	} else {
		for (size_t i = 0U; i < RDEV_MEAS_PARAM_INDICES_LEN; ++i) {
			for (size_t j = 0U; j < BITS_PER_UCHAR; ++j) {
				if ((info->dev_assign_op_params.meas_params.indices[i] &
				     (unsigned char)(1U << j)) != 0U) {
					size_t index = (i * BITS_PER_UCHAR) + j;

					/*
					 * The lowest and highest indices are
					 * reserved by specification
					 */
					assert((index != 0U) && (index != 255U));

					/* Request a single measurement. */
					status = get_measurements(
						info, (uint8_t)index, request_attribute);
					if (status != LIBSPDM_STATUS_SUCCESS) {
						return DEV_ASSIGN_STATUS_ERROR;
					}
				}
			}
		}
	}

	if (status != LIBSPDM_STATUS_SUCCESS) {
		return DEV_ASSIGN_STATUS_ERROR;
	}

	return DEV_ASSIGN_STATUS_SUCCESS;
}

/* dev_assign_cmd_stop_connection_main */
/* cppcheck-suppress misra-c2012-8.7 */
int dev_assign_cmd_stop_connection_main(struct dev_assign_info *info)
{
	int rc = DEV_ASSIGN_STATUS_SUCCESS;
	libspdm_return_t status;

	/* Stop IDE at RootPort and Endpoint */
	if (info->ide_active) {
		status = dev_assing_ide_teardown(info);
		if (status != LIBSPDM_STATUS_SUCCESS) {
			ERROR("IDE STOP failed with status 0x%x\n", status);
		} else {
			INFO("IDE Stop completed: 0x%x\n", status);
		}
	}

	if (info->session_id != 0U) {
		/* Terminate the connection. This closes the secure session */
		status = libspdm_stop_session(info->libspdm_ctx,
					      info->session_id,
					      0 /* end_session_attributes */);

		if (status != LIBSPDM_STATUS_SUCCESS) {
			ERROR("SPDM_END_SESSION failed: 0x%x\n", status);
			rc = DEV_ASSIGN_STATUS_ERROR;
			/*assert(false);*/
		} else {
			INFO("SPDM_END_SESSION completed: 0x%x\n", status);
			info->session_id = 0U;
		}
	}

	/* Send GET_VERSION, this resets the SPDM connection */
	(void)libspdm_init_connection(info->libspdm_ctx, true);

	/*
	 * Unset public key context in libspdm connection once the connection is
	 * terminated.
	 */
	dev_assign_unset_pubkey(info);

	/* Clean up the cma spdm connection state */
	init_connection_cleanup(info, true);

	return rc;
}
