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

/* dev_assign_cmd_stop_connection_main */
int dev_assign_cmd_stop_connection_main(struct dev_assign_info *info)
{
	/* Send GET_VERSION, this resets the SPDM connection */
	(void)libspdm_init_connection(info->libspdm_ctx, true);

	/*
	 * Unset public key context in libspdm connection once the connection is
	 * terminated.
	 */
	dev_assign_unset_pubkey(info);

	/* Clean up the cma spdm connection state */
	init_connection_cleanup(info, true);

	return DEV_ASSIGN_STATUS_SUCCESS;
}
