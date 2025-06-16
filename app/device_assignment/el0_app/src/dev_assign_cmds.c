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

/* dsm_cmd_init_connection_main */
int dev_assign_cmd_init_connection_main(struct dev_assign_info *info)
{
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

	return (int)LIBSPDM_STATUS_SUCCESS;
}
