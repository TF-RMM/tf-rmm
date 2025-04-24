/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef DEV_ASSIGN_PRIVATE_H
#define DEV_ASSIGN_PRIVATE_H

#include <assert.h>
#include <dev_assign_structs.h>
#include <industry_standard/spdm.h>
#include <industry_standard/spdm_secured_message.h>
#include <library/spdm_requester_lib.h>
#include <library/spdm_secured_message_lib.h>
#include <mbedtls/memory_buffer_alloc.h>
#include <psa/crypto.h>
#include <sizes.h>
#include <utils_def.h>

/*
 * Requester SPDM version is 1.2. This is the minimum SPDM version required to
 * support TDISP.
 *
 * From PCIe spec: CMA requires SPDM Version 1.0 or above. IDE requires SPDM
 * Version 1.1 or above. TDISP requires version 1.2 or above.
 */
#define CMA_SPDM_VERSION		SPDM_MESSAGE_VERSION_12

/*
 * Secured Messages using SPDM Specification (IDE requires version 1.0 or above)
 * Set this to 1.1. DSM supports 1.1
 */
#define CMA_SECURED_SPDM_VERSION	SECURED_SPDM_VERSION_11

/*
 * Responders must implement a Cryptographic Timeout (CT), as defined by SPDM
 * specification, of not more than 2^23 μs.
 */
#define CMA_SPDM_GET_CAPABILITY_CT_EXPONENT		20

/*
 * List of capabilities enabled and supported by SPDM requester. These flags are
 * passed to GET_CAPABILITIES request message. Currently these flags are specific
 * to PCIe TDI off-chip device.
 *
 * CERT_CAP	- Supports DIGESTS and CERTIFICATE response messages.
 * ENCRYPT_CAP	- Supports message encryption in a secure session.
 * KEY_EX_CAP	- Support KEY_EXCHANGE request message. Needs ENCRYPT_CAP and
 *		  MAC_CAP.
 * MAC_CAP	- Supports message authentication in a secure session.
 * CHUNK_CAP	- Supports large SPDM message transfer mechanism messages.
 *		  Note: Add SPDM_GET_CAPABILITIES_REQUEST_FLAGS_CHUNK_CAP.
 *			CHUNK retrieval is not verified.
 */
#define CMA_SPDM_GET_CAPABILITIES_REQUEST_FLAGS				( \
	SPDM_GET_CAPABILITIES_REQUEST_FLAGS_CERT_CAP			| \
	SPDM_GET_CAPABILITIES_REQUEST_FLAGS_ENCRYPT_CAP			| \
	SPDM_GET_CAPABILITIES_REQUEST_FLAGS_MAC_CAP			| \
	SPDM_GET_CAPABILITIES_REQUEST_FLAGS_KEY_EX_CAP			| \
	SPDM_GET_CAPABILITIES_REQUEST_FLAGS_HANDSHAKE_IN_THE_CLEAR_CAP)

/*
 * List of minimum set of capabilities required to be supported by the responder.
 * These flags are checked against CAPABILITIES response message. Currently these
 * flags are specific to PCIe TDI off-chip device.
 */
#define CMA_SPDM_GET_CAPABILITIES_RESPONSE_FLAGS			( \
	SPDM_GET_CAPABILITIES_RESPONSE_FLAGS_CERT_CAP			| \
	SPDM_GET_CAPABILITIES_RESPONSE_FLAGS_ENCRYPT_CAP		| \
	SPDM_GET_CAPABILITIES_RESPONSE_FLAGS_MAC_CAP			| \
	SPDM_GET_CAPABILITIES_RESPONSE_FLAGS_MEAS_CAP			| \
	SPDM_GET_CAPABILITIES_RESPONSE_FLAGS_KEY_EX_CAP)

/*
 * Optional set of capabilities that can be supported by the responder. These
 * flags are checked against CAPABILITIES response message.
 */
#define CMA_SPDM_GET_CAPABILITIES_RESPONSE_OPTIONAL_FLAGS		( \
	SPDM_GET_CAPABILITIES_RESPONSE_FLAGS_MEAS_FRESH_CAP		| \
	SPDM_GET_CAPABILITIES_RESPONSE_FLAGS_CHUNK_CAP)

/*
 * The measurement specification is used in the MEASUREMENTS response. This is
 * not explicitly mentioned in PCIe CMA-SPDM.
 */
#define CMA_SPDM_ALGORITHMS_MEASUREMENT_SPEC				\
	SPDM_MEASUREMENT_SPECIFICATION_DMTF

/*
 * OtherParamsSupport: Opaque data format used is DMTF. This is not explicitly
 * mentioned in PCIe CMA-SPDM.
 */
#define CMA_SPDM_ALGORITHMS_OTHER_PARAMS_SUPPORT			\
	SPDM_ALGORITHMS_OPAQUE_DATA_FORMAT_1

/*
 * Requesters are required to support responders that implement any of these
 * choices of BaseAsymAlgo:
 *	TPM_ALG_RSASSA_3072
 *	TPM_ALG_ECDSA_ECC_NIST_P256
 *	TPM_ALG_ECDSA_ECC_NIST_P384
 */
#define CMA_SPDM_ALGORITHMS_BASE_ASYM_ALGOS				( \
	SPDM_ALGORITHMS_BASE_ASYM_ALGO_TPM_ALG_RSASSA_3072		| \
	SPDM_ALGORITHMS_BASE_ASYM_ALGO_TPM_ALG_ECDSA_ECC_NIST_P256	| \
	SPDM_ALGORITHMS_BASE_ASYM_ALGO_TPM_ALG_ECDSA_ECC_NIST_P384)

/*
 * Requesters and responders must, for MeasurementHashAlgo, support one or both
 * of the following:
 *	TPM_ALG_SHA_256
 *	TPM_ALG_SHA_384
 */
#define CMA_SPDM_ALGORITHMS_BASE_HASH_ALGOS				( \
	SPDM_ALGORITHMS_BASE_HASH_ALGO_TPM_ALG_SHA_256			| \
	SPDM_ALGORITHMS_BASE_HASH_ALGO_TPM_ALG_SHA_384)

/*
 * Requester are required to responders that implement any of these DHE groups
 *	SECP_256_R1
 *	SECP_384_R1
 */
#define CMA_SPDM_ALGORITHMS_DHE_GROUPS					( \
	SPDM_ALGORITHMS_DHE_NAMED_GROUP_SECP_256_R1			| \
	SPDM_ALGORITHMS_DHE_NAMED_GROUP_SECP_384_R1)

/*
 * Requester are required to responders that implement any of these AEAD Cipher
 * Suite
 *	AES-128-GCM
 *	AES-256-GCM
 */
#define CMA_SPDM_ALGORITHMS_AEAD_CIPHER_SUITES				( \
	SPDM_ALGORITHMS_AEAD_CIPHER_SUITE_AES_128_GCM			| \
	SPDM_ALGORITHMS_AEAD_CIPHER_SUITE_AES_256_GCM)

/* Requester-supported SPDM-enumerated Key Schedule algorithms. */
#define CMA_SPDM_ALGORITHMS_KEY_SCHEDULE				\
	SPDM_ALGORITHMS_KEY_SCHEDULE_HMAC_HASH

/*
 * Requesters supported asym algorithm.
 *	TPM_ALG_RSAPSS_3072
 *	TPM_ALG_RSAPSS_2048
 *	TPM_ALG_RSASSA_3072
 *	TPM_ALG_RSASSA_2048
 */
#define CMA_SPDM_ALGORITHMS_REQ_BASE_ASYM_ALGOS				( \
	SPDM_ALGORITHMS_BASE_ASYM_ALGO_TPM_ALG_RSAPSS_3072		| \
	SPDM_ALGORITHMS_BASE_ASYM_ALGO_TPM_ALG_RSAPSS_2048		| \
	SPDM_ALGORITHMS_BASE_ASYM_ALGO_TPM_ALG_RSASSA_3072		| \
	SPDM_ALGORITHMS_BASE_ASYM_ALGO_TPM_ALG_RSASSA_2048)

/*
 * SPDM GET_CAPABILITIES.DataTransferSize
 *
 * This is the size of send/receive buffer that is registered with libspdm to
 * write device request and read device response. RMM uses the same buffer for
 * both send and receive as only one device request can be active at a time.
 *
 * RMM spec limits the response (recv) length to GRANULE_SIZE. And so the send
 * buffer size is also limited to GRANULE_SIZE. This value is set as SPDM
 * requester GET_CAPABILITIES.DataTransferSize as part of connection init.
 *
 * Note: Increasing CMA_DATA_TRANSFER_SIZE increases
 * PRIV_DATA_LIBSPMD_SCRATCH_BUFFER_SIZE.
 */
#define CMA_DATA_TRANSFER_SIZE		GRANULE_SIZE
#define CMA_SENDER_BUFFER_SIZE		CMA_DATA_TRANSFER_SIZE
#define CMA_RECEIVER_BUFFER_SIZE	CMA_DATA_TRANSFER_SIZE

/*
 * SPDM GET_CAPABILITIES.MaxSPDMmsgSize
 *
 * If the Requester supports the Large SPDM message transfer mechanism this
 * field shall indicate the maximum size, in bytes, of the internal buffer used
 * to reassemble a single and complete Large SPDM message.
 *
 * Currently this is set as the same value of CMA_DATA_TRANSFER_SIZE. This value
 * is set as SPDM requester GET_CAPABILITIES.MaxSPDMmsgSize as part of connection
 * init.
 *
 * This could be later incremented once SPDM CHUNK support is enabled and tested.
 */
#define CMA_MAX_SPDM_MSG_SIZE		CMA_DATA_TRANSFER_SIZE

/*
 * List of data objects mapped in heap prefixed by PRIV_
 *
 * PRIV_LIBSPDM_SEND_RECV_BUF_SIZE:
 *	This is buffer to send and receive SPDM data. Must be allocated first on
 *	heap as this shared with RMM stub and accessed by RMM.
 *
 * PRIV_LIBSPDM_CONTEXT_SIZE:
 *	Libspdm public headers do not export the type of libsdpm_context. Reserve
 *	2*4K pages and check at runtime if context size are within limit using
 *	libspdm_get_context_size() api.
 *
 * PRIV_LIBSPDM_SCRATCH_BUF_SIZE:
 *	This is an internal buffer used by libspdm as scratch space. This is
 *	approx 6 times of CMA_DATA_TRANSFER_SIZE. As part of init connection
 *	there is a run time check to verify if enough scratch space is reserved.
 *
 * PRIV_LIBSPDM_MBEDTLS_HEAP_SIZE
 *	This is the heap used by Libspdm MbedTLS library.
 */
#define PRIV_LIBSPDM_SEND_RECV_BUF_SIZE		sizeof(struct dev_assign_spdm_shared)
#define PRIV_LIBSPDM_CONTEXT_SIZE		(2U * SZ_4K)
#define PRIV_LIBSPDM_SCRATCH_BUF_SIZE		(6U * CMA_DATA_TRANSFER_SIZE)
#define PRIV_LIBSPDM_MBEDTLS_HEAP_SIZE		(3U * SZ_4K)

/* Custom libspdm status code. Wait for device response  */
#define LIBSPDM_STATUS_DEV_COMM_BLOCKED		((libspdm_return_t)0x80008000U)

#define spdm_to_dev_assign_info(spdm)					\
		((struct dev_assign_info *)((unsigned long)(spdm) +	\
		PRIV_LIBSPDM_CONTEXT_SIZE))

#define heap_start_to_dev_assign_info(heap)				\
				((struct dev_assign_info *)((heap) +	\
				PRIV_LIBSPDM_SEND_RECV_BUF_SIZE +	\
				PRIV_LIBSPDM_SCRATCH_BUF_SIZE +		\
				PRIV_LIBSPDM_MBEDTLS_HEAP_SIZE +	\
				PRIV_LIBSPDM_CONTEXT_SIZE))

struct dev_assign_info {
	/* RMI device handle */
	void *dev_handle;

	/* SPDM certificate slot ID */
	uint8_t cert_slot_id;

	bool has_ide;

	/* Identify the root complex (RC). */
	uint64_t ecam_addr;

	/* Identify the RP within the RC. RootPort PCI BDF */
	uint16_t rp_id;

	/* IDE stream ID */
	uint64_t ide_sid;

	buffer_alloc_ctx mbedtls_heap_ctx;

	/* Exit and Entry args for dev_communicate cmds */
	struct rmi_dev_comm_enter enter_args;
	struct rmi_dev_comm_exit exit_args;

	/*
	 * The PSA equivalent of the 'rmi_hash_algo'. This value is used by PSA
	 * crypto calls to calculate hash of cached device objects.
	 */
	psa_algorithm_t psa_hash_algo;

	void *send_recv_buffer;
	void *scratch_buffer;
	void *mbedtls_heap_buf;
	void *libspdm_ctx;

	void *shared_buf;
};

int dev_assign_cmd_init_connection_main(struct dev_assign_info *info);

#endif /* DEV_ASSIGN_PRIVATE_H */
