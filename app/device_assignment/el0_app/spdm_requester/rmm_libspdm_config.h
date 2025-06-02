/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef LIBSPDM_CONFIG_H
#define LIBSPDM_CONFIG_H

/* Disable FIPS 140-3 mode. */
#define LIBSPDM_FIPS_MODE 0

/* Based on RMM build type, set libspdm DEBUG flag */
#ifdef DEBUG
#define LIBSPDM_DEBUG_ENABLE 1
#else
#define LIBSPDM_DEBUG_ENABLE 0
#endif

/*
 * Setting this causes libspdm_debug_assert to call assert(0). The default
 * config uses a deadloop while(1) code.
 */
#define LIBSPDM_DEBUG_LIBSPDM_ASSERT_CONFIG 0

/*
 * For a Requester this value specifies the maximum number of entries that
 * libspdm will tolerate in a `VERSION` response before returning an error.
 */
#define LIBSPDM_MAX_VERSION_COUNT 5

/*
 * This value specifies the maximum size, in bytes, of the
 * `PSK_EXCHANGE.PSKHint` field. Although RMM disables PSK capability, this
 * macro mut be defined as libspdm_secured_message_context_t uses this macro.
 */
#define LIBSPDM_PSK_MAX_HINT_LENGTH 16

/*
 * This value specifies the maximum number of root certificates that libspdm
 * can support.
 */
#define LIBSPDM_MAX_ROOT_CERT_SUPPORT 10

/* Only one session per device is supported by RMM Specification */
#define LIBSPDM_MAX_SESSION_COUNT 1

/*
 * This value specifies the maximum size, in bytes, of a certificate chain or
 * measurements that can be stored in a libspdm context.
 */
#define LIBSPDM_MAX_CERT_CHAIN_SIZE 0x1000
#define LIBSPDM_MAX_MEASUREMENT_RECORD_SIZE 0x1000

/*
 * Partial certificates can be retrieved from a Responder and through multiple
 * messages the complete certificate chain can be constructed. This value
 * specifies the maximum size, in bytes, of a partial  certificate that can be
 * received.
 */
#define LIBSPDM_MAX_CERT_CHAIN_BLOCK_LEN 1024

/*
 * This value specifies whether libspdm will use a running calculation over the
 * transcript, where requests and responses are discarded as they are
 * cryptographically consumed, or whether libspdm will buffer the entire
 * transcript before calculating the digest or signature.
 */
#define LIBSPDM_RECORD_TRANSCRIPT_DATA_SUPPORT 0

/* This can be set to 0 for the device which does not need X509 parser. */
#define LIBSPDM_CERT_PARSE_SUPPORT 1

/*
 * Enable only the cryptography configuration that are required for SPDM
 * requester for DA. todo: Disable more cryptography configuration.
 */
#define LIBSPDM_RSA_SSA_2048_SUPPORT 1
#define LIBSPDM_RSA_SSA_3072_SUPPORT 1
#define LIBSPDM_RSA_SSA_4096_SUPPORT 1

#define LIBSPDM_RSA_PSS_2048_SUPPORT 1
#define LIBSPDM_RSA_PSS_3072_SUPPORT 1
#define LIBSPDM_RSA_PSS_4096_SUPPORT 1

#define LIBSPDM_ECDSA_P256_SUPPORT 1
#define LIBSPDM_ECDSA_P384_SUPPORT 1
#define LIBSPDM_ECDSA_P521_SUPPORT 1

#define LIBSPDM_SM2_DSA_P256_SUPPORT 0

#define LIBSPDM_EDDSA_ED25519_SUPPORT 0
#define LIBSPDM_EDDSA_ED448_SUPPORT 0

#define LIBSPDM_FFDHE_2048_SUPPORT 1
#define LIBSPDM_FFDHE_3072_SUPPORT 1
#define LIBSPDM_FFDHE_4096_SUPPORT 1

#define LIBSPDM_ECDHE_P256_SUPPORT 1
#define LIBSPDM_ECDHE_P384_SUPPORT 1
#define LIBSPDM_ECDHE_P521_SUPPORT 1

#define LIBSPDM_SM2_KEY_EXCHANGE_P256_SUPPORT 0

#define LIBSPDM_AEAD_AES_128_GCM_SUPPORT 1
#define LIBSPDM_AEAD_AES_256_GCM_SUPPORT 1

#define LIBSPDM_AEAD_CHACHA20_POLY1305_SUPPORT 1

#define LIBSPDM_AEAD_SM4_128_GCM_SUPPORT 0

#define LIBSPDM_SHA256_SUPPORT 1
#define LIBSPDM_SHA384_SUPPORT 1
#define LIBSPDM_SHA512_SUPPORT 1

#define LIBSPDM_SHA3_256_SUPPORT 0
#define LIBSPDM_SHA3_384_SUPPORT 0
#define LIBSPDM_SHA3_512_SUPPORT 0

#define LIBSPDM_SM3_256_SUPPORT 0

/* Enable only the capabilities that are required for SPDM requester for DA */
#define LIBSPDM_ENABLE_CAPABILITY_CERT_CAP 1
#define LIBSPDM_ENABLE_CAPABILITY_MEAS_CAP 1
#define LIBSPDM_ENABLE_CAPABILITY_KEY_EX_CAP 1
#define LIBSPDM_ENABLE_CAPABILITY_CHUNK_CAP 1
#define LIBSPDM_ENABLE_CAPABILITY_CHAL_CAP 1
#define LIBSPDM_ENABLE_CAPABILITY_PSK_CAP 0
#define LIBSPDM_ENABLE_CAPABILITY_HBEAT_CAP 0
#define LIBSPDM_ENABLE_CAPABILITY_MUT_AUTH_CAP 0
#define LIBSPDM_ENABLE_CAPABILITY_ENCAP_CAP 0
#define LIBSPDM_ENABLE_CAPABILITY_CSR_CAP 0
#define LIBSPDM_ENABLE_CAPABILITY_CSR_CAP_EX 0
#define LIBSPDM_ENABLE_CAPABILITY_SET_CERT_CAP 0
#define LIBSPDM_ENABLE_CAPABILITY_EVENT_CAP 0

/* Required for IDE_KM and TDISP VDM messages */
#define LIBSPDM_ENABLE_VENDOR_DEFINED_MESSAGES 1

/*
 * If 1 then endpoint supports sending GET_CERTIFICATE and GET_DIGESTS requests.
 */
#define LIBSPDM_SEND_GET_CERTIFICATE_SUPPORT 1

/* If 1 then endpoint supports sending CHALLENGE request. */
#define LIBSPDM_SEND_CHALLENGE_SUPPORT 0

/*
 * If 1 then endpoint supports sending the GET_SUPPORTED_EVENT_TYPES,
 * SUBSCRIBE_EVENT_TYPES, and encapsulated EVENT_ACK messages. In addition,
 * LIBSPDM_ENABLE_CAPABILITY_ENCAP_CAP must also be 1.
 */
#define LIBSPDM_EVENT_RECIPIENT_SUPPORT 0

/*
 * When LIBSPDM_RESPOND_IF_READY_SUPPORT is 0 then
 * - For a Requester, if the Responder sends a ResponseNotReady ERROR response
 *   then the error is immediately returned to the Integrator. The Requester
 *   cannot send a RESPOND_IF_READY request.
 * When LIBSPDM_RESPOND_IF_READY_SUPPORT is 1 then
 * - For a Requester, if the Responder sends a ResponseNotReady ERROR response
 *   then libspdm waits an amount of time, as specified by the RDTExponent
 *   parameter, before sending RESPOND_IF_READY.
 */
#define LIBSPDM_RESPOND_IF_READY_SUPPORT 1

/* Enable message logging. */
#define LIBSPDM_ENABLE_MSG_LOG 0

/* Enable libspdm configs macro checking during compilation. */
#define LIBSPDM_CHECK_MACRO 1

/* Enable checks to the SPDM context during runtime. */
#define LIBSPDM_CHECK_SPDM_CONTEXT 1

/* Enable passing the SPDM context to HAL functions. */
#define LIBSPDM_HAL_PASS_SPDM_CONTEXT 0

#endif /* LIBSPDM_CONFIG_H */
