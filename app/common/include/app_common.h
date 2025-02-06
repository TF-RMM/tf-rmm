/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef APP_COMMON_H
#define APP_COMMON_H

#ifndef __ASSEMBLER__
#include <stddef.h>
#include <stdint.h>
#endif /* __ASSEMBLER__ */
#include <utils_def.h>

/* The heap properties are encoded in a single unsigned long.
 * It is assumed that the heap_va is granule aligned, so at
 * least the lower 12 bits are always zero.
 */
#define HEAP_PAGE_COUNT_MASK ((1UL << 12U) - 1UL)
#define HEAP_VA_MASK (~HEAP_PAGE_COUNT_MASK)

#define APP_EXIT_CALL		UL(23)
#define APP_SERVICE_CALL	UL(47)

#define APP_SERVICE_COUNT			16U
#define APP_SERVICE_PRINT			2U
#define APP_SERVICE_RANDOM			3U
#define APP_SERVICE_GET_REALM_ATTESTATION_KEY	4U
#define APP_SERVICE_GET_PLATFORM_TOKEN		5U
#define APP_SERVICE_GET_REALM_ATTEST_PUB_KEY_FROM_EL3	6U
#define APP_SERVICE_EL3_TOKEN_SIGN_QUEUE_TRY_ENQUEUE	7U
#define APP_SERVICE_EL3_IFC_EL3_TOKEN_SIGN_SUPPORTED	8U

#ifndef __ASSEMBLER__

struct service_get_realm_attestation_key_struct {
	size_t attest_key_buf_size;
	uint8_t attest_key_buf[GRANULE_SIZE - 8U];
};
COMPILER_ASSERT(sizeof(struct service_get_realm_attestation_key_struct) == GRANULE_SIZE);

struct service_get_realm_attestation_pub_key_struct {
	size_t attest_pub_key_buf_size;
	uint8_t attest_pub_key_buf[GRANULE_SIZE - 8U];
};
COMPILER_ASSERT(sizeof(struct service_get_realm_attestation_pub_key_struct) == GRANULE_SIZE);

struct service_get_platform_token_struct {
	size_t token_hunk_len;
	size_t remaining_len;
	uint8_t token_hunk_buf[GRANULE_SIZE - 16U];
};
COMPILER_ASSERT(sizeof(struct service_get_platform_token_struct) == GRANULE_SIZE);

#if ATTEST_EL3_TOKEN_SIGN
struct service_el3_token_sign_request {
	uint64_t cookie;
	uint64_t ticket;
	size_t hash_buf_len;
	uint8_t hash_buf[GRANULE_SIZE - 24U];
};
COMPILER_ASSERT(sizeof(struct service_el3_token_sign_request) == GRANULE_SIZE);

#endif

#endif /* __ASSEMBLER__ */
#endif /* APP_COMMON_H */
