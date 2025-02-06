/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <app_common.h>
#include <arch.h>
#include <arch_features.h>
#include <assert.h>
#include <attest_measurement.h>
#include <attestation.h>
#include <attestation_token.h>
#include <el0_app_helpers.h>
#include <errno.h>
#include <mbedtls/memory_buffer_alloc.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

/*
 * The heap buffer size used by the Mbed TLS allocator is calculated so that
 * attest_heap_t has the same size as HEAP_PAGE_COUNT * GRANULE_SIZE
 * fills the memory
 */
#define MBEDTLS_HEAP_BUF_SIZE				\
	((HEAP_PAGE_COUNT * GRANULE_SIZE) -		\
		(sizeof(buffer_alloc_ctx) +		\
		 sizeof(struct token_sign_cntxt) +	\
		 REC_ATTEST_TOKEN_BUF_SIZE +		\
		 RMM_REALM_TOKEN_BUF_SIZE +		\
		 sizeof(size_t)))

/* The following static variables are common for all attest app instances */
static bool attest_key_init_done;

/*
 * Variables that need to be allocated in the heap buffer
 * (Must be declared in struct attest_heap_t):
 */
struct attest_heap_t {
	/*
	 * Variables that are not dynamically allocated, but need to be kept
	 * local to app instance.
	 */
	struct token_sign_cntxt token_sign_context;
	uint8_t cca_attest_token_buf[REC_ATTEST_TOKEN_BUF_SIZE];
	/* The realm token is never returned to RMM only used inside the app */
	uint8_t realm_attest_token_buf[RMM_REALM_TOKEN_BUF_SIZE];
	size_t realm_token_len;
	/* The actual heap buffer */
	unsigned char mbedtls_heap_buf[MBEDTLS_HEAP_BUF_SIZE] __aligned(sizeof(unsigned long));
};
COMPILER_ASSERT(sizeof(struct attest_heap_t) == (HEAP_PAGE_COUNT * GRANULE_SIZE));

/* Make sure that the buffer used by the allocator is aligned */
COMPILER_ASSERT((UL(offsetof(struct attest_heap_t, mbedtls_heap_buf)) % sizeof(unsigned long)) == 0U);

/*
 * This function is used by Mbed TLS as a source of entropy. This means it is
 * called during RMM operation, to add entropy to the signing process.
 * See declaration in ext/mbedtls/include/psa/crypto_extra.h.
 * For details see `MBEDTLS_PSA_CRYPTO_EXTERNAL_RNG` in mbedtls/mbedtls_config.h
 */
/* coverity[misra_c_2012_rule_8_7_violation:SUPPRESS] */
psa_status_t mbedtls_psa_external_get_random(
	mbedtls_psa_external_random_context_t *context,
	uint8_t *output, size_t output_size, size_t *output_length)
{
	unsigned long ret;

	assert(output_size <= get_shared_mem_size());
	ret = el0_app_service_call(APP_SERVICE_RANDOM,
				   output_size, 0, 0, 0);

	(void)context;

	if (ret != 0U) {
		return PSA_ERROR_HARDWARE_FAILURE;
	}

	(void)memcpy((void *)output, get_shared_mem_start(), output_size);
	*output_length = output_size;

	return PSA_SUCCESS;
}

static unsigned long app_global_init(void)
{
	int ret;
	psa_status_t psa_status;
	struct attest_heap_t *heap = (struct attest_heap_t *)get_heap_start();

	mbedtls_memory_buffer_alloc_init(heap->mem_buf, sizeof(heap->mem_buf));
	psa_status = psa_crypto_init();
	if (psa_status != PSA_SUCCESS) {
		return (unsigned long)(-EINVAL);
	}

	/*
	 * Set the number of max operations per ECC signing iteration to the
	 * configured value.
	 *
	 * This adjusts the length of a single signing loop.
	 */
	psa_interruptible_set_max_ops(MBEDTLS_ECP_MAX_OPS);

	ret = attestation_init();
	if (ret != 0) {
		return (unsigned long)(long)ret;
	}

	attest_key_init_done = true;

	return 0UL;
}

static unsigned long do_token_creation(void)
{
	heap->token_sign_context.ctx.completed_token_len =
		attest_cca_token_create(&heap->token_sign_context,
			heap->cca_attest_token_buf,
			sizeof(heap->cca_attest_token_buf),
			heap->realm_attest_token_buf,
			heap->realm_token_len);
	return heap->token_sign_context.ctx.completed_token_len;
}

static size_t copy_attest_token_to_shared(size_t offset, size_t len)
{
	struct attest_heap_t *heap = (struct attest_heap_t *)get_heap_start();

	if ((len >= GRANULE_SIZE) ||
		(offset > heap->token_sign_context.ctx.completed_token_len) ||
		((offset + len) > heap->token_sign_context.ctx.completed_token_len)) {
		return 0;
	}
	(void)memcpy(get_shared_mem_start(), (void *)&heap->cca_attest_token_buf[offset], len);
	return len;
}

static long token_context_init(void)
{
	struct attest_heap_t *heap = (struct attest_heap_t *)get_heap_start();

	heap->realm_token_len = 0;
	mbedtls_memory_buffer_alloc_init(heap->mbedtls_heap_buf, sizeof(heap->mbedtls_heap_buf));
	return attest_token_ctx_init(&heap->token_sign_context);
}

static void *get_realm_token_create_params(void)
{
	return get_shared_mem_start();
}

static unsigned long realm_token_create(enum hash_algo algorithm)
{

	struct attest_realm_token_create_params *params =
		get_realm_token_create_params();
	struct attest_heap_t *heap = (struct attest_heap_t *)get_heap_start();

	/* coverity[misra_c_2012_directive_4_7_violation:SUPPRESS] */
	return (unsigned long)attest_realm_token_create(algorithm,
			     params->measurements,
			     MEASUREMENT_SLOT_NR,
			     &(params->rpv),
			     RPV_SIZE,
			     &(params->challenge),
			     ATTEST_CHALLENGE_SIZE,
			     &heap->token_sign_context,
			     heap->realm_attest_token_buf,
			     sizeof(heap->realm_attest_token_buf));
}

/* coverity[misra_c_2012_rule_5_8_violation:SUPPRESS] */
unsigned long el0_app_entry_func(
	unsigned long func_id,
	unsigned long arg_0,
	unsigned long arg_1,
	unsigned long arg_2,
	unsigned long arg_3)
{
	enum attest_token_err_t token_ret;
	struct attest_heap_t *heap = (struct attest_heap_t *)get_heap_start();
	void *shared = get_shared_mem_start();

	(void)arg_2;
	(void)arg_3;

	switch (func_id) {
	case ATTESTATION_APP_FUNC_ID_GLOBAL_INIT:
		return app_global_init();
	case ATTESTATION_APP_FUNC_ID_DO_HASH:
		return app_do_hash((enum hash_algo)arg_0, arg_1, (uint8_t *)shared);
	case ATTESTATION_APP_FUNC_ID_EXTEND_MEASUREMENT:
		return app_do_extend((enum hash_algo)arg_0, arg_1, (uint8_t *)shared);
	case ATTESTATION_APP_FUNC_ID_TOKEN_SIGN:
		/* coverity[misra_c_2012_directive_4_7_violation:SUPPRESS] */
		token_ret = attest_realm_token_sign(
			&heap->token_sign_context, &heap->realm_token_len);
		*((size_t *)get_shared_mem_start()) = heap->realm_token_len;
		return (unsigned long)token_ret;
	case ATTESTATION_APP_FUNC_ID_DO_CCA_TOKEN_CREATION:
		/* coverity[misra_c_2012_directive_4_7_violation:SUPPRESS] */
		return do_token_creation();
	case ATTESTATION_APP_FUNC_ID_COPY_ATTEST_TOKEN_TO_SHARED:
		return copy_attest_token_to_shared(arg_0, arg_1);
	case ATTESTATION_APP_FUNC_ID_TOKEN_CTX_INIT:
		if (!attest_key_init_done) {
			return (unsigned long)ATTEST_TOKEN_ERR_INVALID_STATE;
		}
		return token_context_init();
	case ATTESTATION_APP_FUNC_ID_REALM_TOKEN_CREATE:
		return realm_token_create((enum hash_algo)arg_0);
	default:
		assert(false);
		return 0;
	}
}
