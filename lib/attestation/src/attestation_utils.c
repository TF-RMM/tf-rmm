/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <assert.h>
#include <attestation.h>
#include <attestation_priv.h>
#include <debug.h>
#include <errno.h>
#include <mbedtls/memory_buffer_alloc.h>
#include <memory_alloc.h>
#include <psa/crypto.h>
#include <simd.h>
#include <sizes.h>

/*
 * Memory buffer for the allocator during key initialization.
 *
 * Used to compute the public key and set up a PRNG object per CPU. PRNGs are
 * needed for key blinding during EC signing.
 *
 * Memory requirements:
 * +------------------------+-------+-------------------------+
 * |                        |  MAX  |  Persisting allocation  |
 * +------------------------+-------+-------------------------+
 * | Public key computation |  2.9K |         0.1K            |
 * +------------------------+-------+-------------------------+
 * | one SHA256 HMAC_DRBG   |       |                         |
 * |   buffer               |  364B |         364B            |
 * |                        |       |                         |
 * | PRNG setup for 32 CPUs |  12K  |        11.6K            |
 * +------------------------+-------+-------------------------+
 *
 * Measured with eg:
 *	src/lib/memory_buffer_alloc.c: mbedtls_memory_buffer_alloc_status()
 *
 * Reserve enough space for the temporary PRNG and per-CPU ones (see
 * attest_rnd_prng_init()), plus more space for other allocations.
 */
#define PRNG_INIT_HEAP_SIZE	((MAX_CPUS + 1UL) * 364UL)
#define MISC_PER_CPU		(SZ_4K / 16U)
#define INIT_HEAP_SIZE		(PRNG_INIT_HEAP_SIZE + (MISC_PER_CPU * MAX_CPUS))

static unsigned char mem_buf[INIT_HEAP_SIZE]
					__aligned(sizeof(unsigned long));

static bool attest_initialized;

static struct buffer_alloc_ctx init_ctx;

int attestation_init(void)
{
	int ret;
	psa_status_t psa_status;

	/* Enable Data Independent Timing feature */
	write_dit(DIT_BIT);

	/*
	 * Associate the allocated heap for mbedtls with the current CPU.
	 */
	ret = buffer_alloc_ctx_assign(&init_ctx);
	if (ret != 0) {
		return ret;
	}

	SIMD_FPU_ALLOW(mbedtls_memory_buffer_alloc_init(mem_buf,
							sizeof(mem_buf)));

	SIMD_FPU_ALLOW(ret = attest_rnd_prng_init());
	if (ret != 0) {
		goto attest_init_fail;
	}

	SIMD_FPU_ALLOW(psa_status = psa_crypto_init());
	if (psa_status != PSA_SUCCESS) {
		ret = -EINVAL;
		goto attest_init_fail;
	}

	/*
	 * Set the number of max operations per ECC signing iteration to the
	 * configured value.
	 *
	 * This adjusts the length of a single signing loop.
	 */
	SIMD_FPU_ALLOW(psa_interruptible_set_max_ops(MBEDTLS_ECP_MAX_OPS));

	/* Retrieve the platform key from root world */
	SIMD_FPU_ALLOW(ret = attest_init_realm_attestation_key());
	if (ret != 0) {
		goto attest_init_fail;
	}

	/* Retrieve the platform token from root world */
	ret = attest_setup_platform_token();
	if (ret != 0) {
		goto attest_init_fail;
	}

#if ATTEST_EL3_TOKEN_SIGN
	/* Initialize the EL3 queue */
	if (el3_token_sign_queue_init() != 0) {
		WARN("EL3 queue init failed.\n");
		ret = -ENOTSUP;
		goto attest_init_fail;
	}
#endif
	attest_initialized = true;

	/* Disable Data Independent Timing feature */
	write_dit(0x0);

attest_init_fail:
	buffer_alloc_ctx_unassign();
	return ret;
}

int attestation_heap_ctx_init(unsigned char *buf, size_t buf_size)
{
	assert(buf != NULL);

	if (attest_initialized == false) {
		ERROR("Attestation init failed.\n");
		return -EINVAL;
	}

	/* Initialise the mbedTLS heap */
	mbedtls_memory_buffer_alloc_init(buf, buf_size);

	return 0;
}

void attestation_heap_ctx_assign_pe(struct buffer_alloc_ctx *ctx)
{
	int ret __unused;
	assert(ctx != NULL);

	/* Associate the buffer_alloc_ctx to this CPU */
	ret = buffer_alloc_ctx_assign(ctx);
	assert(ret == 0);
}

void attestation_heap_ctx_unassign_pe(void)
{
	buffer_alloc_ctx_unassign();
}
