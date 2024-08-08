/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <attestation_priv.h>
#include <psa/crypto.h>
#include <random_app.h>

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
	(void)context;
	struct app_data_cfg *rnd_app_data = get_rmm_random_application();
	int ret = random_app_prng_get_random(rnd_app_data, output, output_size);
	if (ret != 0) {
		return PSA_ERROR_HARDWARE_FAILURE;
	}
	*output_length = output_size;

	return PSA_SUCCESS;
}

int attest_rnd_prng_init(void)
{
	/* TODO: this function shouldn't panic!!*/
	init_rmm_random_applications();
	return 0;
}
