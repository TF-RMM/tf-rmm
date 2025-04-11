/*
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <app_common.h>
#include <assert.h>
#include <base.h>
#include <el0_app_helpers.h>
#include <library/rnglib.h>
#include <psa/crypto.h>
#include <string.h>

/*
 * Generates a 64-bit random number.
 *
 * if rand is NULL, then assert().
 *
 * @param[out] rand_data     buffer pointer to store the 64-bit random value.
 *
 * @retval true         Random number generated successfully.
 * @retval false        Failed to generate the random number.
 *
 */
bool libspdm_get_random_number_64(uint64_t *rand_data)
{
	unsigned long ret;

	ret = el0_app_service_call(APP_SERVICE_RANDOM,
				   sizeof(*rand_data), 0, 0, 0);
	if (ret != 0U) {
		return false;
	}

	(void)memcpy((void *)rand_data, get_shared_mem_start(), sizeof(*rand_data));

	return true;
}
