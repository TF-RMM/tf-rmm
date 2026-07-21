/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifdef CBMC

#include <simd.h>
#include <tb_common.h>

void simd_init(void)
{
	ASSERT(false, "simd_init");
}

int simd_get_cpu_config(struct simd_config *simd_cfg)
{
	memset(simd_cfg, 0, sizeof(*simd_cfg));
	return 0;
}

int simd_context_init(simd_owner_t owner, struct simd_context *simd_ctx,
		      const struct simd_config *simd_cfg)
{
	ASSERT(false, "simd_context_init");
	return 0;
}

bool simd_is_state_saved(void)
{
	ASSERT(false, "simd_is_state_saved");
	return false;
}

void simd_update_smc_sve_hint(struct simd_context *ctx, bool sve_hint)
{
	ASSERT(false, "simd_update_smc_sve_hint");
}
#endif /* CBMC */
