/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <assert.h>
#include <rmm_el3_compat.h>
#include <rmm_el3_ifc_priv.h>

static struct rmm_el3_compat_callbacks *compat_callbacks;

/* cppcheck-suppress misra-c2012-8.7 */
void rmm_el3_ifc_set_compat_callbacks(
		struct rmm_el3_compat_callbacks *callbacks)
{
	compat_callbacks = callbacks;
}

/* cppcheck-suppress misra-c2012-8.7 */
void compat_reserve_memory(size_t size, uint64_t arg, struct smc_result *smc_res)
{
	assert(compat_callbacks != NULL);
	assert(compat_callbacks->reserve_mem_cb != NULL);

	smc_res->x[0] = (unsigned long)compat_callbacks->reserve_mem_cb(size, &arg);
	smc_res->x[1] = arg;
}
