/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <assert.h>
#include <debug.h>
#include <rmm_el3_ifc.h>
#include <sizes.h>
#include <smc.h>
#include <spinlock.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <xlat_defs.h>

/* Platform parameter */
extern uintptr_t rmm_shared_buffer_start_va;

/* Spinlock used to protect the EL3<->RMM shared area */
static spinlock_t shared_area_lock = {0U};

/*
 * Get and lock a pointer to the start of the RMM<->EL3 shared buffer.
 */
uintptr_t rmm_el3_ifc_get_shared_buf_locked(void)
{
	spinlock_acquire(&shared_area_lock);

	return rmm_shared_buffer_start_va;
}

/*
 * Release the RMM <-> EL3 buffer.
 */
void rmm_el3_ifc_release_shared_buf(void)
{
	spinlock_release(&shared_area_lock);
}

/*
 * Get the realm attestation key to sign the realm attestation token. It is
 * expected that only the private key is retrieved in raw format.
 */
int rmm_el3_ifc_get_realm_attest_key(uintptr_t buf, size_t buflen,
					size_t *len, unsigned int crv)
{
	struct smc_result smc_res;
	unsigned long buffer_pa;
	unsigned long offset =
		(unsigned long)(buf - rmm_shared_buffer_start_va);

	assert((offset + buflen) <= rmm_el3_ifc_get_shared_buf_size());
	assert((buf & ~PAGE_SIZE_MASK) == rmm_shared_buffer_start_va);

	buffer_pa = (unsigned long)rmm_el3_ifc_get_shared_buf_pa() + offset;

	monitor_call_with_res(SMC_RMM_GET_REALM_ATTEST_KEY,
			      buffer_pa,
			      buflen,
			      crv, 0UL, 0UL, 0UL, &smc_res);

	if (smc_res.x[0] != 0UL) {
		ERROR("Failed to get realm attestation key x0 = 0x%lx\n",
				smc_res.x[0]);
		return (int)smc_res.x[0];
	}

	*len = smc_res.x[1];

	return 0;
}

/*
 * Get the platform token from the EL3 firmware.
 * The caller must have already populated the public hash in `buf` which is an
 * input for platform token computation.
 */
int rmm_el3_ifc_get_platform_token(uintptr_t buf, size_t buflen,
					size_t *len, size_t hash_size)
{
	struct smc_result smc_res;
	unsigned long buffer_pa;
	unsigned long offset =
		(unsigned long)(buf - rmm_shared_buffer_start_va);

	assert((offset + buflen) <= rmm_el3_ifc_get_shared_buf_size());
	assert((buf & ~PAGE_SIZE_MASK) == rmm_shared_buffer_start_va);

	buffer_pa = (unsigned long)rmm_el3_ifc_get_shared_buf_pa() + offset;
	/* Get the available space on the buffer after the offset */

	monitor_call_with_res(SMC_RMM_GET_PLAT_TOKEN,
			      buffer_pa,
			      buflen,
			      hash_size,
			      0UL, 0UL, 0UL, &smc_res);

	if (smc_res.x[0] != 0UL) {
		ERROR("Failed to get platform token x0 = 0x%lx\n",
				smc_res.x[0]);
		return (int)smc_res.x[0];
	}

	*len = smc_res.x[1];

	return 0;
}
