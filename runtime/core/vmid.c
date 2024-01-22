/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch_features.h>
#include <assert.h>
#include <atomics.h>
#include <sizes.h>
#include <utils_def.h>
#include <vmid.h>

#define VMID8_COUNT		(U(1) << 8)
#define VMID16_COUNT		(U(1) << 16)
#define MAX_VMID_COUNT		VMID16_COUNT
#define VMID_ARRAY_LONG_SIZE	(MAX_VMID_COUNT / BITS_PER_UL)

/*
 * The bitmap for the reserved/used VMID values.
 */
IF_NCBMC(static) unsigned long vmids[VMID_ARRAY_LONG_SIZE];

/*
 * Marks the VMID value to be in use. It returns:
 * - True, on success
 * - False, if the vmid is out of range,
 *   or if it was already reserved (in use).
 */
bool vmid_reserve(unsigned int vmid)
{
	unsigned int offset;
	unsigned int vmid_count;

	/* Number of supported VMID values */
	vmid_count = is_feat_vmid16_present() ? VMID16_COUNT : VMID8_COUNT;

	/*
	 * The input from NS as part of RMI_REALM_CREATE is 'short int' type,
	 * so this check will not fail on systems with FEAT_VMID16 implemented.
	 */
	if (vmid >= vmid_count) {
		return false;
	}

	offset = vmid / BITS_PER_UL;
	vmid %= BITS_PER_UL;

	return !atomic_bit_set_acquire_release_64(&vmids[offset], vmid);
}

/*
 * Marks the VMID value to be not in use.
 */
void vmid_free(unsigned int vmid)
{
	unsigned int offset;
	unsigned int __unused vmid_count;

	/* Number of supported VMID values */
	vmid_count = is_feat_vmid16_present() ? VMID16_COUNT : VMID8_COUNT;

	/* Check the number of supported VMID values */
	assert(vmid < vmid_count);

	offset = vmid / BITS_PER_UL;
	vmid %= BITS_PER_UL;

	atomic_bit_clear_release_64(&vmids[offset], vmid);
}
