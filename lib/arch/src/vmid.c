/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch_features.h>
#include <assert.h>
#include <atomics.h>
#include <utils_def.h>
#include <vmid.h>

#ifndef CBMC
static unsigned long *vmids;
#else
/* For CBMC, keep as an array */
unsigned long vmids[VMID_ARRAY_LONG_SIZE];
#endif

/*
 * Marks the VMID value to be in use. It returns:
 * - True, on success
 * - False, if the vmid is out of range,
 *   or if it was already reserved (in use).
 */
static bool vmid_reserve(unsigned int vmid)
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

void vmid_init(uintptr_t alloc, size_t alloc_size)
{
	(void)alloc_size;

#ifndef CBMC
	vmids = (unsigned long *)alloc;
	assert(vmids != NULL);
	assert(alloc_size >= (VMID_ARRAY_LONG_SIZE * sizeof(unsigned long)));
#endif
}

/*
 * Returns a starting position for allocation search by scanning all bitmap
 * words for the first free VMID.
 */
static unsigned int vmid_hint(void)
{
	for (unsigned int i = 0U; i < VMID_ARRAY_LONG_SIZE; i++) {
		unsigned long word_val = vmids[i];

		if (word_val != ~0UL) {
			return i * BITS_PER_UL +
				(unsigned int)__builtin_ctzl(~word_val);
		}
	}

	return 0U;
}

/*
 * Allocates a free VMID from the available pool.
 * Returns:
 * - True, on success and sets vmid to the allocated value
 * - False, if no free VMID is available
 */
bool vmid_alloc(unsigned int *vmid)
{
	unsigned int vmid_count;
	unsigned int i;
	unsigned int start_hint;

	/* Number of supported VMID values */
	vmid_count = is_feat_vmid16_present() ? VMID16_COUNT : VMID8_COUNT;

	/* Get hint for where to start searching */
	start_hint = vmid_hint();
	if (start_hint >= vmid_count) {
		start_hint = 0U;
	}

	/* Search for a free VMID in the bitmap, in two phases */
	for (i = start_hint; i < vmid_count; i++) {
		if (vmid_reserve(i)) {
			*vmid = i;
			return true;
		}
	}
	for (i = 0U; i < start_hint; i++) {
		if (vmid_reserve(i)) {
			*vmid = i;
			return true;
		}
	}

	return false;
}
