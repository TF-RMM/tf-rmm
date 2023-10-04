/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch_helpers.h>
#include <assert.h>
#include <debug.h>
#include <rmm_el3_ifc.h>
#include <smc.h>
#include <stdint.h>
#include <string.h>
#include <utils_def.h>
#include <xlat_defs.h>

/*
 * Local copy of the core boot manifest to be used during runtime
 */
static struct rmm_core_manifest local_core_manifest;

/*
 * Manifest status
 */
static bool manifest_processed;

void rmm_el3_ifc_process_boot_manifest(void)
{
	assert((manifest_processed == (bool)false) &&
		(is_mmu_enabled() == (bool)false));

	/*
	 * The boot manifest is expected to be on the shared area.
	 * Make a local copy of it.
	 */
	(void)memcpy((void *)&local_core_manifest,
		     (void *)rmm_el3_ifc_get_shared_buf_pa(),
		     sizeof(struct rmm_core_manifest));

	inv_dcache_range((uintptr_t)&local_core_manifest,
				sizeof(local_core_manifest));

	/*
	 * Validate the Boot Manifest Version.
	 */
	if (!IS_RMM_EL3_MANIFEST_COMPATIBLE(local_core_manifest.version)) {
		rmm_el3_ifc_report_fail_to_el3(
					E_RMM_BOOT_MANIFEST_VERSION_NOT_SUPPORTED);
	}

	manifest_processed = true;
	inv_dcache_range((uintptr_t)&manifest_processed, sizeof(bool));
}

/* Return the raw value of the received boot manifest */
unsigned int rmm_el3_ifc_get_manifest_version(void)
{
	assert(manifest_processed == (bool)true);

	return local_core_manifest.version;
}

/* Return a pointer to the platform manifest */
uintptr_t rmm_el3_ifc_get_plat_manifest_pa(void)
{
	assert((manifest_processed == (bool)true) &&
		(is_mmu_enabled() == (bool)false));

	return local_core_manifest.plat_data;
}

/*
 * Validate DRAM data passed in plat_dram pointer.
 * Return a pointer to the platform DRAM info structure setup by EL3 Firmware
 * or NULL in case of an error.
 */
int rmm_el3_ifc_get_dram_data_validated_pa(unsigned long max_num_banks,
					   struct ns_dram_info **plat_dram_info)
{
	uint64_t num_banks, checksum, num_granules = 0UL;
	uintptr_t end = 0UL;
	struct ns_dram_info *plat_dram;
	struct ns_dram_bank *bank_ptr;

	assert((manifest_processed == (bool)true) &&
		(is_mmu_enabled() == (bool)false));

	*plat_dram_info = NULL;

	/*
	 * Validate the Boot Manifest Version
	 */
	if (local_core_manifest.version <
			RMM_EL3_MANIFEST_MAKE_VERSION(0U, 2U)) {
		return E_RMM_BOOT_MANIFEST_VERSION_NOT_SUPPORTED;
	}

	plat_dram = &local_core_manifest.plat_dram;

	/* Number of banks */
	num_banks = plat_dram->num_banks;	/* number of banks */

	/* Pointer to ns_dram_bank[] array */
	bank_ptr = plat_dram->banks;

	/* Validate number of banks and pointer to banks[] */
	if ((num_banks == 0UL) || (num_banks > max_num_banks) ||
	    (bank_ptr == NULL)) {
		return E_RMM_BOOT_MANIFEST_DATA_ERROR;
	}

	/* Calculate checksum of ns_dram_info structure */
	checksum = num_banks + (uint64_t)bank_ptr + plat_dram->checksum;

	for (unsigned long i = 0UL; i < num_banks; i++) {
		uint64_t size = bank_ptr->size;
		uintptr_t start = bank_ptr->base;

		/* Base address, size of bank and alignments */
		if ((start == 0UL) || (size == 0UL) ||
		    (((start | size) & PAGE_SIZE_MASK) != 0UL)) {
			return E_RMM_BOOT_MANIFEST_DATA_ERROR;
		}

		/*
		 * Check that base addresses of DRAM banks are
		 * passed in ascending order without overlapping.
		 */
		if (start < end) {
			return E_RMM_BOOT_MANIFEST_DATA_ERROR;
		}

		/* Update checksum */
		checksum += start + size;

		/* Update end address of the bank */
		end = start + size - 1UL;

		/* Total number of granules */
		num_granules += (size / GRANULE_SIZE);

		VERBOSE("DRAM%lu: 0x%lx-0x%lx\n", i, start, end);

		bank_ptr++;
	}

	/* Checksum must be 0 */
	if (checksum != 0UL) {
		return E_RMM_BOOT_MANIFEST_DATA_ERROR;
	}

	/* Check for the maximum number of granules supported */
	if (num_granules > RMM_MAX_GRANULES) {
		ERROR("Number of granules %lu exceeds maximum of %u\n",
			num_granules, RMM_MAX_GRANULES);
		return E_RMM_BOOT_MANIFEST_DATA_ERROR;
	}

	*plat_dram_info = plat_dram;
	return E_RMM_BOOT_SUCCESS;
}
