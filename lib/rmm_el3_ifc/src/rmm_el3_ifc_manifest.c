/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch_features.h>
#include <arch_helpers.h>
#include <assert.h>
#include <debug.h>
#include <rmm_el3_ifc.h>
#include <rmm_el3_ifc_priv.h>
#include <smc.h>
#include <stdint.h>
#include <string.h>
#include <utils_def.h>

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
	assert(!manifest_processed && !is_mmu_enabled());

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
	assert(manifest_processed);

	return local_core_manifest.version;
}

/* Return a pointer to the platform manifest */
/* coverity[misra_c_2012_rule_8_7_violation:SUPPRESS] */
uintptr_t rmm_el3_ifc_get_plat_manifest_pa(void)
{
	assert(manifest_processed && !is_mmu_enabled());

	return local_core_manifest.plat_data;
}

/*
 * Calculate checksum of 64-bit words @buffer with @size length
 */
static uint64_t checksum_calc(uint64_t *buffer, size_t size)
{
	uint64_t sum = 0UL;

	assert(((uintptr_t)buffer & (sizeof(uint64_t) - 1UL)) == 0UL);
	assert((size & (sizeof(uint64_t) - 1UL)) == 0UL);

	for (unsigned long i = 0UL; i < (size / sizeof(uint64_t)); i++) {
		sum += buffer[i];
	}

	return sum;
}

/*
 * Return validated memory data passed in plat_memory pointer.
 * If the function returns E_RMM_BOOT_SUCCESS, then it either returns a pointer
 * to the platform memory info structure setup by EL3 Firmware in *memory_info
 * or NULL if the number of memory banks specified by EL3 is 0 and the pointer
 * to memory_bank[] array is NULL. In case of any other error, NULL is returned
 * in *memory_info.
 */
static int get_memory_data_validated_pa(unsigned long max_num_banks,
					struct memory_info **memory_info,
					struct memory_info *plat_memory)
{
	uint64_t num_banks, checksum;
	uintptr_t end = 0UL;
	struct memory_bank *bank_ptr;

	assert((memory_info != NULL) && (plat_memory != NULL));
	assert(manifest_processed && !is_mmu_enabled());

	/* Set pointer to the platform memory info structure to NULL */
	*memory_info = NULL;

	/* Number of banks */
	num_banks = plat_memory->num_banks;

	/* Pointer to memory_bank[] array */
	bank_ptr = plat_memory->banks;

	/*
	 * Return *memory_info set to NULL if number of banks is 0 and all other
	 * fields are valid. This is expected only for device address ranges.
	 */
	if ((num_banks == 0UL) && (bank_ptr == NULL) &&
	    (plat_memory->checksum == 0UL)) {
		VERBOSE(" None\n");
		return E_RMM_BOOT_SUCCESS;
	}

	/* Validate number of banks and pointer to banks[] */
	if ((num_banks == 0UL) || (num_banks > max_num_banks) ||
	    (bank_ptr == NULL)) {
		return E_RMM_BOOT_MANIFEST_DATA_ERROR;
	}

	/* Calculate checksum of memory_info structure */
	checksum = num_banks + (uint64_t)bank_ptr + plat_memory->checksum;

	for (unsigned long i = 0UL; i < num_banks; i++) {
		uint64_t size = bank_ptr->size;
		uintptr_t start = bank_ptr->base;
		uintptr_t max_pa_size =
				(uintptr_t)(1ULL << arch_feat_get_pa_width());

		/* Base address, size of bank and alignments */
		if ((start == 0UL) || (size == 0UL) ||
		    (!GRANULE_ALIGNED(start | size))) {
			return E_RMM_BOOT_MANIFEST_DATA_ERROR;
		}

		/*
		 * Check that base addresses of DRAM banks are
		 * passed in ascending order without overlapping.
		 */
		if (start < end) {
			return E_RMM_BOOT_MANIFEST_DATA_ERROR;
		}

		/* Update end address of the bank */
		end = start + size - 1UL;

		/*
		 * Check that the bank does not exceed the PA range
		 * supported by the platform.
		 */
		if (end >= max_pa_size) {
			return E_RMM_BOOT_MANIFEST_DATA_ERROR;
		}

		VERBOSE(" 0x%lx-0x%lx\n", start, end);

		bank_ptr++;
	}

	/* Update checksum */
	assert(plat_memory->banks != NULL);
	checksum += checksum_calc((uint64_t *)plat_memory->banks,
					sizeof(struct memory_bank) * num_banks);

	/* Checksum must be 0 */
	if (checksum != 0UL) {
		return E_RMM_BOOT_MANIFEST_DATA_ERROR;
	}

	*memory_info = plat_memory;
	return E_RMM_BOOT_SUCCESS;
}

/*
 * Return validated DRAM data passed in plat_dram pointer.
 * Return a pointer to the platform DRAM info structure setup by EL3 Firmware
 * or NULL in case of an error.
 */
int rmm_el3_ifc_get_dram_data_validated_pa(unsigned long max_num_banks,
					   struct memory_info **plat_dram_info)
{
	int ret;

	assert(plat_dram_info != NULL);

	/*
	 * Validate the Boot Manifest Version
	 */
	if (local_core_manifest.version <
		RMM_EL3_MANIFEST_MAKE_VERSION(U(0), U(2))) {
		return E_RMM_BOOT_MANIFEST_VERSION_NOT_SUPPORTED;
	}

	VERBOSE("DRAM:\n");

	ret = get_memory_data_validated_pa(max_num_banks, plat_dram_info,
					   &local_core_manifest.plat_dram);
	if (ret != E_RMM_BOOT_SUCCESS) {
		return ret;
	}

	/* No DRAM data */
	if (*plat_dram_info == NULL) {
		return E_RMM_BOOT_MANIFEST_DATA_ERROR;
	}

	return E_RMM_BOOT_SUCCESS;
}

/*
 * Return validated device address ranges data passed in plat_dev_range_info
 * pointer type.
 * In case of E_RMM_BOOT_SUCCESS, return a pointer to the platform device
 * address ranges info structure setup by EL3 Firmware or NULL if the number
 * of memory banks specified by EL3 is 0 and the pointer to memory_bank[] array
 * is NULL. In case of any other error, return NULL in *plat_dev_range_info.
 */
int rmm_el3_ifc_get_dev_range_validated_pa(unsigned long max_num_banks,
					   struct memory_info **plat_dev_range_info,
					   enum dev_coh_type type)
{
	struct memory_info *plat_memory;

	/*
	 * Validate the Boot Manifest Version
	 */
	if (local_core_manifest.version <
		RMM_EL3_MANIFEST_MAKE_VERSION(U(0), U(4))) {
		*plat_dev_range_info = NULL;
		return E_RMM_BOOT_MANIFEST_VERSION_NOT_SUPPORTED;
	}

	assert(type < DEV_MEM_MAX);

	VERBOSE("Device %scoherent address range:\n",
		(type == DEV_MEM_COHERENT) ? "" : "non-");

	if (type == DEV_MEM_COHERENT) {
		plat_memory = &local_core_manifest.plat_coh_region;
	} else {
		plat_memory = &local_core_manifest.plat_ncoh_region;
	}

	return get_memory_data_validated_pa(max_num_banks, plat_dev_range_info,
					    plat_memory);
}

/*
 * Return validated Console list passed in plat_console pointer
 * from the Boot manifest v0.3 onwards.
 */
int rmm_el3_ifc_get_console_list_pa(struct console_list **plat_console_list)
{
	uint64_t num_consoles, checksum;
	struct console_list *csl_list;
	struct console_info *console_ptr;

	assert(manifest_processed && !is_mmu_enabled());

	*plat_console_list = NULL;

	/*
	 * Validate the Boot Manifest Version
	 */
	if (local_core_manifest.version <
			RMM_EL3_MANIFEST_MAKE_VERSION(U(0), U(3))) {
		return E_RMM_BOOT_MANIFEST_VERSION_NOT_SUPPORTED;
	}

	csl_list = &local_core_manifest.plat_console;

	/* Number of consoles */
	num_consoles = csl_list->num_consoles;

	/* Pointer to the consoles array */
	console_ptr = csl_list->consoles;

	/* Calculate the checksum of the console_list structure */
	checksum = num_consoles + (uint64_t)console_ptr + csl_list->checksum;

	/* Update checksum */
	checksum += checksum_calc((uint64_t *)console_ptr,
					sizeof(struct console_info) * num_consoles);

	/* Verify the checksum is 0 */
	if (checksum != 0UL) {
		return E_RMM_BOOT_MANIFEST_DATA_ERROR;
	}

	*plat_console_list = csl_list;

	return E_RMM_BOOT_SUCCESS;
}

/*
 * Return validated Root Complex list in plat_rc_list pointer from the Boot
 * manifest v0.5 onwards.
 */
int rmm_el3_ifc_get_root_complex_list_pa(struct root_complex_list **plat_rc_list)
{
	struct root_complex_list *rc_list;
	struct root_complex_info *rc_info;
	uint64_t num_root_complexes;
	uint64_t total_size;
	uint64_t checksum;

	assert((manifest_processed == (bool)true) &&
		(is_mmu_enabled() == (bool)false));

	*plat_rc_list = NULL;

	/* Validate the Boot Manifest Version */
	if (local_core_manifest.version <
			RMM_EL3_MANIFEST_MAKE_VERSION(U(0), U(5))) {
		return E_RMM_BOOT_MANIFEST_VERSION_NOT_SUPPORTED;
	}

	rc_list = &local_core_manifest.plat_root_complex;

	num_root_complexes = rc_list->num_root_complex;
	rc_info = rc_list->root_complex;

	/* Calculate the checksum of the rc_list structure */
	checksum = num_root_complexes + (uint64_t)rc_info + rc_list->checksum;

	/* Calculate all Root complex info size */
	total_size = num_root_complexes * sizeof(struct root_complex_info);

	for (uint64_t rc_idx = 0UL; rc_idx < num_root_complexes; rc_idx++) {
		struct root_port_info *rp_info;
		uint32_t num_root_ports;

		num_root_ports = rc_info[rc_idx].num_root_ports;
		rp_info = rc_info[rc_idx].root_ports;

		total_size += num_root_ports * sizeof(struct root_port_info);
		total_size += rp_info->num_bdf_mappings *
			sizeof(struct bdf_mapping_info);
	}

	/* Update checksum */
	checksum += checksum_calc((uint64_t *)rc_info, total_size);

	/* Verify the checksum is 0 */
	if (checksum != 0UL) {
		return E_RMM_BOOT_MANIFEST_DATA_ERROR;
	}

	*plat_rc_list = rc_list;

	return E_RMM_BOOT_SUCCESS;
}

/*
 * Return validated SMMUv3 list passed in plat_smmu pointer
 * from the Boot manifest v0.5 onwards.
 */
int rmm_el3_ifc_get_smmu_list_pa(struct smmu_list **plat_smmu_list)
{
	uint64_t num_smmus, checksum;
	struct smmu_list *smmus_list;
	struct smmu_info *smmus_ptr;

	assert(manifest_processed && !is_mmu_enabled());

	*plat_smmu_list = NULL;

	/*
	 * Validate the Boot Manifest Version
	 */
	if (local_core_manifest.version <
			RMM_EL3_MANIFEST_MAKE_VERSION(U(0), U(5))) {
		return E_RMM_BOOT_MANIFEST_VERSION_NOT_SUPPORTED;
	}

	smmus_list = &local_core_manifest.plat_smmu;

	/* Number of SMMUv3 */
	num_smmus = smmus_list->num_smmus;

	/* Verify number of SMMUv3 */
	if ((num_smmus == 0UL) || (num_smmus > RMM_MAX_SMMUS)) {
		return E_RMM_BOOT_MANIFEST_DATA_ERROR;
	}

	/* Pointer to the SMMUv3 array */
	smmus_ptr = smmus_list->smmus;

	/* Calculate the checksum of the smmu_list structure */
	checksum = num_smmus + (uint64_t)smmus_ptr + smmus_list->checksum;

	/* Update checksum */
	checksum += checksum_calc((uint64_t *)smmus_ptr,
					sizeof(struct smmu_info) * num_smmus);

	/* Verify the checksum is 0 */
	if (checksum != 0UL) {
		return E_RMM_BOOT_MANIFEST_DATA_ERROR;
	}

	*plat_smmu_list = smmus_list;

	return E_RMM_BOOT_SUCCESS;
}
