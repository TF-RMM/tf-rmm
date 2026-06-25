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
 * Local copy of the core Boot Manifest to be used during runtime
 */
static uint8_t cached_manifest[GRANULE_SIZE] __aligned(GRANULE_SIZE);
static struct rmm_core_manifest *local_core_manifest;

/*
 * Copy the SMMU list data into the cached manifest buffer.
 * The SMMU info array needs to be copied separately since it's
 * pointed to by the manifest structure.
 *
 * Return updated offset.
 */
static size_t copy_smmu_data(size_t offset)
{
	struct smmu_info *smmus_ptr = local_core_manifest->plat_smmu.smmus;
	size_t smmu_array_size = sizeof(struct smmu_info) *
					local_core_manifest->plat_smmu.num_smmus;
	void *cached_smmu_array;

	if ((smmu_array_size == 0UL) || (smmus_ptr == NULL)) {
		return offset;
	}

	/* Ensure the SMMU array fits in the cached manifest buffer */
	assert((offset + smmu_array_size) <= GRANULE_SIZE);

	cached_smmu_array = (void *)((uintptr_t)cached_manifest + offset);

	/* Copy the SMMU array to cached buffer */
	(void)memcpy(cached_smmu_array, (void *)smmus_ptr, smmu_array_size);

	/* Update the pointer in local_core_manifest to point to cached copy */
	local_core_manifest->plat_smmu.smmus = (struct smmu_info *)cached_smmu_array;

	inv_dcache_range((uintptr_t)cached_smmu_array, smmu_array_size);

	return (offset + smmu_array_size);
}

/*
 * Calculate the size of the PCIe Root Complex List data.
 */
static size_t get_root_complex_size(struct root_complex_list *rc_list)
{
	struct root_complex_info *rc_info;
	uint64_t num_root_complexes;
	size_t size;

	assert(rc_list != NULL);

	rc_info = rc_list->root_complex;
	num_root_complexes = rc_list->num_root_complex;

	/* No Root Complex List data */
	if ((num_root_complexes == 0UL) || (rc_info == NULL)) {
		return 0UL;
	}

	/* Root Complex info size */
	size = num_root_complexes * sizeof(struct root_complex_info);

	/* Calculate all Root Complex data size */
	for (uint64_t rc_idx = 0UL; rc_idx < num_root_complexes; rc_idx++) {
		struct root_port_info *rp_info = rc_info[rc_idx].root_ports;
		uint32_t num_root_ports = rc_info[rc_idx].num_root_ports;

		/* No Root Port data */
		if ((num_root_ports == 0U) || (rp_info == NULL)) {
			continue;
		}

		size += num_root_ports * sizeof(struct root_port_info);

		/* Sum BDF mapping counts across all Root Ports */
		for (uint32_t rp_idx = 0U; rp_idx < num_root_ports; rp_idx++) {
			size += rp_info[rp_idx].num_bdf_mappings *
				sizeof(struct bdf_mapping_info);
		}
	}

	return size;
}

/*
 * Copy the PCIe Root Port data into a new buffer.
 *
 * The root_complex_info array and all nested root_port_info and
 * bdf_mapping_info arrays are copied into @buffer at @offset.  The
 * internal pointers within the copied structures (root_ports,
 * bdf_mappings) are updated to point into the new buffer.
 *
 * NOTE: The top-level rc_list->root_complex pointer is NOT updated.
 * The caller must patch it after this call:
 *
 *   rc_list->root_complex =
 *       (struct root_complex_info *)((uintptr_t)buffer + offset);
 */
static void set_root_complex_data(struct root_complex_list *rc_list,
				  void *buffer, size_t offset)
{
	struct root_complex_info *rc_info, *dst_rc_info;
	uint64_t num_root_complexes;
	size_t copy_size;

	assert(rc_list != NULL);
	assert(buffer != NULL);

	num_root_complexes = rc_list->num_root_complex;

	rc_info = rc_list->root_complex;

	/* No Root Complex data */
	if ((num_root_complexes == 0UL) || (rc_info == NULL)) {
		return;
	}

	copy_size = num_root_complexes * sizeof(struct root_complex_info);

	dst_rc_info = (struct root_complex_info *)((uintptr_t)buffer + offset);

	/* Copy all Root Complex info structures */
	(void)memcpy((void *)dst_rc_info, (void *)rc_info, copy_size);

	offset += copy_size;

	/* Iterate over all Root Complexes */
	for (uint64_t rc_idx = 0UL; rc_idx < num_root_complexes; rc_idx++) {
		struct root_port_info *rp_info = dst_rc_info[rc_idx].root_ports;
		struct root_port_info *dst_rp_info =
			(struct root_port_info *)((uintptr_t)buffer + offset);
		uint32_t num_root_ports = dst_rc_info[rc_idx].num_root_ports;

		/* No Root Port data */
		if ((num_root_ports == 0U) || (rp_info == NULL)) {
			continue;
		}

		copy_size = num_root_ports * sizeof(struct root_port_info);

		/* Copy all Root Port info structures */
		(void)memcpy((void *)dst_rp_info, (void *)rp_info, copy_size);

		offset += copy_size;

		/* Update the pointer in local_core_manifest */
		dst_rc_info[rc_idx].root_ports = dst_rp_info;

		/* Iterate over all Root Ports */
		for (uint32_t rp_idx = 0U; rp_idx < num_root_ports; rp_idx++) {
			struct bdf_mapping_info *bdf_info =
						dst_rp_info[rp_idx].bdf_mappings;
			struct bdf_mapping_info *dst_bdf_info =
				(struct bdf_mapping_info *)((uintptr_t)buffer + offset);
			uint32_t num_bdf_mappings = rp_info[rp_idx].num_bdf_mappings;

			/* No BDF Mapping data */
			if ((num_bdf_mappings == 0U) || (bdf_info == NULL)) {
				continue;
			}

			copy_size = num_bdf_mappings * sizeof(struct bdf_mapping_info);

			/* Copy all BDF Mapping Info structures */
			(void)memcpy((void *)dst_bdf_info, (void *)bdf_info, copy_size);

			offset += copy_size;

			/* Update the pointer in local_core_manifest */
			dst_rp_info[rp_idx].bdf_mappings = dst_bdf_info;
		}
	}
}

/*
 * Copy the PCIe Root Port data into the cached manifest buffer.
 *
 * Return updated offset.
 */
static size_t copy_root_complex_data(size_t offset)
{
	struct root_complex_list *rc_list = &local_core_manifest->plat_root_complex;
	size_t size = get_root_complex_size(rc_list);

	/* Ensure all Root Complex info fits in the cached manifest buffer */
	assert((offset + size) <= GRANULE_SIZE);

	/* Copy the data and update the associated pointers */
	if (size != 0UL) {
		struct root_complex_info *cached_rc_info;

		set_root_complex_data(rc_list, (void *)cached_manifest, offset);

		cached_rc_info = (struct root_complex_info *)
					((uintptr_t)cached_manifest + offset);

		/* Update the pointer in local_core_manifest to point to the cached copy */
		local_core_manifest->plat_root_complex.root_complex = cached_rc_info;

		inv_dcache_range((uintptr_t)cached_rc_info, size);
	}

	return (offset + size);
}

void rmm_el3_ifc_process_boot_manifest(void)
{
	struct rmm_core_manifest *core_manifest;

	assert((local_core_manifest == NULL) && !is_mmu_enabled());

	core_manifest = (struct rmm_core_manifest *)rmm_el3_ifc_get_shared_buf_pa();

	/* Validate the Boot Manifest Version */
	if (!IS_RMM_EL3_MANIFEST_COMPATIBLE(core_manifest->version)) {
		rmm_el3_ifc_report_fail_to_el3(
					E_RMM_BOOT_MANIFEST_VERSION_NOT_SUPPORTED);
	}

	local_core_manifest = (struct rmm_core_manifest *)&cached_manifest;

	inv_dcache_range((uintptr_t)&local_core_manifest, sizeof(uintptr_t));

	/*
	 * The Boot Manifest is expected to be on the shared area.
	 * Make a local copy of it.
	 */
	(void)memcpy((void *)local_core_manifest, (void *)core_manifest,
		     sizeof(struct rmm_core_manifest));

	/* Check the Boot Manifest Version */
	if (local_core_manifest->version >=
		RMM_EL3_MANIFEST_MAKE_VERSION(U(0), U(5))) {

		/* Copy the SMMU list data into the cached manifest buffer */
		size_t offset = copy_smmu_data(sizeof(struct rmm_core_manifest));

		/* Copy the PCIe Root Complex data into the cached manifest buffer */
		(void)copy_root_complex_data(offset);
	}

	/*
	 * Invalidate the cache for the manifest header to ensure visibility of the
	 * data copied by memcpy() and any updates performed by copy_smmu_data()
	 * and copy_root_complex_data().
	 */
	inv_dcache_range((uintptr_t)local_core_manifest,
				sizeof(struct rmm_core_manifest));
}

/* Return the raw value of the received boot manifest */
unsigned int rmm_el3_ifc_get_manifest_version(void)
{
	assert(local_core_manifest != NULL);

	return local_core_manifest->version;
}

/* Return a pointer to the platform manifest */
/* coverity[misra_c_2012_rule_8_7_violation:SUPPRESS] */
uintptr_t rmm_el3_ifc_get_plat_manifest_pa(void)
{
	assert((local_core_manifest != NULL) && !is_mmu_enabled());

	return local_core_manifest->plat_data;
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
	assert((local_core_manifest != NULL) && !is_mmu_enabled());

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
	if (local_core_manifest->version <
		RMM_EL3_MANIFEST_MAKE_VERSION(U(0), U(2))) {
		return E_RMM_BOOT_MANIFEST_VERSION_NOT_SUPPORTED;
	}

	VERBOSE("DRAM:\n");

	ret = get_memory_data_validated_pa(max_num_banks, plat_dram_info,
					   &local_core_manifest->plat_dram);
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
	if (local_core_manifest->version <
		RMM_EL3_MANIFEST_MAKE_VERSION(U(0), U(4))) {
		*plat_dev_range_info = NULL;
		return E_RMM_BOOT_MANIFEST_VERSION_NOT_SUPPORTED;
	}

	assert(type < DEV_MEM_MAX);

	VERBOSE("Device %scoherent address range:\n",
		(type == DEV_MEM_COHERENT) ? "" : "non-");

	if (type == DEV_MEM_COHERENT) {
		plat_memory = &local_core_manifest->plat_coh_region;
	} else {
		plat_memory = &local_core_manifest->plat_ncoh_region;
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

	assert((local_core_manifest != NULL) && !is_mmu_enabled());

	*plat_console_list = NULL;

	/*
	 * Validate the Boot Manifest Version
	 */
	if (local_core_manifest->version <
			RMM_EL3_MANIFEST_MAKE_VERSION(U(0), U(3))) {
		return E_RMM_BOOT_MANIFEST_VERSION_NOT_SUPPORTED;
	}

	csl_list = &local_core_manifest->plat_console;

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
 * Return SMMUv3 list passed in plat_smmu pointer cached in RMM.
 * From the Boot manifest v0.5 onwards.
 */
int rmm_el3_ifc_get_cached_smmu_list_pa(struct smmu_list **plat_smmu_list)
{
	uint64_t num_smmus;
	struct smmu_list *smmus_list;

	assert((local_core_manifest != NULL) && is_mmu_enabled());

	*plat_smmu_list = NULL;

	/*
	 * Validate the Boot Manifest Version
	 */
	if (local_core_manifest->version <
			RMM_EL3_MANIFEST_MAKE_VERSION(U(0), U(5))) {
		return E_RMM_BOOT_MANIFEST_VERSION_NOT_SUPPORTED;
	}

	smmus_list = &local_core_manifest->plat_smmu;

	/* Number of SMMUv3 */
	num_smmus = smmus_list->num_smmus;

	/* Verify number of SMMUv3 */
	if ((num_smmus == 0UL) || (smmus_list->smmus == NULL)) {
		return E_RMM_BOOT_MANIFEST_DATA_ERROR;
	}

	*plat_smmu_list = smmus_list;
	return E_RMM_BOOT_SUCCESS;
}

/*
 * Check whether @ecam_addr matches a Root Complex ECAM base address from the
 * cached Root Complex topology.
 */
bool rmm_el3_ifc_is_ecam_base_valid(unsigned long ecam_addr)
{
	struct root_complex_list *rc_list;
	struct root_complex_info *root_complex;
	uint64_t num_root_complexes;

	assert(local_core_manifest != NULL);

	rc_list = &local_core_manifest->plat_root_complex;
	num_root_complexes = rc_list->num_root_complex;
	root_complex = rc_list->root_complex;

	if ((num_root_complexes == 0UL) || (root_complex == NULL)) {
		return false;
	}

	for (uint64_t rc_idx = 0UL; rc_idx < num_root_complexes; rc_idx++) {
		if (root_complex[rc_idx].ecam_base == ecam_addr) {
			return true;
		}
	}

	return false;
}

bool rmm_el3_ifc_is_bdf_valid(unsigned long ecam_addr, unsigned int bdf)
{
	struct root_complex_list *rc_list;
	struct root_complex_info *root_complex;
	uint64_t num_root_complexes;

	assert(local_core_manifest != NULL);

	rc_list = &local_core_manifest->plat_root_complex;
	num_root_complexes = rc_list->num_root_complex;
	root_complex = rc_list->root_complex;

	if ((num_root_complexes == 0UL) || (root_complex == NULL)) {
		return false;
	}

	for (uint64_t rc_idx = 0UL; rc_idx < num_root_complexes; rc_idx++) {
		struct root_port_info *rp_info;
		uint32_t num_root_ports;

		if (root_complex[rc_idx].ecam_base != ecam_addr) {
			continue;
		}

		rp_info = root_complex[rc_idx].root_ports;
		num_root_ports = root_complex[rc_idx].num_root_ports;

		if ((num_root_ports == 0U) || (rp_info == NULL)) {
			return false;
		}

		for (uint32_t rp_idx = 0U; rp_idx < num_root_ports; rp_idx++) {
			struct bdf_mapping_info *bdf_info = rp_info[rp_idx].bdf_mappings;
			uint32_t num_bdf_mappings = rp_info[rp_idx].num_bdf_mappings;

			if ((num_bdf_mappings == 0U) || (bdf_info == NULL)) {
				continue;
			}

			for (uint32_t map_idx = 0U; map_idx < num_bdf_mappings; map_idx++) {
				if ((bdf >= bdf_info[map_idx].mapping_base) &&
				    (bdf <= bdf_info[map_idx].mapping_top)) {
					return true;
				}
			}
		}

		return false;
	}

	return false;
}

bool rmm_el3_ifc_is_root_port_id_valid(unsigned long ecam_addr,
				       unsigned int root_port_id)
{
	struct root_complex_list *rc_list;
	struct root_complex_info *root_complex;
	uint64_t num_root_complexes;

	assert(local_core_manifest != NULL);

	rc_list = &local_core_manifest->plat_root_complex;
	num_root_complexes = rc_list->num_root_complex;
	root_complex = rc_list->root_complex;

	if ((num_root_complexes == 0UL) || (root_complex == NULL)) {
		return false;
	}

	for (uint64_t rc_idx = 0UL; rc_idx < num_root_complexes; rc_idx++) {
		struct root_port_info *rp_info;
		uint32_t num_root_ports;

		if (root_complex[rc_idx].ecam_base != ecam_addr) {
			continue;
		}

		rp_info = root_complex[rc_idx].root_ports;
		num_root_ports = root_complex[rc_idx].num_root_ports;

		if ((num_root_ports == 0U) || (rp_info == NULL)) {
			return false;
		}

		for (uint32_t rp_idx = 0U; rp_idx < num_root_ports; rp_idx++) {
			if (rp_info[rp_idx].root_port_id == root_port_id) {
				return true;
			}
		}

		return false;
	}

	return false;
}

/*
 * Resolve a PCIe device BDF to an SMMU index and StreamID using the
 * cached Root Complex topology.
 */
int rmm_el3_ifc_bdf_to_smmu(unsigned long ecam_addr, unsigned int bdf,
			    unsigned int *smmu_idx, unsigned int *sid)
{
	struct root_complex_list *rc_list;
	struct root_complex_info *root_complex;
	uint64_t num_root_complexes;

	assert(smmu_idx != NULL);
	assert(sid != NULL);
	assert(local_core_manifest != NULL);

	rc_list = &local_core_manifest->plat_root_complex;
	num_root_complexes = rc_list->num_root_complex;
	root_complex = rc_list->root_complex;

	if ((num_root_complexes == 0UL) || (root_complex == NULL)) {
		return E_RMM_INVAL;
	}

	/* Find the Root Complex matching the ECAM base address */
	for (uint64_t rc_idx = 0UL; rc_idx < num_root_complexes; rc_idx++) {
		struct root_port_info *rp_info;
		uint32_t num_root_ports;

		if (root_complex[rc_idx].ecam_base != ecam_addr) {
			continue;
		}

		rp_info = root_complex[rc_idx].root_ports;
		num_root_ports = root_complex[rc_idx].num_root_ports;

		if ((num_root_ports == 0U) || (rp_info == NULL)) {
			return E_RMM_INVAL;
		}

		/* Iterate over all Root Ports */
		for (uint32_t rp_idx = 0U; rp_idx < num_root_ports; rp_idx++) {
			struct bdf_mapping_info *bdf_info =
						rp_info[rp_idx].bdf_mappings;
			uint32_t num_bdf_mappings =
						rp_info[rp_idx].num_bdf_mappings;

			if ((num_bdf_mappings == 0U) || (bdf_info == NULL)) {
				continue;
			}

			/* Iterate over all BDF Mappings */
			for (uint32_t map_idx = 0U;
			     map_idx < num_bdf_mappings; map_idx++) {
				if ((bdf >= bdf_info[map_idx].mapping_base) &&
				    (bdf <= bdf_info[map_idx].mapping_top)) {
					*smmu_idx = (unsigned int)
							bdf_info[map_idx].smmu_idx;
					*sid = bdf + ((unsigned int)
							bdf_info[map_idx].mapping_off << 16);
					return E_RMM_OK;
				}
			}
		}

		/* ECAM matched but BDF not found in this Root Complex */
		return E_RMM_INVAL;
	}

	return E_RMM_INVAL;
}

/*
 * Return the maximum StreamID for the given SMMU index.
 *
 * The function scans the Root Complex information provided in the local
 * core manifest and searches all BDF mapping entries associated with the
 * requested SMMU. For each matching entry, the BDF mapping top is
 * translated using mapping_off, and the highest resulting
 * StreamID value is returned.
 *
 * Args:
 *	- smmu_idx	SMMU index to search for.
 *	- sid_max	Output pointer for the maximum StreamID.
 *
 * Return:
 *	- E_RMM_OK	StreamID range found successfully.
 *	- E_RMM_INVAL	Invalid manifest data, invalid BDF mapping, or SMMU index
 *			not found.
 */
int rmm_el3_ifc_sid_max(unsigned int smmu_idx, unsigned int *sid_max)
{
	struct root_complex_list *rc_list;
	struct root_complex_info *root_complex;
	uint64_t num_root_complexes;
	unsigned int max = 0U;
	bool found = false;

	assert(sid_max != NULL);
	assert(local_core_manifest != NULL);

	rc_list = &local_core_manifest->plat_root_complex;
	num_root_complexes = rc_list->num_root_complex;
	root_complex = rc_list->root_complex;

	if ((num_root_complexes == 0UL) || (root_complex == NULL)) {
		return E_RMM_INVAL;
	}

	/* Scan all Root Complexes to find matching SMMU index */
	for (uint64_t rc_idx = 0UL; rc_idx < num_root_complexes; rc_idx++) {
		struct root_port_info *rp_info;
		uint32_t num_root_ports;

		rp_info = root_complex[rc_idx].root_ports;
		num_root_ports = root_complex[rc_idx].num_root_ports;

		if ((num_root_ports == 0U) || (rp_info == NULL)) {
			return E_RMM_INVAL;
		}

		/* Iterate over all Root Ports */
		for (uint32_t rp_idx = 0U; rp_idx < num_root_ports; rp_idx++) {
			struct bdf_mapping_info *bdf_info =
						rp_info[rp_idx].bdf_mappings;
			uint32_t num_bdf_mappings =
						rp_info[rp_idx].num_bdf_mappings;

			if ((num_bdf_mappings == 0U) || (bdf_info == NULL)) {
				continue;
			}

			/* Iterate over all BDF Mappings */
			for (uint32_t map_idx = 0U;
			     map_idx < num_bdf_mappings; map_idx++) {
				/*
				 * Validate the BDF Mapping Info structure:
				 * mapping_base must be less than or equal to mapping_top.
				 */
				if (bdf_info[map_idx].mapping_base >
					bdf_info[map_idx].mapping_top) {
					return E_RMM_INVAL;
				}

				/* Check for matching SMMU index */
				if (smmu_idx == (unsigned int)bdf_info[map_idx].smmu_idx) {
					/* Top of BDF mapping (inclusive) */
					unsigned int top =
						(unsigned int)bdf_info[map_idx].mapping_top +
						((unsigned int)bdf_info[map_idx].mapping_off << 16);

					found = true;

					/* Update maximum if 'top' is larger */
					if (top > max) {
						max = top;
					}
				}
			}
		}
	}

	/* SMMU index not found in this Root Complex */
	if (!found) {
		return E_RMM_INVAL;
	}

	*sid_max = max;
	return E_RMM_OK;
}
