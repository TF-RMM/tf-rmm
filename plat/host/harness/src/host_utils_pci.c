/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch_helpers.h>
#include <assert.h>
#include <debug.h>
#include <errno.h>
#include <gic.h>
#include <host_utils.h>
#include <host_utils_pci.h>
#include <plat_common.h>
#include <rmm_el3_ifc.h>
#include <stdbool.h>
#include <string.h>
#ifndef CBMC
#include <sys/mman.h>
#endif
#include <utils_def.h>

#define PCIE_ECAP_START			U(0x100)
#define HOST_PCIE_ECAM_SIZE		(SZ_4K)

/* PCIe Extended Capability Header - Values */
#define PCIE_ECH_ID_DVSEC		U(0x23)
#define PCIE_ECH_CAP_VER_1		U(0x1)

/* RME-DA DVSEC Header1 - Values */
#define DVSEC_VENDOR_ID_ARM		U(0x13b5)
#define DVSEC_REVISION_0		U(0x0)

/* RME-DA DVSEC Header2 - Values */
#define DVSEC_ID_RME_DA			U(0xFF01)

struct dvsec_rme_da {
	uint32_t ech;
	uint32_t dvsec_hdr1;
	uint32_t dvsec_hdr2;
	uint32_t dvsec_rme_da_ctl_reg1;
	uint32_t dvsec_rme_da_ctl_reg2;
};

#ifndef CBMC
static uintptr_t mmap_ecam_space(void)
{
	size_t map_size = (size_t)SZ_256M + HOST_PCIE_ECAM_SIZE;
	void *map_base;

	map_base = mmap(NULL, map_size, PROT_READ | PROT_WRITE,
			MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
	assert(map_base != MAP_FAILED);

	return round_up((uintptr_t)map_base, (uintptr_t)SZ_256M);
}
#endif

unsigned long host_utils_pci_get_ecam_base(void)
{
	/* Used for one RootPort with BDF=0 to set ECAP to DVSEC with Arm RME DA */
#ifdef CBMC
	static uint8_t ecam_space[HOST_PCIE_ECAM_SIZE] __aligned(SZ_256M);

	return (unsigned long)ecam_space;
#else
	static bool ecam_initialized;
	static uintptr_t ecam_space;

	if (!ecam_initialized) {
		ecam_space = mmap_ecam_space();
		ecam_initialized = true;
	}

	return ecam_space;
#endif
}

unsigned long host_utils_pci_get_ecam_base_1(void)
{
	/* Second ECAM space for second root complex (connected to SMMU 1) */
#ifdef CBMC
	static uint8_t ecam_space[HOST_PCIE_ECAM_SIZE] __aligned(SZ_256M);

	return (unsigned long)ecam_space;
#else
	static bool ecam_initialized;
	static uintptr_t ecam_space;

	if (!ecam_initialized) {
		ecam_space = mmap_ecam_space();
		ecam_initialized = true;
	}

	return ecam_space;
#endif
}

int host_utils_pci_rp_dvsec_setup(uint16_t rp_id)
{
	struct dvsec_rme_da *dvsec;
	uint8_t *ecam_space;

	if (rp_id != 0) {
		ERROR("Host only supports RP id 0\n");
		return -1;
	}

	ecam_space = (uint8_t *)host_utils_pci_get_ecam_base();
	dvsec = (struct dvsec_rme_da *)&ecam_space[PCIE_ECAP_START];

	dvsec->ech = PCIE_ECH_ID_DVSEC;
	dvsec->dvsec_hdr1 = DVSEC_VENDOR_ID_ARM;
	dvsec->dvsec_hdr2 = DVSEC_ID_RME_DA;

	return 0;
}

/*
 * PCIe Root Complex topology for BDF-to-SMMU resolution.
 * RC 0: ECAM = gbl_pcie_ecam_space, segment 0, covers BDF [0x0000, 0xFFFF) -> SMMU 0
 * RC 1: ECAM = gbl_pcie_ecam_space_1, segment 1, covers BDF [0x0000, 0xFFFF) -> SMMU 1
 */
static struct bdf_mapping_info host_bdf_mappings_0[1U];
static struct root_port_info host_root_ports_0[1U];
static struct bdf_mapping_info host_bdf_mappings_1[1U];
static struct root_port_info host_root_ports_1[1U];
static struct root_complex_info host_root_complex_info[2U];

void host_utils_pci_setup_root_complex(struct root_complex_list *rc_list)
{
	/*
	 * Root Complex 0: segment 0, one root port (id=0),
	 *   BDF mapping [0x0000, 0xFFFF) -> SMMU 0, offset 0.
	 *   This covers BDF 0x100 (bus=1, dev=0, func=0).
	 *
	 * Root Complex 1: segment 1, one root port (id=0),
	 *   BDF mapping [0x0000, 0xFFFF) -> SMMU 1, offset 0.
	 */
	host_bdf_mappings_0[0].mapping_base = 0x0000U;
	host_bdf_mappings_0[0].mapping_top = 0xFFFFU;
	host_bdf_mappings_0[0].mapping_off = 0x0000U;
	host_bdf_mappings_0[0].smmu_idx = 0U;

	host_root_ports_0[0].root_port_id = 0U;
	host_root_ports_0[0].padding = 0U;
	host_root_ports_0[0].num_bdf_mappings = 1U;
	host_root_ports_0[0].bdf_mappings = host_bdf_mappings_0;

	host_bdf_mappings_1[0].mapping_base = 0x0000U;
	host_bdf_mappings_1[0].mapping_top = 0xFFFFU;
	host_bdf_mappings_1[0].mapping_off = 0x0000U;
	host_bdf_mappings_1[0].smmu_idx = 1U;

	host_root_ports_1[0].root_port_id = 0U;
	host_root_ports_1[0].padding = 0U;
	host_root_ports_1[0].num_bdf_mappings = 1U;
	host_root_ports_1[0].bdf_mappings = host_bdf_mappings_1;

	host_root_complex_info[0].ecam_base =
		(uint64_t)host_utils_pci_get_ecam_base();
	host_root_complex_info[0].segment = 0U;
	host_root_complex_info[0].num_root_ports = 1U;
	host_root_complex_info[0].root_ports = host_root_ports_0;

	host_root_complex_info[1].ecam_base =
		(uint64_t)host_utils_pci_get_ecam_base_1();
	host_root_complex_info[1].segment = 1U;
	host_root_complex_info[1].num_root_ports = 1U;
	host_root_complex_info[1].root_ports = host_root_ports_1;

	rc_list->num_root_complex = 2UL;
	rc_list->rc_info_version = 0U;
	rc_list->padding = 0U;
	rc_list->root_complex = host_root_complex_info;
	rc_list->checksum = 0UL;
}
