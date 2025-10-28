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
#include <plat_common.h>
#include <rmm_el3_ifc.h>
#include <string.h>
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

/* Used for one RootPort with BDF=0 to set ECAP to DVSEC with Arm RME DA */
static uint8_t gbl_pcie_ecam_space[HOST_PCIE_ECAM_SIZE] __aligned(SZ_4K);

unsigned long host_utils_pci_get_ecam_base(void)
{
	return (unsigned long)&gbl_pcie_ecam_space;
}

int host_utils_pci_rp_dvsec_setup(uint16_t rp_id)
{
	struct dvsec_rme_da *dvsec;

	if (rp_id != 0) {
		ERROR("Host only supports RP id 0\n");
		return -1;
	}

	dvsec = (struct dvsec_rme_da *)&gbl_pcie_ecam_space[PCIE_ECAP_START];

	dvsec->ech = PCIE_ECH_ID_DVSEC;
	dvsec->dvsec_hdr1 = DVSEC_VENDOR_ID_ARM;
	dvsec->dvsec_hdr2 = DVSEC_ID_RME_DA;

	return 0;
}
