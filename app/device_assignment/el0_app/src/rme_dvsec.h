/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef RME_DVSEC_H
#define RME_DVSEC_H

#include <stdbool.h>

/* PCI RootPort Extended Capability RMEDA registers offset */

/*
 * Extended Capability Header
 * DVSEC Headers
 * RME-DA Control registers
 */
#define PCIE_ECAP_ECH_OFFSET			U(0)
#define PCIE_ECAP_DVSEC_HDR1_OFFSET		U(4)
#define PCIE_ECAP_DVSEC_HDR2_OFFSET		U(8)
#define PCIE_ECAP_DVSEC_RME_DA_CTL_REG1_OFFSET	U(12)
#define PCIE_ECAP_DVSEC_RME_DA_CTL_REG2_OFFSET	U(16)

/* PCIe Extended Capability Header */
#define PCIE_ECH_ID_SHIFT			U(0)
#define PCIE_ECH_ID_WIDTH			U(16)
#define PCIE_ECH_CAP_VER_SHIFT			U(16)
#define PCIE_ECH_CAP_VER_WIDTH			U(4)
#define PCIE_ECH_NEXT_CAP_OFFSET_SHIFT		U(20)
#define PCIE_ECH_NEXT_CAP_OFFSET_WIDTH		U(12)

/* PCIe Extended Capability Header - Values */
#define PCIE_ECH_ID_DVSEC			U(0x23)
#define PCIE_ECH_CAP_VER_1			U(0x1)

/* RME-DA DVSEC Header1 */
#define DVSEC_HDR1_VENDOR_ID_SHIFT		U(0)
#define DVSEC_HDR1_VENDOR_ID_WIDTH		U(16)
#define DVSEC_HDR1_REVISION_SHIFT		U(16)
#define DVSEC_HDR1_REVISION_WIDTH		U(4)
#define DVSEC_HDR1_LENGTH_SHIFT			U(20)
#define DVSEC_HDR1_LENGTH_WIDTH			U(12)

/* RME-DA DVSEC Header1 - Values */
#define DVSEC_VENDOR_ID_ARM			U(0x13b5)
#define DVSEC_REVISION_0			U(0x0)

/* RME-DA DVSEC Header2 */
#define DVSEC_HDR2_DVSEC_ID_SHIFT		U(0)
#define DVSEC_HDR2_DVSEC_ID_WIDTH		U(16)

/* RME-DA DVSEC Header2 - Values */
#define DVSEC_ID_RME_DA				U(0xFF01)

/* RME-DA Control register 1 */
#define DVSEC_RMEDA_CTL_REG1_TDISP_EN_SHIFT	U(0)
#define DVSEC_RMEDA_CTL_REG1_TDISP_EN_WIDTH	U(1)

/* RME-DA Control register 1 - Values */
#define RME_DA_TDISP_DISABLE			U(0)
#define RME_DA_TDISP_ENABLE			U(1)

/* RME-DA Control register 2. 32 IDE Selective Stream Lock bits */
#define DVSEC_RME_DA_CTL_REG2_SEL_STR_LOCK_SHIFT	U(0)
#define DVSEC_RME_DA_CTL_REG2_SEL_STR_LOCK_WIDTH	U(32)

/* RME DA related DVSEC helpers */
struct dev_assign_info;

/* Initialize Root Port Extended Capability DVEC of type RME DA */
int dvsec_init(struct dev_assign_info *info);
int dvsec_deinit(struct dev_assign_info *info);

/* DVSEC RME DA Stream lock/unlock/is_locked helpers */
int dvsec_stream_lock(struct dev_assign_info *info);
bool dvsec_is_stream_locked(struct dev_assign_info *info);
int dvsec_stream_unlock(struct dev_assign_info *info);

/* DVSEC RME DA TDISP enable/disable/is_enabled helpers */
int dvsec_tdisp_enable(struct dev_assign_info *info);
bool dvsec_is_tdisp_enabled(struct dev_assign_info *info);

#endif /* RME_DVSEC_H */
