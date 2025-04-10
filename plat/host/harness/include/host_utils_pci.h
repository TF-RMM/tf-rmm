/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef HOST_PCI_UTILS_H
#define HOST_PCI_UTILS_H

#include <stddef.h>
#include <types.h>

unsigned long host_utils_pci_get_ecam_base(void);
int host_utils_pci_rp_dvsec_setup(uint16_t rp_id);

#endif /* HOST_PCI_UTILS_H */
