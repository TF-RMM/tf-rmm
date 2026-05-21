/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef HOST_PCI_UTILS_H
#define HOST_PCI_UTILS_H

#include <stddef.h>
#include <types.h>

struct root_complex_list;

unsigned long host_utils_pci_get_ecam_base(void);
unsigned long host_utils_pci_get_ecam_base_1(void);
int host_utils_pci_rp_dvsec_setup(uint16_t rp_id);
void host_utils_pci_setup_root_complex(struct root_complex_list *rc_list);

#endif /* HOST_PCI_UTILS_H */
