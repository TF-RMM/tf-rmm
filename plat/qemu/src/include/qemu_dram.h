/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef QEMU_DRAM_H
#define QEMU_DRAM_H

#include <rmm_el3_ifc.h>
#include <stddef.h>
#include <stdint.h>

/* Maximum number of DRAM banks supported */
#define MAX_DRAM_NUM_BANKS	1UL

/* QEMU runtime structures */
struct qemu_dram_layout {
	uintptr_t start_addr;
	uintptr_t end_addr;
	unsigned long num_granules;
};

void qemu_set_dram_layout(struct ns_dram_info *plat_dram);
struct qemu_dram_layout *qemu_get_dram_layout(void);

#endif /* QEMU_DRAM_H */
