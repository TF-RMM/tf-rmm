/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef ARM_DRAM_H
#define ARM_DRAM_H

#include <rmm_el3_ifc.h>
#include <stddef.h>
#include <stdint.h>

/* Maximum number of DRAM banks supported */
#define MAX_DRAM_NUM_BANKS	2UL

/* Arm runtime structures */
struct arm_dram_bank {
	uintptr_t start_addr;		/* start address */
	uintptr_t end_addr;		/* end address */
};

struct arm_dram_layout {
	unsigned long idx_bank_1;	/* start granule index in bank 1 */
	unsigned long num_granules;	/* number of granules */
	struct arm_dram_bank arm_bank[MAX_DRAM_NUM_BANKS];
};

void arm_set_dram_layout(struct ns_dram_info *plat_dram);
struct arm_dram_layout *arm_get_dram_layout(void);

#endif /* ARM_DRAM_H */
