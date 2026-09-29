/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef ARM_MEMORY_H
#define ARM_MEMORY_H

#include <platform_api.h>
#include <rmm_el3_ifc.h>
#include <stddef.h>
#include <stdint.h>

/* Arm platform memory management structures */
struct arm_memory_layout {
	unsigned long num_banks;	/* number of memory banks */
	struct plat_memory_bank bank[PLAT_ARM_MAX_MEM_BANKS];
};

void arm_set_dram_layout(struct memory_info *plat_dram);
void arm_set_dev_layout(struct memory_info *plat_dev, enum dev_coh_type type);
struct arm_memory_layout *arm_get_dram_layout(void);
struct arm_memory_layout *arm_get_dev_ncoh_layout(void);
struct arm_memory_layout *arm_get_dev_coh_layout(void);

#endif /* ARM_MEMORY_H */
