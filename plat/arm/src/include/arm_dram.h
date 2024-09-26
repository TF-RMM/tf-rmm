/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef ARM_DRAM_H
#define ARM_DRAM_H

#include <rmm_el3_ifc.h>
#include <stddef.h>
#include <stdint.h>

/* Arm platform dram management structures */
struct arm_dram_bank {
	uint64_t base;			/* bank base address */
	uint64_t size;			/* size of this bank */
	/* This idx is a cumulative granule count of previous banks */
	uint64_t start_gran_idx;	/* Start granule index for this bank */
};

struct arm_dram_layout {
	unsigned long num_granules;	/* number of granules */
	unsigned long num_banks;	/* number of dram banks */
	struct arm_dram_bank bank[PLAT_ARM_MAX_DRAM_BANKS];
					/* Sorted array of DRAM banks */
};

void arm_set_dram_layout(struct ns_dram_info *plat_dram);
struct arm_dram_layout *arm_get_dram_layout(void);

#endif /* ARM_DRAM_H */
