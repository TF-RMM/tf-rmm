/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef PLAT_COMPAT_MEM_H
#define PLAT_COMPAT_MEM_H

#include <glob_data.h>
#include <granule_types.h>
#include <rmm_el3_compat.h>

/* Platform header for RMM EL3 compatibility */

/* This macro calculates pages needed based on RMM_VA_POOL_SIZE */
#define RESERVE_MEM_SIZE(nr_gr, nr_ncoh_gr, cmn_xlat)			\
	(round_up((nr_gr) * sizeof(struct granule), GRANULE_SIZE) + \
	round_up((nr_ncoh_gr) * sizeof(struct dev_granule), GRANULE_SIZE) + \
	(((RMM_VA_POOL_SIZE / UL(0x40000000)) * 513U + 1U) * GRANULE_SIZE) + /* VA space pages: (GB * 513) + 1 */ \
	(((cmn_xlat) + 5U) * GRANULE_SIZE) + \
	GLOB_DATA_MAX_SIZE) /* glob_data granule */

/* Reserve memory for RMM compatibility */
int plat_compat_reserve_memory(size_t size, uint64_t *arg);

/* Set the reserved memory region for RMM compatibility */
void plat_cmn_compat_reserve_mem_init(struct rmm_el3_compat_callbacks *cb,
			void *base_addr, size_t size);

#endif /* PLAT_COMPAT_MEM_H */
