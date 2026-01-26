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

/*
 * Calculate SMMU memory requirements.
 * For each SMMU with max StreamID bits (32), worst case:
 * - Driver + devices: 1 granule (shared across all SMMUs)
 * - Command queue: 1 granule
 * - Event queue: 1 granule
 * - L1 stream table: up to (2^(32-SMMU_STRTAB_SPLIT) * 8 bytes), rounded to granule alignment
 * - L2 stream tables: 2^(32-SMMU_STRTAB_SPLIT) granules (one per L1 entry)
 * - SID bitmap: round_up((2^32 / BITS_PER_UL) * 8, GRANULE_SIZE)
 * - l1std_cnt: round_up(2^(32-SMMU_STRTAB_SPLIT) * 2, GRANULE_SIZE)
 *
 * Typical case with streamid_bits = 16:
 *   L1 entries = 2^10 = 1024
 *   L1 table = 2 granule
 *   L2 tables = 1024 granules = 4MB
 *   SID bitmap = 1 granule
 *   l1std_cnt = 1 granule
 *   Total per SMMU (typical): ~4MB + 12KB
 */
#ifndef SMMU_STRTAB_SPLIT
#define SMMU_STRTAB_SPLIT 6U
#endif

#define SMMU_MEM_SIZE(num_smmus, streamid_bits, split) \
	((num_smmus) != 0U ? \
		(GRANULE_SIZE + /* Driver + devices (shared) */ \
		(num_smmus) * ( \
			(2U * GRANULE_SIZE) + /* Command and Event queues */ \
			round_up((UL(1) << ((streamid_bits) - (split))) * 8U, GRANULE_SIZE) + /* L1 table */ \
			((UL(1) << ((streamid_bits) - (split))) * GRANULE_SIZE) + /* L2 tables */ \
			round_up((UL(1) << (streamid_bits)) / 8U, GRANULE_SIZE) + /* SID bitmap */ \
			round_up((UL(1) << ((streamid_bits) - (split))) * 2U, GRANULE_SIZE))) /* l1std_cnt */ \
		: 0UL)

/* This macro calculates pages needed based on RMM_VA_POOL_SIZE */
#define RESERVE_MEM_SIZE(nr_gr, nr_ncoh_gr, cmn_xlat)			\
	(round_up((nr_gr) * sizeof(struct granule), GRANULE_SIZE) + \
	round_up((nr_ncoh_gr) * sizeof(struct dev_granule), GRANULE_SIZE) + \
	(((RMM_VA_POOL_SIZE / UL(0x40000000)) * 513U + 1U) * GRANULE_SIZE) + /* VA space pages: (GB * 513) + 1 */ \
	(((cmn_xlat) + 5U) * GRANULE_SIZE) + \
	GLOB_DATA_MAX_SIZE + /* glob_data granule */ \
	SMMU_MEM_SIZE(RMM_MAX_SMMUS, 16U, SMMU_STRTAB_SPLIT)) /* SMMU allocations */

/* Reserve memory for RMM compatibility */
int plat_compat_reserve_memory(size_t size, uint64_t *arg);

/* Set the reserved memory region for RMM compatibility */
void plat_cmn_compat_reserve_mem_init(struct rmm_el3_compat_callbacks *cb,
			void *base_addr, size_t size);

#endif /* PLAT_COMPAT_MEM_H */
