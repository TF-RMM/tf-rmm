/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef REALM_H
#define REALM_H

#include <assert.h>
#include <measurement.h>
#include <memory.h>
#include <rec.h>
#include <s2tt.h>

#define REALM_NEW		0U
#define REALM_ACTIVE		1U
#define REALM_SYSTEM_OFF	2U

/* struct rd is protected by the rd granule lock */
struct rd {
	/*
	 * 'state' & 'rec_count' are only accessed through dedicated
	 * primitives where the following rules apply:
	 *
	 * (1) To write the value, the RMI handler must hold the rd granule
	 *     lock and use a single copy atomic store with release semantics.
	 *
	 * (2) To read the value, the RMI handler must either:
	 *     - Hold the rd granule lock and use a 64-bit single copy
	 *       atomic load, or
	 *     - Hold the rd reference count and use a 64-bit single copy
	 *       atomic load with acquire semantics.
	 *
	 * Other members of the structure are accessed with rd granule lock held.
	 */
	/* 64-bit variable accessed with READ64/WRITE64/ACQUIRE semantic */
	unsigned long state;

	/* Reference count */
	unsigned long rec_count;

	/* Realm measurement 8 bytes aligned */
	unsigned char measurement[MEASUREMENT_SLOT_NR][MAX_MEASUREMENT_SIZE];

	/* Stage 2 configuration of the Realm */
	struct s2tt_context s2_ctx;

	/* Number of auxiliary REC granules for the Realm */
	unsigned int num_rec_aux;

	/* Algorithm to use for measurements */
	enum hash_algo algorithm;

	/* PMU enabled flag */
	bool pmu_enabled;

	/* Number of PMU counters */
	unsigned int pmu_num_ctrs;

	/* SIMD configuration */
	struct simd_config simd_cfg;

	/* Realm Personalization Value */
	unsigned char rpv[RPV_SIZE];
};
COMPILER_ASSERT((U(offsetof(struct rd, measurement)) & 7U) == 0U);
COMPILER_ASSERT(sizeof(struct rd) <= GRANULE_SIZE);

/*
 * Sets the rd's state while holding the rd granule lock.
 */
static inline void set_rd_state(struct rd *rd, unsigned long state)
{
	SCA_WRITE64_RELEASE(&rd->state, state);
}

/*
 * Gets the rd's state while holding the rd granule lock.
 */
static inline unsigned long get_rd_state_locked(struct rd *rd)
{
	return SCA_READ64(&rd->state);
}

/*
 * Gets the rd's state while holding the rd's reference count, without
 * holding the rd granule lock.
 */
static inline unsigned long get_rd_state_unlocked(struct rd *rd)
{
	return SCA_READ64_ACQUIRE(&rd->state);
}

/*
 * Sets the rd's rec_count while holding the rd granule lock.
 */
static inline void set_rd_rec_count(struct rd *rd, unsigned long val)
{
	SCA_WRITE64_RELEASE(&rd->rec_count, val);
}

/*
 * Gets the rd's rec_count while holding the rd granule lock.
 */
static inline unsigned long get_rd_rec_count_locked(struct rd *rd)
{
	return SCA_READ64(&rd->rec_count);
}

/*
 * Gets the rd's rec_count while holding the rd's reference count, without
 * holding the rd granule lock.
 */
static inline unsigned long get_rd_rec_count_unlocked(struct rd *rd)
{
	return SCA_READ64_ACQUIRE(&rd->rec_count);
}

static inline unsigned long realm_ipa_bits(struct rd *rd)
{
	return rd->s2_ctx.ipa_bits;
}

/*
 * Gets the rd's IPA size.
 */
static inline unsigned long realm_ipa_size(struct rd *rd)
{
	return (1UL << realm_ipa_bits(rd));
}

static inline unsigned long realm_par_size(struct rd *rd)
{
	return (realm_ipa_size(rd) >> 1UL);
}

static inline int realm_rtt_starting_level(struct rd *rd)
{
	return rd->s2_ctx.s2_starting_level;
}

/*
 * Checks that 'address' is within container's parameters.
 *
 * 'container_base' is the start address of the container.
 * 'container_end' is the first address after the container.
 * The container must not overflow.
 */
static inline bool addr_is_contained(unsigned long container_base,
				     unsigned long container_end,
				     unsigned long address)
{
	/* Sanity check the container bounds */
	if (container_base > (container_end - 1UL)) {
		return false;
	}

	return (address >= container_base) && (address <= (container_end - 1UL));
}

/*
 * Checks that region is within container's parameters.
 *
 * 'container_base' is the start address of the container.
 * 'container_end' is the first address after the container.
 * The container must not overflow.
 * 'region_base' is the start address of the region.
 * 'region_end' is the first address after the region.
 * The region must not overflow.
 */
static inline bool region_is_contained(unsigned long container_base,
				       unsigned long container_end,
				       unsigned long region_base,
				       unsigned long region_end)
{
	/* Sanity check the region bounds */
	if (region_base > (region_end - 1UL)) {
		return false;
	}

	return addr_is_contained(container_base, container_end, region_base) &&
	       addr_is_contained(container_base, container_end, region_end - 1UL);
}

static inline unsigned long rec_ipa_size(struct rec *rec)
{
	return (1UL << rec->realm_info.s2_ctx.ipa_bits);
}

static inline unsigned long rec_par_size(struct rec *rec)
{
	return (rec_ipa_size(rec) >> 1U);
}

static inline bool addr_in_rec_par(struct rec *rec, unsigned long addr)
{
	return (addr < rec_par_size(rec));
}

static inline bool region_in_rec_par(struct rec *rec,
				     unsigned long base, unsigned long end)
{
	return region_is_contained(0UL, rec_par_size(rec), base, end);
}

static inline bool addr_in_par(struct rd *rd, unsigned long addr)
{
	return (addr < realm_par_size(rd));
}

enum s2_walk_status {
	/* Successful translation */
	WALK_SUCCESS,
	/* Parameter 'ipa' is unaligned or is not Protected IPA */
	WALK_INVALID_PARAMS,
	/* Mapping is not in the page table */
	WALK_FAIL
};

struct s2_walk_result {
	unsigned long pa;
	unsigned long rtt_level;
	enum ripas ripas_val;
	struct granule *llt;
};

enum s2_walk_status realm_ipa_to_pa(struct rec *rec,
				    unsigned long ipa,
				    struct s2_walk_result *s2_walk);

enum s2_walk_status realm_ipa_get_ripas(struct rec *rec, unsigned long start,
					unsigned long end, unsigned long *top,
					enum ripas *ripas_ptr);
#endif /* REALM_H */
