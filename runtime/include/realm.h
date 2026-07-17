/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef REALM_H
#define REALM_H

#include <assert.h>
#include <atomics.h>
#include <dev.h>
#include <measurement.h>
#include <memory.h>
#include <planes.h>
#include <rec.h>
#include <rsi-handler.h>
#include <s2tt.h>
#include <smmuv3.h>

#define REALM_NEW		0U
#define REALM_ACTIVE		1U
#define REALM_SYSTEM_OFF	2U
#define REALM_ZOMBIE		3U

/*
 * Possible values for rtt_s2ap_encoding
 */
#define S2AP_DIRECT_ENC		(false)
#define S2AP_INDIRECT_ENC	(true)

/* struct rd is protected by the rd granule lock */
struct rd {
	/*
	 * 'state_and_count' packs realm state (upper 2 bits) and
	 * active_rec_count (lower 62 bits) into a single 64-bit word.
	 * This allows lock-free atomic transitions using CAS (CASAL):
	 *
	 * - smc_rec_enter: atomically increments count only if state is ACTIVE
	 * - smc_realm_terminate: atomically sets ZOMBIE only if count == 0
	 *
	 * 'rec_count' is accessed through dedicated primitives:
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
	/*
	 * Packed: bits [63:62] = state, bits [61:0] = active_rec_count.
	 * Accessed via CAS (lock-free) or plain atomic load under lock.
	 */
	unsigned long state_and_count;

	/* Reference count */
	unsigned long rec_count;

	/* Realm measurement 8 bytes aligned */
	unsigned char measurement[MEASUREMENT_SLOT_NR][MAX_MEASUREMENT_SIZE];

	/* Realm Instance ID */
	unsigned char realm_instance_id[REALM_INSTANCE_ID_SIZE];

	/* Stage 2 configuration of the Realm */
	struct s2tt_context s2_ctx[MAX_S2_CTXS];

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

	/* Number of auxiliary planes (not counting Plane 0) */
	unsigned int num_aux_planes;

	/*
	 * Flag to indicate if the realm uses a single S2 translation table
	 * tree or if the translation table tree is shared across planes.
	 *
	 * rtt_tree_pp == false: All planes share the same RTT tree.
	 * rtt_tree_pp == true: Each plane has its own RTT tree.
	 */
	bool rtt_tree_pp;

	/*
	 * Flag to indicate if the realm uses indirect or direct permission
	 * encoding into the S2TTEs.
	 */
	bool rtt_s2ap_encoding;

	/*
	 * This field contains a lock per possible overlay index value
	 * which indicates whether the permission associated to that index
	 * can be modified or not.
	 */
	unsigned long overlay_index_lock;

	/* Whether device assignment is enabled for this Realm */
	bool da_enabled;

	/* Reference count of VDEVs assigned to this Realm */
	unsigned long num_vdevs;

	/*
	 * VDEV instances assigned to this Realm. This is a constantly
	 * incrementing counter and used to initialize the VDEV instance ID when
	 * VDEV is assigned to Realm.
	 */
	unsigned long vdev_inst_counter;

	/*
	 * Index of Plane whose stage 2 permissions are observed by ATS
	 * request from devices assigned to the Realm.
	 */
	unsigned long ats_plane;

	/* CMD_SYNC completion state for SMMU TLB invalidations. */
	struct smmuv3_cmd_sync smmu_cmd_sync;
};
COMPILER_ASSERT((U(offsetof(struct rd, measurement)) & 7U) == 0U);
COMPILER_ASSERT((U(offsetof(struct rd, smmu_cmd_sync.completion)) & 3U) == 0U);
COMPILER_ASSERT(sizeof(struct rd) <= GRANULE_SIZE);

/*
 * state_and_count packing:
 *   bits [63:62] = realm state (2 bits, supports values 0-3)
 *   bits [61:0]  = active_rec_count (62 bits)
 */
#define RD_STATE_SHIFT		62U
#define RD_COUNT_MASK		((1UL << RD_STATE_SHIFT) - 1UL)
#define RD_PACK_SC(s, c)	(((unsigned long)(s) << RD_STATE_SHIFT) | (c))
#define RD_UNPACK_STATE(v)	((v) >> RD_STATE_SHIFT)
#define RD_UNPACK_COUNT(v)	((v) & RD_COUNT_MASK)

/*
 * Gets the rd's state while holding the rd granule lock.
 */
static inline unsigned long get_rd_state_locked(struct rd *rd)
{
	return RD_UNPACK_STATE(SCA_READ64(&rd->state_and_count));
}

/*
 * Gets the rd's state while holding the rd's reference count, without
 * holding the rd granule lock.
 */
static inline unsigned long get_rd_state_unlocked(struct rd *rd)
{
	return RD_UNPACK_STATE(SCA_READ64_ACQUIRE(&rd->state_and_count));
}

/*
 * Sets the rd's state via CAS loop. Safe to call even when
 * active_rec_count is being concurrently modified (lock-free).
 * The caller must hold the rd granule lock or otherwise guarantee
 * no concurrent state transitions.
 */
static inline void set_rd_state(struct rd *rd, unsigned long state)
{
	unsigned long old;

	do {
		old = SCA_READ64_ACQUIRE(&rd->state_and_count);
	} while (!atomic_cas_acquire_release_64(
			(uint64_t *)&rd->state_and_count,
			old,
			RD_PACK_SC(state, RD_UNPACK_COUNT(old))));
}

/*
 * Atomically transitions state from @expected_state to @new_state only if
 * the current state matches and active_rec_count == 0.
 * Uses CAS with acquire-release semantics (lock-free).
 * Returns true on success.
 */
static inline bool rd_cas_state_if_count_zero(struct rd *rd,
					      unsigned long expected_state,
					      unsigned long new_state)
{
	uint64_t expected = RD_PACK_SC(expected_state, 0UL);
	uint64_t desired = RD_PACK_SC(new_state, 0UL);

	return atomic_cas_acquire_release_64(
		(uint64_t *)&rd->state_and_count, expected, desired);
}

/*
 * Atomically increments active_rec_count only if the realm state is ACTIVE.
 * Uses CAS with acquire-release semantics (lock-free).
 * Returns true on success, false if realm is not ACTIVE.
 */
static inline bool rd_active_rec_count_inc_if_active(struct rd *rd)
{
	unsigned long old, new_val;

	do {
		old = SCA_READ64_ACQUIRE(&rd->state_and_count);
		if (RD_UNPACK_STATE(old) != REALM_ACTIVE) {
			return false;
		}
		new_val = old + 1UL;
		/* Count overflow into state bits would be catastrophic */
		assert(RD_UNPACK_STATE(new_val) == REALM_ACTIVE);
	} while (!atomic_cas_acquire_release_64(
			(uint64_t *)&rd->state_and_count, old, new_val));

	return true;
}

/*
 * Atomically decrements active_rec_count (unconditional, lock-free).
 * Uses release semantics so that smc_realm_terminate()'s acquire read
 * observes the decrement.
 */
static inline void rd_active_rec_count_dec(struct rd *rd)
{
	uint64_t old = atomic_load_add_release_64((uint64_t *)&rd->state_and_count,
					 (uint64_t)-1LL);

	assert(RD_UNPACK_COUNT(old) > 0UL);
	(void)old;
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

/*
 * Return the number of planes supported by the realm referenced by @rd.
 * This takes into account Plane 0.
 */
static inline unsigned int realm_num_planes(struct rd *rd)
{
#ifndef CBMC
	return rd->num_aux_planes + 1U;
#else
	return 1U;
#endif
}

/*
 * Return the number of S2 contexts supported by the realm referenced by @rd.
 */
static inline unsigned int realm_num_s2_contexts(struct rd *rd)
{
	return realm_num_planes(rd);
}

/*
 * Return the number of S2 RTTs supported by the realm referenced by @rd.
 */
static inline unsigned int realm_num_s2_rtts(struct rd *rd)
{
#ifndef CBMC
	return rd->rtt_tree_pp ? realm_num_s2_contexts(rd) : 1U;
#else
	return 1U;
#endif
}

/*
 * Retrieve a stage 2 context given the Realm Descriptor and the plane ID.
 *
 * Every plane has its own s2tt_context structure, even when using a single
 * translation table. This allows for each plane to store its own overlay
 * permissions inside its translation context.
 *
 * Note that the mapping between PlaneID and s2tt_context ID is:
 *
 * s2tt_context ID = (PlaneID + 1) % realm_num_planes()
 */
static inline struct s2tt_context *plane_to_s2_context(struct rd *rd,
						       unsigned int plane_id)
{
	unsigned int index;

	assert(plane_id < realm_num_planes(rd));

	index = ((plane_id + 1U) % realm_num_planes(rd));
	return &rd->s2_ctx[index];
}

/*
 * Resets rd->num_vdevs to 0.
 */
static inline void rd_vdev_refcount_reset(struct rd *rd)
{
	SCA_WRITE64(&rd->num_vdevs, 0UL);
}

/*
 * Returns rd->num_vdevs while holding the rd granule lock.
 */
static inline unsigned long rd_vdev_refcount_get(struct rd *rd)
{
	return SCA_READ64(&rd->num_vdevs);
}

/*
 * Increases rd->num_vdevs by 1 while holding the rd granule lock.
 */
static inline void rd_vdev_refcount_inc(struct rd *rd)
{
	atomic_add_64(&rd->num_vdevs, 1UL);
}

/*
 * Decreases rd->num_vdevs by 1 while holding the rd granule lock.
 */
static inline void rd_vdev_refcount_dec(struct rd *rd)
{
	atomic_add_64(&rd->num_vdevs, (unsigned long)(-1L));
}

static inline unsigned long realm_ipa_bits(struct rd *rd)
{
	return plane_to_s2_context(rd, PLANE_0_ID)->ipa_bits;
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
	return plane_to_s2_context(rd, PLANE_0_ID)->s2_starting_level;
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
	return (1UL << rec->realm_info.primary_s2_ctx.ipa_bits);
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

static inline void set_perm_immutable(struct rd *rd, unsigned long perm_index)
{
	atomic_bit_set_release_64(&rd->overlay_index_lock, (unsigned int)perm_index);
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
bool realm_mem_lock_map(struct rec *rec, unsigned long ipa,
			void **va, struct granule **llt,
			struct rsi_result *res);

#endif /* REALM_H */
