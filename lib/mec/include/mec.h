/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef MEC_H
#define MEC_H

#include <arch.h>
#include <arch_features.h>
#include <arch_helpers.h>
#include <assert.h>
#include <sizes.h>
#include <spinlock.h>
#include <stdint.h>

/*
 * Before enabling the MMU, the RMM code is written and read with MECID 0, so
 * the only possible value at the moment for RMM is 0.
 */
#define RESERVED_MECID_SYSTEM	0U

/* Avoid MISRA C:2102-20.9 violation */
#ifndef RMM_MEM_SCRUB_METHOD
#define RMM_MEM_SCRUB_METHOD 0
#endif /* RMM_MEM_SCRUB_METHOD */

#if (RMM_MEM_SCRUB_METHOD == 2)
/* Reserve MECID 1 for Sanitizing/Scrubbing Granules */
#define RESERVED_MECID_SCRUB	1U
/* RMM reserves 2 MECIDs ID for itself - 0 for RMM use and 1 for Scrub */
#define RESERVED_IDS	2U
#else
/* RMM reserves only a single ID for itself */
#define RESERVED_IDS	1U
#endif

/*
 * The effective MECID programmed internally is offset by RESERVED_IDS
 * from the `mecid` parameter passed to this component's API.
 *
 * This offset ensures compliance with the RMM specification, which requires
 * that the RMM user interface sees MECID 0 as valid and available for use.
 * Internally, however, RMM itself uses MECID 0, so the offset allows
 * RMM to reserve low MECID values for internal use while presenting
 * a contiguous range starting from 0 to external users.
 *
 * As a result, the user-visible MECID 0 is not actually programmed as 0,
 * but as RESERVED_IDS, effectively hiding the internal reservation.
 */
#define INTERNAL_MECID(id)	((id) + RESERVED_IDS)

#define MECID_WIDTH	U(16)
#define MEC_MAX_COUNT	(U(1) << MECID_WIDTH)
#define MECID_INVALID	U(-1)

#define MECID_ARRAY_SIZE	((MEC_MAX_COUNT) / BITS_PER_UL)

struct mec_state_s {
	/*
	 * Together, the mec_reserved array and the shared_mec value define the
	 * state of all MECs in the system.
	 *
	 * For a given mecid:
	 *
	 * if mecid == shared_mec
	 *     MEC state is SHARED
	 *
	 * if mec_reserved[mecid] == true
	 *     MEC state is PRIVATE_ASSIGNED or SHARED or RESERVED.
	 * else
	 *     MEC state is PRIVATE_UNASSIGNED
	 */
	unsigned long shared_mec_members;
	unsigned int shared_mec;

	spinlock_t shared_mecid_spinlock;

	/* The bitmap for the reserved/used MECID values.*/
	unsigned long mec_reserved[MECID_ARRAY_SIZE];

	/* Indicates whether the mec_state has been initialized */
	bool is_init;
};

/* MEC helper functions */

void mec_init_mmu(void);
void mec_init_state(uintptr_t state, size_t state_size);
unsigned int mecid_max(void);
int mec_set_private(unsigned int mecid);
int mec_set_shared(unsigned int mecid);
bool mecid_reserve(unsigned int mecid);
void mecid_free(unsigned int mecid);

void _mecid_s1_get(unsigned int mecid);
void _mecid_s1_put(void);

/* Initialize Realm MECID for Stage 1 of RMM */
static inline void mec_realm_mecid_s1_init(unsigned int mecid)
{
	(void)mecid;
	/* cppcheck-suppress knownConditionTrueFalse */
	if (!is_feat_mec_present()) {
		return;
	}

	_mecid_s1_get(mecid);
}

/* Reset Realm MECID for Stage 1 of RMM */
static inline void mec_realm_mecid_s1_reset(void)
{
	/* cppcheck-suppress knownConditionTrueFalse */
	if (!is_feat_mec_present()) {
		return;
	}

	_mecid_s1_put();
}

/* Initialize Realm MECID for Stage 2 of Realm */
static inline void mec_realm_mecid_s2_init(unsigned int mecid)
{
	(void)mecid;
	if (is_feat_mec_present()) {
		assert((unsigned int)read_vmecid_p_el2() ==
				RESERVED_MECID_SYSTEM);
		write_vmecid_p_el2((unsigned long)INTERNAL_MECID(mecid));
		/* No isb() since the following ERET is expected after this */
	}
}

/* Initialize Realm MECID for Stage 2 of Realm */
static inline void mec_realm_mecid_s2_reset(void)
{
	if (is_feat_mec_present()) {
		assert(read_vmecid_p_el2() != RESERVED_MECID_SYSTEM);
		write_vmecid_p_el2(RESERVED_MECID_SYSTEM);
		/* No isb() since NS world switch is expected after this */
	}
}

/* Check if both Realm MECID registers for S1 and S2 are reset */
static inline bool is_mec_reset_realm_mecid(void)
{
	/* cppcheck-suppress knownConditionTrueFalse */
	if (!is_feat_mec_present()) {
		return true;
	}

	if ((read_mecid_a1_el2() == RESERVED_MECID_SYSTEM) &&
		(read_vmecid_p_el2() == RESERVED_MECID_SYSTEM)) {
			return true;
	}

	return false;
}

/* Check if Realm MECID for Stage 1 of RMM is initialized */
static inline bool mec_is_realm_mecid_s1_init(void)
{
	if (is_feat_mec_present()) {
		if ((unsigned int)read_mecid_a1_el2() ==
				RESERVED_MECID_SYSTEM) {
			return false;
		}
	}
	return true;
}

/*
 * Check if MECID programmed in Realm S2 is private.
 * This function will be invoked while REC is running.
 */
bool mec_is_realm_mecid_s2_pvt(void);

#if (RMM_MEM_SCRUB_METHOD == 2)
/* Initialize the reserved scrub MECID for Stage 1 of RMM */
static inline void mec_init_scrub_mecid_s1(void)
{
	if (is_feat_mec_present()) {
		assert(read_mecid_a1_el2() == RESERVED_MECID_SYSTEM);
		write_mecid_a1_el2(RESERVED_MECID_SCRUB);
		isb();
	}
}

/* Reset the reserved scrub MECID for Stage 1 of RMM */
static inline void mec_reset_scrub_mecid_s1(void)
{
	if (is_feat_mec_present()) {
		assert(read_mecid_a1_el2() == RESERVED_MECID_SCRUB);
		write_mecid_a1_el2(RESERVED_MECID_SYSTEM);
		isb();
	}
}
#endif /* #if (RMM_MEM_SCRUB_METHOD == 2) */

/*************************************
 * Test API, only used for unit tests
 ************************************/

 /*
  * Reset MEC state to power-on reset values.
  * Only to be used in unit tests.
  */
void mec_test_reset(void);

#endif /* MEC_H */
