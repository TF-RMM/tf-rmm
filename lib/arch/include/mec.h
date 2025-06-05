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
#include <stdint.h>

/*
 * Before enabling the MMU, the RMM code is written and read with MECID 0, so
 * the only possible value at the moment for RMM is 0.
 */
#define RESERVED_MECID_SYSTEM	0U

/* RMM reserves only a single ID for itself */
#define RESERVED_IDS	1U

/*
 * Note that the actually programmed MECID is shifted
 * by RESERVED_IDS from the param `mecid`. This helps RMM to reserve
 * MECIDs starting from 0 and adhere to the RMM specification which
 * mandates reservation from the maximum MECID values.
 */
#define INTERNAL_MECID(id)	((id) + RESERVED_IDS)

/* MEC helper functions */

void mec_init_mmu(void);
int mec_set_private(unsigned int mecid);
int mec_set_shared(unsigned int mecid);
bool mecid_reserve(unsigned int mecid);
void mecid_free(unsigned int mecid);

/* Initialize Realm MECID for Stage 1 of RMM */
static inline void mec_init_realm_mecid_s1(unsigned int mecid)
{
	(void)mecid;
	if (is_feat_mec_present()) {
		assert((unsigned int)read_mecid_a1_el2() ==
				RESERVED_MECID_SYSTEM);
		write_mecid_a1_el2((unsigned long)INTERNAL_MECID(mecid));
		isb();
	}
}

/* Initialize Realm MECID for Stage 2 of Realm */
static inline void mec_init_realm_mecid_s2(unsigned int mecid)
{
	(void)mecid;
	if (is_feat_mec_present()) {
		assert((unsigned int)read_vmecid_p_el2() ==
				RESERVED_MECID_SYSTEM);
		write_vmecid_p_el2((unsigned long)INTERNAL_MECID(mecid));
		/* No isb() since the following ERET is expected after this */
	}
}

/* Reset Realm MECID registers , both for S1 of RMM and S2 of Realm */
static inline void mec_reset_realm_mecid(void)
{
	if (is_feat_mec_present()) {
		write_mecid_a1_el2((unsigned long)RESERVED_MECID_SYSTEM);
		write_vmecid_p_el2((unsigned long)RESERVED_MECID_SYSTEM);
		isb();
	}
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

#endif /* MEC_H */
