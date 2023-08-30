/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <buffer.h>
#include <granule.h>
#include <realm.h>

/**
 * Translate a realm granule IPA to PA.
 *
 * Parameters:
 * [in]   rec		    Pointer to REC granule.
 * [in]   ipa		    The intermediate physical address of the realm
 *			    granule.
 * [in]   s2_walk	    Address of s2_walk_result structure to return:
 * [out]  s2_walk.pa	    The physical address of the realm granule.
 * [out]  s2_walk.rtt_level The last level reached by the table walk.
 * [out]  s2_walk.ripas_val RIPAS of s2tte.
 * [out]  s2_walk.llt	    Pointer to the last level page table which contains
 *			    the mapping of the granule. If function returns with
 *			    WALK_SUCCESS then 's2_walk.llt' must be unlocked by
 *			    the caller. Lock avoids to destoy the realm granule
 *			    while RMM accessing to it.
 * Returns:
 * WALK_SUCCESS		Translation succeeded. The IPA is a valid mapping
 *			(hipas is RMI_ASSIGNED and ripas is RIPAS_RAM).
 *			All members of 's2_walk' are updated.
 *			The rtt granule that is pointed to by 's2_walk->pa'
 *			is locked.
 * WALK_INVALID_PARAMS	Parameter 'ipa' is unaligned to granule size or is not
 *			a Protected IPA, 's2_walk' structure is not updated.
 * WALK_FAIL		Mapping is not in the page table (either hipas is not
 *			RMI_ASSIGNED or ripas is not RIPAS_RAM).
 *			Only 's2_walk.rtt_level' and 's2_walk.ripas' are
 *			updated. NS Host needs to fix.
 */
enum s2_walk_status realm_ipa_to_pa(struct rec *rec,
				    unsigned long ipa,
				    struct s2_walk_result *s2_walk)
{
	struct granule *g_table_root;
	struct rtt_walk wi;
	unsigned long s2tte, *ll_table, offset;
	enum s2_walk_status walk_status;

	if (!GRANULE_ALIGNED(ipa) || !addr_in_rec_par(rec, ipa)) {
		return WALK_INVALID_PARAMS;
	}

	g_table_root = rec->realm_info.g_rtt;
	granule_lock(g_table_root, GRANULE_STATE_RTT);
	rtt_walk_lock_unlock(g_table_root,
			     rec->realm_info.s2_starting_level,
			     rec->realm_info.ipa_bits,
			     ipa,
			     RTT_PAGE_LEVEL,
			     &wi);

	ll_table = granule_map(wi.g_llt, SLOT_RTT);
	assert(ll_table != NULL);

	s2tte = s2tte_read(&ll_table[wi.index]);

	if (s2tte_is_assigned_ram(s2tte, wi.last_level)) {
		s2_walk->llt = wi.g_llt; /* Must be unlocked by caller */
		s2_walk->pa = s2tte_pa(s2tte, wi.last_level);
		offset = ipa & (s2tte_map_size(wi.last_level) - 1UL);
		s2_walk->pa += offset;
		s2_walk->ripas_val = RIPAS_RAM;
		walk_status = WALK_SUCCESS;
	} else {
		if (s2tte_is_unassigned_destroyed(s2tte) ||
		    s2tte_is_assigned_destroyed(s2tte, wi.last_level)) {
			s2_walk->ripas_val = RIPAS_DESTROYED;
		} else if (s2tte_is_unassigned_ram(s2tte)) {
			s2_walk->ripas_val = RIPAS_RAM;
		} else {
			/*
			 * Only unassigned_empty & assigned_empty
			 * are left as an option.
			 */
			s2_walk->ripas_val = RIPAS_EMPTY;
		}

		granule_unlock(wi.g_llt);
		walk_status = WALK_FAIL;
	}

	s2_walk->rtt_level = (unsigned long)wi.last_level;

	buffer_unmap(ll_table);
	return walk_status;
}

/*
 * Get RIPAS of IPA
 *
 * Parameters:
 *	[in]  @rec:		Pointer to the rec
 *	[in]  @ipa:		IPA for which RIPAS is queried.
 *	[out] @ripas_ptr:	RIPAS value returned for the IPA. This is set in
 *				case of WALK_SUCCESS is returned.
 * Returns:
 *	WALK_SUCCESS:		RIPAS of IPA found
 *	WALK_FAIL:		RIPAS of IPA not found
 */
enum s2_walk_status realm_ipa_get_ripas(struct rec *rec, unsigned long ipa,
					enum ripas *ripas_ptr)
{
	unsigned long s2tte, *ll_table;
	struct rtt_walk wi;
	enum s2_walk_status ws;

	assert(ripas_ptr != NULL);
	assert(GRANULE_ALIGNED(ipa));
	assert(addr_in_rec_par(rec, ipa));

	granule_lock(rec->realm_info.g_rtt, GRANULE_STATE_RTT);

	rtt_walk_lock_unlock(rec->realm_info.g_rtt,
			     rec->realm_info.s2_starting_level,
			     rec->realm_info.ipa_bits,
			     ipa, RTT_PAGE_LEVEL, &wi);

	ll_table = granule_map(wi.g_llt, SLOT_RTT);
	assert(ll_table != NULL);

	s2tte = s2tte_read(&ll_table[wi.index]);
	if (!s2tte_has_ripas(s2tte, wi.last_level)) {
		ws = WALK_FAIL;
		goto out_unmap_unlock;
	}

	*ripas_ptr = s2tte_is_assigned_ram(s2tte, wi.last_level) ?
			RIPAS_RAM : s2tte_get_ripas(s2tte);
	ws = WALK_SUCCESS;

out_unmap_unlock:
	buffer_unmap(ll_table);
	granule_unlock(wi.g_llt);

	return ws;
}
