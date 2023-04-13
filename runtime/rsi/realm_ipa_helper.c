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
 * [in]   rd		    Pointer to realm descriptor granule.
 * [in]   ipa		    The intermediate physical address of the realm granule.
 * [in]   s2_walk	    Address of s2_walk_result structure to return:
 * [out]  s2_walk.pa	    The physical address of the realm granule.
 * [out]  s2_walk.rtt_level The last level reached by the table walk.
 * [out]  s2_walk.ripas	    RIPAS of s2tte.
 * [out]  s2_walk.destroyed 'true', if s2tte has HIPAS=DESTROYED.
 * [out]  s2_walk.llt	    Pointer to the last level page table which contains
 *			    the mapping of the granule. If function returns with
 *			    WALK_SUCCESS then 'llt' must be unlocked by the caller.
 *			    Lock avoids to destoy the realm granule while RMM
 *			    accessing to it.
 * Returns:
 * WALK_SUCCESS		Translation succeeded.
 * WALK_INVALID_PARAMS	Parameter 'ipa' is unaligned or is not a Protected IPA.
 * WALK_FAIL		Mapping is not in the page table. NS Host needs to fix.
 */
enum s2_walk_status realm_ipa_to_pa(struct rd *rd,
				    unsigned long ipa,
				    struct s2_walk_result *s2_walk)
{
	struct granule *g_table_root;
	struct rtt_walk wi;
	unsigned long s2tte, *ll_table, offset;
	enum s2_walk_status walk_status;

	if (!GRANULE_ALIGNED(ipa) || !addr_in_par(rd, ipa)) {
		return WALK_INVALID_PARAMS;
	}

	/*
	 * SW table walk to find corresponding PA. It handles cases when buffer
	 * is mapped on page level or on block level.
	 *
	 * Todo:
	 * - Page mapping is assumed.
	 */
	g_table_root = rd->s2_ctx.g_rtt;
	granule_lock(g_table_root, GRANULE_STATE_RTT);
	rtt_walk_lock_unlock(g_table_root,
			     realm_rtt_starting_level(rd),
			     realm_ipa_bits(rd),
			     ipa,
			     RTT_PAGE_LEVEL,
			     &wi);

	ll_table = granule_map(wi.g_llt, SLOT_RTT);

	/* Must be unlocked by caller */
	s2_walk->llt = wi.g_llt;
	s2tte = s2tte_read(&ll_table[wi.index]);

	if (!s2tte_is_assigned_ram(s2tte, wi.last_level)) {
		/*
		 * This 'tte' is still not been made valid by the Host.
		 * Depending on the RIPAS value, the caller needs to
		 * emulate a Data Abort back to the Host or return error
		 * back to Realm.
		 */
		s2_walk->rtt_level = wi.last_level;
		if (s2tte_is_destroyed(s2tte)) {
			s2_walk->destroyed = true;
		} else {
			s2_walk->ripas = s2tte_get_ripas(s2tte);
		}
		granule_unlock(wi.g_llt);
		walk_status = WALK_FAIL;
		goto out_unmap_table;
	}

	s2_walk->pa = s2tte_pa(s2tte, wi.last_level);
	offset = ipa & (s2tte_map_size(wi.last_level) - 1UL);
	s2_walk->pa += offset;
	s2_walk->ripas = RIPAS_RAM;

	walk_status = WALK_SUCCESS;

out_unmap_table:
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
 *	[out] @rtt_level:	Value of last level reached by table walk. This
 *				is set in case of WALK_FAIL is returned.
 * Returns:
 *	WALK_SUCCESS:		RIPAS of IPA found
 *	WALK_FAIL:		RIPAS of IPA not found. s2tte has HIPAS=DESTROYED
 */
enum s2_walk_status realm_ipa_get_ripas(struct rec *rec, unsigned long ipa,
					enum ripas *ripas_ptr,
					unsigned long *rtt_level)
{
	unsigned long s2tte, *ll_table;
	struct rtt_walk wi;
	enum s2_walk_status ws;

	assert(ripas_ptr != NULL);
	assert(rtt_level != NULL);
	assert(GRANULE_ALIGNED(ipa));
	assert(addr_in_rec_par(rec, ipa));

	granule_lock(rec->realm_info.g_rtt, GRANULE_STATE_RTT);

	rtt_walk_lock_unlock(rec->realm_info.g_rtt,
			     rec->realm_info.s2_starting_level,
			     rec->realm_info.ipa_bits,
			     ipa, RTT_PAGE_LEVEL, &wi);

	ll_table = granule_map(wi.g_llt, SLOT_RTT);
	s2tte = s2tte_read(&ll_table[wi.index]);

	if (s2tte_is_destroyed(s2tte)) {
		*rtt_level = wi.last_level;
		/*
		 * The IPA has been destroyed by NS Host. Return data_abort back
		 * to NS Host and there is no recovery possible of this Rec
		 * after this.
		 */
		ws = WALK_FAIL;
	} else {
		*ripas_ptr = s2tte_get_ripas(s2tte);
		ws = WALK_SUCCESS;
	}

	buffer_unmap(ll_table);
	granule_unlock(wi.g_llt);

	return ws;
}
