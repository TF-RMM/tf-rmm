/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <assert.h>
#include <buffer.h>
#include <debug.h>
#include <feature.h>
#include <granule.h>
#include <measurement.h>
#include <realm.h>
#include <simd.h>
#include <smc-handler.h>
#include <smc-rmi.h>
#include <smc.h>
#include <stddef.h>
#include <string.h>
#include <table.h>
#include <vmid.h>

#define RMM_FEATURE_MIN_IPA_SIZE	PARANGE_0000_WIDTH

unsigned long smc_realm_activate(unsigned long rd_addr)
{
	struct rd *rd;
	struct granule *g_rd;
	unsigned long ret;

	g_rd = find_lock_granule(rd_addr, GRANULE_STATE_RD);
	if (g_rd == NULL) {
		return RMI_ERROR_INPUT;
	}

	rd = granule_map(g_rd, SLOT_RD);
	assert(rd != NULL);

	if (get_rd_state_locked(rd) == REALM_STATE_NEW) {
		set_rd_state(rd, REALM_STATE_ACTIVE);
		ret = RMI_SUCCESS;
	} else {
		ret = RMI_ERROR_REALM;
	}
	buffer_unmap(rd);

	granule_unlock(g_rd);

	return ret;
}

static bool get_realm_params(struct rmi_realm_params *realm_params,
				unsigned long realm_params_addr)
{
	bool ns_access_ok;
	struct granule *g_realm_params;

	g_realm_params = find_granule(realm_params_addr);
	if ((g_realm_params == NULL) || (g_realm_params->state != GRANULE_STATE_NS)) {
		return false;
	}

	ns_access_ok = ns_buffer_read(SLOT_NS, g_realm_params, 0U,
				      sizeof(*realm_params), realm_params);

	return ns_access_ok;
}

/*
 * See the library pseudocode
 * aarch64/translation/vmsa_faults/AArch64.S2InconsistentSL on which this is
 * modeled.
 */
static bool s2_inconsistent_sl(unsigned int ipa_bits, int sl)
{
	unsigned int levels = (unsigned int)(RTT_PAGE_LEVEL - sl);
	unsigned int sl_min_ipa_bits, sl_max_ipa_bits;

	/*
	 * The maximum number of concatenated tables is 16,
	 * hence we are adding 4 to the 'sl_max_ipa_bits'.
	 */
	sl_min_ipa_bits = levels * S2TTE_STRIDE + GRANULE_SHIFT + 1U;
	sl_max_ipa_bits = sl_min_ipa_bits + (S2TTE_STRIDE - 1U) + 4U;

	return ((ipa_bits < sl_min_ipa_bits) || (ipa_bits > sl_max_ipa_bits));
}

static bool validate_ipa_bits_and_sl(unsigned int ipa_bits, long sl)
{
	if ((ipa_bits < MIN_IPA_BITS) || (ipa_bits > MAX_IPA_BITS)) {
		return false;
	}

	if ((sl < MIN_STARTING_LEVEL) || (sl > RTT_PAGE_LEVEL)) {
		return false;
	}

	/*
	 * We assume ARMv8.4-TTST is supported with RME so the only SL
	 * configuration we need to check with 4K granules is SL == 0 following
	 * the library pseudocode aarch64/translation/vmsa_faults/AArch64.S2InvalidSL.
	 *
	 * Note that this only checks invalid SL values against the properties
	 * of the hardware platform, other misconfigurations between IPA size
	 * and SL is checked in s2_inconsistent_sl.
	 */
	if ((sl == 0L) && (max_ipa_size() < 44U)) {
		return false;
	}

	return !s2_inconsistent_sl(ipa_bits, (int)sl);
}

static unsigned int s2_num_root_rtts(unsigned int ipa_bits, int sl)
{
	unsigned int levels = (unsigned int)(RTT_PAGE_LEVEL - sl);
	unsigned int sl_ipa_bits;

	/* First calculate how many bits can be resolved without concatenation */
	sl_ipa_bits = levels * S2TTE_STRIDE /* Bits resolved by table walk without SL */
		      + GRANULE_SHIFT	    /* Bits directly mapped to OA */
		      + S2TTE_STRIDE;	    /* Bits resolved by single SL */

	if (sl_ipa_bits >= ipa_bits) {
		return 1U;
	}

	return (unsigned int)(1U << (ipa_bits - sl_ipa_bits));
}

/*
 * Initialize the starting level of stage 2 translation tables.
 *
 * The protected half of the IPA space is initialized to
 * unassigned_empty type of s2tte.
 * The unprotected half of the IPA space is initialized to
 * unassigned_ns type of s2tte.
 * The remaining entries are not initialized.
 */
static void init_s2_starting_level(struct rd *rd)
{
	unsigned long current_ipa = 0U;
	struct granule *g_rtt = rd->s2_ctx.g_rtt;
	unsigned int levels = RTT_PAGE_LEVEL - rd->s2_ctx.s2_starting_level;

	/*
	 * The size of the IPA space that is covered by one S2TTE at
	 * the starting level.
	 */
	unsigned long sl_entry_map_size =
			1UL << (levels * S2TTE_STRIDE + GRANULE_SHIFT);

	for (unsigned int rtt = 0U; rtt < rd->s2_ctx.num_root_rtts; rtt++) {
		unsigned long *s2tt = granule_map(g_rtt, SLOT_RTT);

		assert(s2tt != NULL);

		for (unsigned int rtte = 0U; rtte < S2TTES_PER_S2TT; rtte++) {
			if (addr_in_par(rd, current_ipa)) {
				s2tt[rtte] = s2tte_create_unassigned_empty();
			} else {
				s2tt[rtte] = s2tte_create_unassigned_ns();
			}

			current_ipa += sl_entry_map_size;
			if (current_ipa == realm_ipa_size(rd)) {
				buffer_unmap(s2tt);
				return;
			}

		}
		buffer_unmap(s2tt);
		g_rtt++;
	}

	/*
	 * We have come to the end of starting level s2tts but we haven't
	 * reached the ipa size.
	 */
	assert(false);
}

static bool validate_realm_params(struct rmi_realm_params *p)
{
	unsigned long feat_reg0 = get_feature_register_0();

	/* Validate LPA2 flag */
	if ((EXTRACT(RMI_REALM_FLAGS_LPA2, p->flags) == RMI_FEATURE_TRUE) &&
	    (EXTRACT(RMM_FEATURE_REGISTER_0_LPA2, feat_reg0) ==
							RMI_FEATURE_FALSE)) {
		return false;
	}

	/* Validate S2SZ field */
	if ((p->s2sz < RMM_FEATURE_MIN_IPA_SIZE) ||
	    (p->s2sz > EXTRACT(RMM_FEATURE_REGISTER_0_S2SZ, feat_reg0))) {
		return false;
	}

	/* Validate number of breakpoints */
	if ((p->num_bps !=
		EXTRACT(RMM_FEATURE_REGISTER_0_NUM_BPS, feat_reg0)) ||
	    (p->num_wps !=
		EXTRACT(RMM_FEATURE_REGISTER_0_NUM_WPS, feat_reg0))) {
		return false;
	}

	/* Validate RMI_REALM_FLAGS_SVE flag */
	if (EXTRACT(RMI_REALM_FLAGS_SVE, p->flags) == RMI_FEATURE_TRUE) {
		if (EXTRACT(RMM_FEATURE_REGISTER_0_SVE_EN, feat_reg0) ==
						      RMI_FEATURE_FALSE) {
			return false;
		}

		/* Validate SVE_VL value */
		if (p->sve_vl >
			EXTRACT(RMM_FEATURE_REGISTER_0_SVE_VL, feat_reg0)) {
			return false;
		}
	}

	/*
	 * Skip validation of RMI_REALM_FLAGS_PMU flag
	 * as RMM always assumes that PMUv3p7+ is present.
	 */

	/* Validate number of PMU counters if PMUv3 is enabled */
	if ((EXTRACT(RMI_REALM_FLAGS_PMU, p->flags) == RMI_FEATURE_TRUE) &&
	    (p->pmu_num_ctrs !=
		EXTRACT(RMM_FEATURE_REGISTER_0_PMU_NUM_CTRS, feat_reg0))) {
		return false;
	}

	if (!validate_ipa_bits_and_sl(p->s2sz, p->rtt_level_start)) {
		return false;
	}

	if (s2_num_root_rtts(p->s2sz, (int)p->rtt_level_start) !=
						p->rtt_num_start) {
		return false;
	}

	/*
	 * TODO: Check the VMSA configuration which is either static for the
	 * RMM or per realm with the supplied parameters and store the
	 * configuration on the RD, and it can potentially be copied into RECs
	 * later.
	 */

	switch (p->algorithm) {
	case RMI_HASH_SHA_256:
	case RMI_HASH_SHA_512:
		break;
	default:
		return false;
	}

	/* Check VMID collision and reserve it atomically if available */
	return vmid_reserve((unsigned int)p->vmid);
}

/*
 * Update the realm measurement with the realm parameters.
 */
static void realm_params_measure(struct rd *rd,
				 struct rmi_realm_params *realm_params)
{
	/* By specification realm_params is 4KB */
	unsigned char buffer[SZ_4K] = {0};
	struct rmi_realm_params *realm_params_measured =
		(struct rmi_realm_params *)&buffer[0];

	realm_params_measured->algorithm = realm_params->algorithm;
	/* TODO: Add later */
	/* realm_params_measured->features_0 = realm_params->features_0; */

	/* Measure relevant realm params this will be the init value of RIM */
	measurement_hash_compute(rd->algorithm,
			       buffer,
			       sizeof(buffer),
			       rd->measurement[RIM_MEASUREMENT_SLOT]);
}

static void free_sl_rtts(struct granule *g_rtt, unsigned int num_rtts)
{
	unsigned int i;

	for (i = 0U; i < num_rtts; i++) {
		struct granule *g = g_rtt + i;

		granule_lock(g, GRANULE_STATE_RTT);
		granule_memzero(g, SLOT_RTT);
		granule_unlock_transition(g, GRANULE_STATE_DELEGATED);
	}
}

static bool find_lock_rd_granules(unsigned long rd_addr,
				  struct granule **p_g_rd,
				  unsigned long rtt_base_addr,
				  unsigned int num_rtts,
				  struct granule **p_g_rtt_base)
{
	struct granule *g_rd = NULL, *g_rtt_base = NULL;
	unsigned int i = 0U;

	if (rd_addr < rtt_base_addr) {
		g_rd = find_lock_granule(rd_addr, GRANULE_STATE_DELEGATED);
		if (g_rd == NULL) {
			goto out_err;
		}
	}

	for (; i < num_rtts; i++) {
		unsigned long rtt_addr = rtt_base_addr + i * GRANULE_SIZE;
		struct granule *g_rtt;

		g_rtt = find_lock_granule(rtt_addr, GRANULE_STATE_DELEGATED);
		if (g_rtt == NULL) {
			goto out_err;
		}

		if (i == 0U) {
			g_rtt_base = g_rtt;
		}
	}

	if (g_rd == NULL) {
		g_rd = find_lock_granule(rd_addr, GRANULE_STATE_DELEGATED);
		if (g_rd == NULL) {
			goto out_err;
		}
	}

	*p_g_rd = g_rd;
	*p_g_rtt_base = g_rtt_base;

	return true;

out_err:
	while (i-- != 0U) {
		granule_unlock(g_rtt_base + i);
	}

	if (g_rd != NULL) {
		granule_unlock(g_rd);
	}

	return false;
}

unsigned long smc_realm_create(unsigned long rd_addr,
			       unsigned long realm_params_addr)
{
	struct granule *g_rd, *g_rtt_base;
	struct rd *rd;
	struct rmi_realm_params p;
	unsigned int i;

	if (!get_realm_params(&p, realm_params_addr)) {
		return RMI_ERROR_INPUT;
	}

	if (!validate_realm_params(&p)) {
		return RMI_ERROR_INPUT;
	}

	/*
	 * At this point VMID is reserved for the Realm
	 *
	 * Check for aliasing between rd_addr and
	 * starting level RTT address(es)
	 */
	if (addr_is_contained(p.rtt_base,
			      p.rtt_base + p.rtt_num_start * GRANULE_SIZE,
			      rd_addr)) {

		/* Free reserved VMID before returning */
		vmid_free((unsigned int)p.vmid);
		return RMI_ERROR_INPUT;
	}

	if (!find_lock_rd_granules(rd_addr, &g_rd, p.rtt_base,
				  p.rtt_num_start, &g_rtt_base)) {
		/* Free reserved VMID */
		vmid_free((unsigned int)p.vmid);
		return RMI_ERROR_INPUT;
	}

	rd = granule_map(g_rd, SLOT_RD);
	assert(rd != NULL);

	set_rd_state(rd, REALM_STATE_NEW);
	set_rd_rec_count(rd, 0UL);
	rd->s2_ctx.g_rtt = find_granule(p.rtt_base);
	rd->s2_ctx.ipa_bits = p.s2sz;
	rd->s2_ctx.s2_starting_level = (int)p.rtt_level_start;
	rd->s2_ctx.num_root_rtts = p.rtt_num_start;
	(void)memcpy(&rd->rpv[0], &p.rpv[0], RPV_SIZE);

	rd->s2_ctx.vmid = (unsigned int)p.vmid;

	rd->num_rec_aux = MAX_REC_AUX_GRANULES;

	rd->sve_enabled = EXTRACT(RMI_REALM_FLAGS_SVE, p.flags) != 0UL;
	if (rd->sve_enabled) {
		rd->sve_vq = (uint8_t)p.sve_vl;
	}

	if (p.algorithm == RMI_HASH_SHA_256) {
		rd->algorithm = HASH_SHA_256;
	} else {
		rd->algorithm = HASH_SHA_512;
	}

	rd->pmu_enabled = EXTRACT(RMI_REALM_FLAGS_PMU, p.flags) != 0UL;
	rd->pmu_num_ctrs = p.pmu_num_ctrs;

	realm_params_measure(rd, &p);

	init_s2_starting_level(rd);

	buffer_unmap(rd);

	granule_unlock_transition(g_rd, GRANULE_STATE_RD);

	for (i = 0U; i < p.rtt_num_start; i++) {
		granule_unlock_transition(g_rtt_base + i, GRANULE_STATE_RTT);
	}

	return RMI_SUCCESS;
}

static unsigned long total_root_rtt_refcount(struct granule *g_rtt,
					     unsigned int num_rtts)
{
	unsigned long refcount = 0UL;
	unsigned int i;

	for (i = 0U; i < num_rtts; i++) {
		struct granule *g = g_rtt + i;

	       /*
		* Lock starting from the RTT root.
		* Enforcing locking order RD->RTT is enough to ensure
		* deadlock free locking guarentee.
		*/
		granule_lock(g, GRANULE_STATE_RTT);
		refcount += g->refcount;
		granule_unlock(g);
	}

	return refcount;
}

unsigned long smc_realm_destroy(unsigned long rd_addr)
{
	struct granule *g_rd;
	struct granule *g_rtt;
	struct rd *rd;
	unsigned int num_rtts;

	/* RD should not be destroyed if refcount != 0. */
	g_rd = find_lock_unused_granule(rd_addr, GRANULE_STATE_RD);
	if (ptr_is_err(g_rd)) {
		switch (ptr_status(g_rd)) {
		case 1U:
			return RMI_ERROR_INPUT;
		case 2U:
			/* RD should not be destroyed if refcount != 0 */
			return RMI_ERROR_REALM;
		default:
			panic();
		}
	}

	rd = granule_map(g_rd, SLOT_RD);
	assert(rd != NULL);

	g_rtt = rd->s2_ctx.g_rtt;
	num_rtts = rd->s2_ctx.num_root_rtts;

	/* Check if granules are unused */
	if (total_root_rtt_refcount(g_rtt, num_rtts) != 0UL) {
		buffer_unmap(rd);
		granule_unlock(g_rd);
		return RMI_ERROR_REALM;
	}

	/*
	 * All the mappings in the Realm have been removed and the TLB caches
	 * are invalidated. Therefore, there are no TLB entries tagged with
	 * this Realm's VMID (in this security state).
	 * Just release the VMID value so it can be used in another Realm.
	 */
	vmid_free(rd->s2_ctx.vmid);
	buffer_unmap(rd);

	free_sl_rtts(g_rtt, num_rtts);

	/* This implictly destroys the measurement */
	granule_memzero(g_rd, SLOT_RD);
	granule_unlock_transition(g_rd, GRANULE_STATE_DELEGATED);

	return RMI_SUCCESS;
}
