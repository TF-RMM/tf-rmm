/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch_helpers.h>
#include <assert.h>
#include <bitmap.h>
#include <buffer.h>
#include <dev_granule.h>
#include <granule.h>
#include <ripas.h>
#include <s2ap_ind.h>
#include <s2tt.h>
#include <s2tt_ap.h>
#include <s2tt_pvt_defs.h>
#include <smc-rmi.h>
#include <smc.h>
#include <stdbool.h>
#include <stddef.h>

/*
 * Return a mask for the PA field within a S2TTE
 */
static unsigned long s2tte_lvl_mask(long level, bool lpa2)
{
	assert(level <= S2TT_PAGE_LEVEL);
	assert(level >= S2TT_MIN_STARTING_LEVEL_LPA2);

	unsigned long mask;
	unsigned long levels = (unsigned long)(S2TT_PAGE_LEVEL - level);
	unsigned long lsb = (levels * S2TTE_STRIDE) + GRANULE_SHIFT;

	mask = BIT_MASK_ULL((S2TTE_OA_BITS - 1U), lsb);

	if (lpa2) {
		mask |= (MASK(LPA2_S2TTE_51_50) | MASK(LPA2_OA_49_48));
	}

	return mask;
}

/*
 * Return an IPA mask @level
 */
unsigned long s2tte_ipa_lvl_mask(long level, bool lpa2)
{
	assert(level <= S2TT_PAGE_LEVEL);
	assert(level >= S2TT_MIN_STARTING_LEVEL_LPA2);

	unsigned long mask;
	unsigned long levels = (unsigned long)(S2TT_PAGE_LEVEL - level);
	unsigned long lsb = (levels * S2TTE_STRIDE) + GRANULE_SHIFT;
	unsigned long oa_bits = (lpa2 == true) ? S2TTE_OA_BITS_LPA2 :
						 S2TTE_OA_BITS;

	mask = BIT_MASK_ULL((oa_bits - 1U), lsb);

	return mask;
}

/*
 * Extracts the PA mapped by an S2TTE, aligned to a given level.
 */
static unsigned long s2tte_to_pa(unsigned long s2tte, long level, bool lpa2)
{
	unsigned long pa = s2tte & s2tte_lvl_mask(level, lpa2);

	if (lpa2) {
		pa &= ~MASK(LPA2_S2TTE_51_50);
		pa |= INPLACE(LPA2_OA_51_50, EXTRACT(LPA2_S2TTE_51_50, s2tte));
	}

	return pa;
}

/*
 * Invalidates S2 TLB entries from [ipa, ipa + size] region tagged with `vmid`.
 */
static void stage2_tlbi_ipa(const struct s2tt_context *s2_ctx,
			    unsigned long ipa,
			    unsigned long size)
{
	/*
	 * Notes:
	 *
	 * - This follows the description provided in the Arm ARM on
	 *   "Invalidation of TLB entries from stage 2 translations".
	 *
	 * - @TODO: Provide additional information to this primitive so that
	 *   we can utilize:
	 *   - The TTL level hint, see FEAT_TTL,
	 *   - Final level lookup only invalidation,
	 *   - Address range invalidation.
	 */

	assert(s2_ctx != NULL);

	/*
	 * Save the current content of vttb_el2.
	 */
	unsigned long old_vttbr_el2 = read_vttbr_el2();

	/*
	 * Make 'vmid' the `current vmid`. Note that the tlbi instructions
	 * bellow target the TLB entries that match the `current vmid`.
	 */
	write_vttbr_el2(INPLACE(VTTBR_EL2_VMID, s2_ctx->vmid));
	isb();

	/*
	 * Invalidate entries in S2 TLB caches that
	 * match both `ipa` & the `current vmid`.
	 */
	while (size != 0UL) {
		tlbiipas2e1is(ipa >> 12);
		size -= GRANULE_SIZE;
		ipa += GRANULE_SIZE;
	}
	dsb(ish);

	/*
	 * The architecture does not require TLB invalidation by IPA to affect
	 * combined Stage-1 + Stage-2 TLBs. Therefore we must invalidate all of
	 * Stage-1 after invalidating Stage-2.
	 *
	 * Bear in mind that as the effective value of HCR_EL2.{E2H, TGE} == {1, 1}
	 * the current VMID is not taken into account for the invalidation.
	 */
	tlbivmalle1is();
	dsb(ish);
	isb();

	/*
	 * Restore the old content of vttb_el2.
	 */
	write_vttbr_el2(old_vttbr_el2);
	isb();
}

/*
 * Returns true if @s2tte has HIPAS=@hipas.
 */
static inline bool s2tte_has_hipas(unsigned long s2tte, unsigned long hipas)
{
	bool invalid_desc = ((s2tte & S2TT_DESC_VALID_MASK) == S2TTE_INVALID);
	unsigned long invalid_desc_hipas = s2tte & S2TTE_INVALID_HIPAS_MASK;

	return (invalid_desc && (invalid_desc_hipas == hipas));
}

/*
 * Returns true if s2tte has 'output address' field, namely, if it is one of:
 * - valid TTE
 * - HIPAS = assigned
 * - HIPAS = assigned_dev
 */
static bool s2tte_has_pa(const struct s2tt_context *s2_ctx,
			 unsigned long s2tte, long level)
{
	(void)s2_ctx;
	(void)level;
	bool valid_desc = ((s2tte & S2TT_DESC_VALID_MASK) == S2TTE_VALID);

	return (valid_desc ||	/* block, page or table */
		s2tte_has_hipas(s2tte, S2TTE_INVALID_HIPAS_ASSIGNED) ||
		s2tte_has_hipas(s2tte, S2TTE_INVALID_HIPAS_ASSIGNED_DEV));
}

/*
 * Creates a TTE containing only the PA.
 * This function expects 'pa' to be aligned and bounded.
 */
static unsigned long pa_to_s2tte(unsigned long pa, bool lpa2)
{
	unsigned long tte = pa;

	if (lpa2) {
		tte &= ~MASK(LPA2_OA_51_50);
		tte |= INPLACE(LPA2_S2TTE_51_50, EXTRACT(LPA2_OA_51_50, pa));
	}

	return tte;
}

/*
 * Get the Access Permissions of a given S2TTE modifying them as follows:
 *
 * - If @dev == true and Permission Indirection is enabled:
 *      + Set the default Permission Indirection Index to S2TTE_DEV_DEF_BASE_PERM_IDX.
 *      + Preserve the Overlay Index.
 *
 * - If @dev == false and Permission Indirection is enabled:
 *      + Set the default Permission Indirection Index to S2TTE_DEF_BASE_PERM_IDX.
 *      + Preserve the Overlay Index.
 *
 * - If @dev == true and Permission Indirection is disabled:
 *      + Set eXecution permissions to S2TTE_PERM_XNU_XNP (disable all permissions).
 *      + Preserve R and W permissions.
 *
 * - If @dev == false and Permission Indirection is disabled:
 *      + Preserve all the access permissions.
 *
 * This function also sets the DIRTY BIT if indirect permission is used.
 */
static unsigned long s2tte_get_ap(const struct s2tt_context *s2_ctx,
				  unsigned long s2tte, bool dev)
{
	unsigned long s2tte_ap;

	assert(s2_ctx != NULL);

	if (!s2_ctx->indirect_s2ap) {
		s2tte_ap = s2tte & S2TTE_RW_AP_MASK;
		return dev ? (s2tte_ap | S2TTE_PERM_XNU_XNP) :
			     (s2tte_ap | (s2tte & MASK(S2TTE_PERM_XN)));
	}

	s2tte_ap = (s2tte & MASK(S2TTE_PO_INDEX)) | S2TTE_DIRTY_BIT;

	return s2tte_set_pi_index(s2_ctx, s2tte_ap,
			(dev ? S2TTE_DEV_DEF_BASE_PERM_IDX : S2TTE_DEF_BASE_PERM_IDX));
}

/*
 * Invalidate S2 TLB entries with "addr" IPA.
 * Call this function after:
 * 1.  A L3 page desc has been removed.
 */
void s2tt_invalidate_page(const struct s2tt_context *s2_ctx, unsigned long addr)
{
	stage2_tlbi_ipa(s2_ctx, addr, GRANULE_SIZE);
}

/*
 * Invalidate S2 TLB entries with "addr" IPA.
 * Call this function after:
 * 1.  A L2 block desc has been removed, or
 * 2a. A L2 table desc has been removed, where
 * 2b. All S2TTEs in L3 table that the L2 table desc was pointed to were invalid.
 */
void s2tt_invalidate_block(const struct s2tt_context *s2_ctx, unsigned long addr)
{
	stage2_tlbi_ipa(s2_ctx, addr, GRANULE_SIZE);
}

/*
 * Invalidate S2 TLB entries with "addr" IPA.
 * Call this function after:
 * 1a. A L2 table desc has been removed, where
 * 1b. Some S2TTEs in the table that the L2 table desc was pointed to were valid.
 */
void s2tt_invalidate_pages_in_block(const struct s2tt_context *s2_ctx,
				    unsigned long addr)
{
	stage2_tlbi_ipa(s2_ctx, addr, BLOCK_L2_SIZE);
}

/*
 * Return the index of the entry describing @addr in the translation table at
 * level @level. This only works for non-concatenated page tables, so should
 * not be called to get the index for the starting level.
 *
 * See the library pseudocode
 * aarch64/translation/vmsa_addrcalc/AArch64.TTEntryAddress on which this is
 * modeled.
 */
static unsigned long s2_addr_to_idx(unsigned long addr, long level)
{
	unsigned int levels, lsb;
	unsigned int s2tte_stride = (level < S2TT_MIN_STARTING_LEVEL) ?
					S2TTE_STRIDE_LM1 : S2TTE_STRIDE;

	levels = (unsigned int)(S2TT_PAGE_LEVEL - level);
	lsb = (levels * S2TTE_STRIDE) + GRANULE_SHIFT;

	addr >>= lsb;
	addr &= (1UL << s2tte_stride) - 1UL;
	return addr;
}

/*
 * Return the index of the entry describing @addr in the translation table
 * starting level. This may return an index >= S2TTES_PER_S2TT when the
 * combination of @start_level and @ipa_bits implies concatenated
 * stage 2 tables.
 *
 * See the library pseudocode
 * aarch64/translation/vmsa_addrcalc/AArch64.S2SLTTEntryAddress on which
 * this is modeled.
 */
static unsigned long s2_sl_addr_to_idx(unsigned long addr, int start_level,
				       unsigned long ipa_bits)
{
	unsigned int levels, lsb;

	levels = (unsigned int)(S2TT_PAGE_LEVEL - start_level);
	lsb = (levels * S2TTE_STRIDE) + GRANULE_SHIFT;

	addr &= ((1UL << ipa_bits) - 1UL);
	addr >>= lsb;
	return addr;
}

static bool entry_is_table(unsigned long entry)
{
	return ((entry & S2TT_DESC_TYPE_MASK) == S2TTE_L012_TABLE);
}

static unsigned long table_get_entry(const struct s2tt_context *s2_ctx,
				     struct granule *g_tbl,
				     unsigned long idx)
{
	unsigned long *table, entry;

	(void)s2_ctx;

	table = buffer_granule_map(g_tbl, SLOT_RTT);
	assert(table != NULL);

	entry = s2tte_read(&table[idx]);
	buffer_unmap(table);

	return entry;
}

#define table_entry_to_phys(tte, lpa2)			\
				s2tte_to_pa(tte, S2TT_PAGE_LEVEL, lpa2)

static struct granule *find_next_level_idx(const struct s2tt_context *s2_ctx,
					   struct granule *g_tbl,
					   unsigned long idx)
{
	assert(s2_ctx != NULL);

	const unsigned long entry = table_get_entry(s2_ctx, g_tbl, idx);

	if (!entry_is_table(entry)) {
		return NULL;
	}

	return addr_to_granule(table_entry_to_phys(entry, s2_ctx->enable_lpa2));
}

static struct granule *find_lock_next_level(const struct s2tt_context *s2_ctx,
					    struct granule *g_tbl,
					    unsigned long map_addr,
					    long level)
{
	const unsigned long idx = s2_addr_to_idx(map_addr, level);
	struct granule *g = find_next_level_idx(s2_ctx, g_tbl, idx);

	if (g != NULL) {
		granule_lock(g, GRANULE_STATE_RTT);
	}

	return g;
}

/*
 * Walk an RTT until level @level using @map_addr.
 * @g_root is the root (level 0/-1) table and must be locked before the call.
 * @start_level is the initial lookup level used for the stage 2 translation
 * tables which may depend on the configuration of the realm, factoring in the
 * IPA size of the realm and the desired starting level (within the limits
 * defined by the Armv8 VMSA including options for stage 2 table concatenation).
 * The function uses hand-over-hand locking to avoid race conditions and allow
 * concurrent access to RTT tree which is not part of the current walk; when a
 * next level table is reached it is locked before releasing previously locked
 * table.
 * The walk stops when either:
 * - The entry found is a leaf entry (not an RTT Table entry), or
 * - Level @level is reached (in this case, a RTT Table entry can be returned).
 *
 * On return:
 * - s2tt_walk::last_level is the last level that has been reached by the walk.
 * - s2tt_walk.g_llt points to the TABLE granule at level @s2tt_walk::level.
 *   The granule is locked.
 * - s2tt_walk::index is the entry index at s2tt_walk.g_llt for @map_addr.i
 *
 * NOTE: This function expects that the root table on the s2 context is
 *	 already locked.
 */
void s2tt_walk_lock_unlock(const struct s2tt_context *s2_ctx,
			   unsigned long map_addr,
			   long level,
			   struct s2tt_walk *wi)
{
	/* coverity[misra_c_2012_rule_11_9_violation:SUPPRESS] */
	struct granule *g_tbls[NR_RTT_LEVELS_LPA2] = { (struct granule *)NULL };
	struct granule *g_root;
	unsigned long sl_idx, ipa_bits;
	int i, start_level, last_level;

	assert(s2_ctx != NULL);

	start_level = s2_ctx->s2_starting_level;
	ipa_bits = s2_ctx->ipa_bits;

	assert(level >= start_level);
	assert(level <= S2TT_PAGE_LEVEL);
	assert(map_addr < (1UL << ipa_bits));
	assert(wi != NULL);

	if (s2_ctx->enable_lpa2) {
		assert(ipa_bits <= S2TTE_OA_BITS_LPA2);
	} else {
		assert(ipa_bits <= S2TTE_OA_BITS);
	}

	g_root = s2_ctx->g_rtt;

	/* Handle concatenated starting level (SL) tables */
	sl_idx = s2_sl_addr_to_idx(map_addr, start_level, ipa_bits);
	if (sl_idx >= S2TTES_PER_S2TT) {
		unsigned int tt_num = (unsigned int)(sl_idx >> S2TTE_STRIDE);
		struct granule *g_concat_root;

		assert(tt_num < s2_ctx->num_root_rtts);

		g_concat_root = (struct granule *)((uintptr_t)g_root +
					(tt_num * sizeof(struct granule)));

		granule_lock(g_concat_root, GRANULE_STATE_RTT);
		granule_unlock(g_root);
		g_root = g_concat_root;
	}

	/* 'start_level' can be '-1', so add 1 when used as an index */
	g_tbls[start_level + 1] = g_root;
	for (i = start_level; i < level; i++) {
		/*
		 * Lock next RTT level. Correct locking order is guaranteed
		 * because reference is obtained from a locked granule
		 * (previous level). Also, hand-over-hand locking/unlocking is
		 * used to avoid race conditions.
		 *
		 * Note that as 'start_level' can be -1, we add '1' to the
		 * index 'i' to compensate for the negative value when we
		 * use it to index then 'g_tbls' list.
		 */
		g_tbls[i + 1 + 1] = find_lock_next_level(s2_ctx, g_tbls[i + 1],
						     map_addr, i);
		if (g_tbls[i + 1 + 1] == NULL) {
			last_level = i;
			goto out;
		}
		granule_unlock(g_tbls[i + 1]);
	}

	last_level = (int)level;
out:
	wi->last_level = last_level;
	/* coverity[deref_overflow:SUPPRESS] */
	wi->g_llt = g_tbls[last_level + 1];
	wi->index = s2_addr_to_idx(map_addr, last_level);
}

/*
 * Creates an unassigned_empty s2tte with the given access permissions.
 */
unsigned long s2tte_create_unassigned_empty(const struct s2tt_context *s2_ctx,
					    unsigned long s2tte_ap)
{
	return s2tte_get_ap(s2_ctx, s2tte_ap, false) |
		(S2TTE_INVALID_HIPAS_UNASSIGNED | S2TTE_INVALID_RIPAS_EMPTY);
}

/*
 * Creates an unassigned_ram s2tte with the given access permissions.
 */
unsigned long s2tte_create_unassigned_ram(const struct s2tt_context *s2_ctx,
					  unsigned long s2tte_ap)
{
	return (S2TTE_INVALID_HIPAS_UNASSIGNED | S2TTE_INVALID_RIPAS_RAM) |
		s2tte_get_ap(s2_ctx, s2tte_ap, false);
}

/*
 * Creates an unassigned_destroyed s2tte with the given access permissions.
 */
unsigned long s2tte_create_unassigned_destroyed(const struct s2tt_context *s2_ctx,
						unsigned long s2tte_ap)
{
	return s2tte_get_ap(s2_ctx, s2tte_ap, false) |
		(S2TTE_INVALID_HIPAS_UNASSIGNED | S2TTE_INVALID_RIPAS_DESTROYED);
}

/*
 * Creates an unassigned_ns s2tte.
 */
unsigned long s2tte_create_unassigned_ns(const struct s2tt_context *s2_ctx,
					 unsigned long s2tte_ap)
{
	(void)s2_ctx;
	(void)s2tte_ap;

	return (S2TTE_NS | S2TTE_INVALID_HIPAS_UNASSIGNED);
}

/*
 * Creates s2tte with output address @pa, HIPAS=ASSIGNED and
 * RIPAS=@s2tte_ripas, at level @level.
 */
static unsigned long s2tte_create_assigned(const struct s2tt_context *s2_ctx,
					   unsigned long pa, long level,
					   unsigned long s2tte_ripas)
{
	unsigned long tte;

	assert(s2_ctx != NULL);
	assert(level >= S2TT_MIN_BLOCK_LEVEL);
	assert(level <= S2TT_PAGE_LEVEL);
	assert(s2tte_ripas <= S2TTE_INVALID_RIPAS_DESTROYED);
	assert(s2tte_is_addr_lvl_aligned(s2_ctx, pa, level));

	tte = pa_to_s2tte(pa, s2_ctx->enable_lpa2);

	if (s2tte_ripas == S2TTE_INVALID_RIPAS_RAM) {
		unsigned long s2tte_page, s2tte_block;

		if (s2_ctx->enable_lpa2) {
			s2tte_page = S2TTE_PAGE_LPA2;
			s2tte_block = S2TTE_BLOCK_LPA2;
		} else {
			s2tte_page = S2TTE_PAGE;
			s2tte_block = S2TTE_BLOCK;
		}

		if (level == S2TT_PAGE_LEVEL) {
			return (tte | s2tte_page);
		}
		return (tte | s2tte_block);
	}

	return (tte | S2TTE_INVALID_HIPAS_ASSIGNED | s2tte_ripas);
}

/*
 * Creates and invalid s2tte with output address @pa, HIPAS=ASSIGNED and
 * RIPAS=DESTROYED at level @level with the given access permissions.
 */
unsigned long s2tte_create_assigned_destroyed(const struct s2tt_context *s2_ctx,
					      unsigned long pa, long level,
					      unsigned long s2tte_ap)
{
	return s2tte_get_ap(s2_ctx, s2tte_ap, false) |
			s2tte_create_assigned(s2_ctx, pa, level,
					      S2TTE_INVALID_RIPAS_DESTROYED);
}

/*
 * Creates an invalid s2tte with output address @pa, HIPAS=ASSIGNED and
 * RIPAS=EMPTY at level @level with the given access permission.
 */
unsigned long s2tte_create_assigned_empty(const struct s2tt_context *s2_ctx,
					  unsigned long pa, long level,
					  unsigned long s2tte_ap)
{
	return s2tte_get_ap(s2_ctx, s2tte_ap, false) |
			s2tte_create_assigned(s2_ctx, pa, level,
					      S2TTE_INVALID_RIPAS_EMPTY);
}

/*
 * Creates an assigned_ram s2tte with output address @pa and
 * access permissions @ap
 */
unsigned long s2tte_create_assigned_ram(const struct s2tt_context *s2_ctx,
					unsigned long pa, long level,
					unsigned long s2tte_ap)
{
	return s2tte_create_assigned(s2_ctx, pa, level,
				     S2TTE_INVALID_RIPAS_RAM) |
				     s2tte_get_ap(s2_ctx, s2tte_ap, false);
}

/*
 * Creates an assigned s2tte with output address @pa and the same
 * RIPAS and access permissions as passed on @s2tte.
 */
unsigned long s2tte_create_assigned_unchanged(const struct s2tt_context *s2_ctx,
					      unsigned long s2tte,
					      unsigned long pa,
					      long level)
{
	unsigned long current_ripas = s2tte & S2TTE_INVALID_RIPAS_MASK;

	assert((s2tte & S2TT_DESC_VALID_MASK) == S2TTE_INVALID);

	return s2tte_create_assigned(s2_ctx, pa, level, current_ripas) |
				     s2tte_get_ap(s2_ctx, s2tte, false);
}

/*
 * Creates an invalid s2tte with output address @pa, HIPAS=ASSIGNED_DEV and
 * RIPAS=@s2tte_ripas, at level @level.
 * This function is only called for @s2tte_ripas values corresponding to
 * RIPAS_EMPTY and RIPAS_DESTROYED.
 */
static unsigned long s2tte_create_assigned_dev(const struct s2tt_context *s2_ctx,
						unsigned long pa, long level,
						unsigned long s2tte_ripas)
{
	(void)level;
	unsigned long tte;

	assert(s2_ctx != NULL);
	assert(level >= S2TT_MIN_DEV_BLOCK_LEVEL);
	assert(s2tte_is_addr_lvl_aligned(s2_ctx, pa, level));
	assert((s2tte_ripas == S2TTE_INVALID_RIPAS_EMPTY) ||
	       (s2tte_ripas == S2TTE_INVALID_RIPAS_DESTROYED));

	tte = pa_to_s2tte(pa, s2_ctx->enable_lpa2);

	return (tte | S2TTE_INVALID_HIPAS_ASSIGNED_DEV | s2tte_ripas);
}

/*
 * Creates an invalid s2tte with output address @pa, HIPAS=ASSIGNED_DEV,
 * RIPAS=EMPTY and the access permissions at @s2tte_ap, at level @level.
 *
 * Note that the execution permissions at @s2tte_ap will be overridden
 * to be disabled.
 */
unsigned long s2tte_create_assigned_dev_empty(const struct s2tt_context *s2_ctx,
						unsigned long pa, long level,
						unsigned long s2tte_ap)
{
	return s2tte_get_ap(s2_ctx, s2tte_ap, true) |
		s2tte_create_assigned_dev(s2_ctx, pa, level,
					 S2TTE_INVALID_RIPAS_EMPTY);
}

/*
 * Creates an invalid s2tte with output address @pa, HIPAS=ASSIGNED_DEV,
 * RIPAS=DESTROYED and the access permissions at @s2tte_ap  at level @level.
 *
 * Note that the execution permissions at @s2tte_ap will be overridden
 * to be disabled.
 */
unsigned long s2tte_create_assigned_dev_destroyed(const struct s2tt_context *s2_ctx,
						  unsigned long pa, long level,
						  unsigned long s2tte_ap)
{
	return s2tte_get_ap(s2_ctx, s2tte_ap, true) |
		s2tte_create_assigned_dev(s2_ctx, pa, level,
					 S2TTE_INVALID_RIPAS_DESTROYED);
}

/*
 * Creates an assigned_dev s2tte with output address @pa and the same
 * RIPAS and access permissions as passed on @s2tte.
 *
 * Note that the execution permissions at @s2tte_ap will be overridden
 * to be disabled.
 */
unsigned long s2tte_create_assigned_dev_unchanged(const struct s2tt_context *s2_ctx,
						  unsigned long s2tte,
						  unsigned long pa,
						  long level)
{
	unsigned long current_ripas = s2tte & S2TTE_INVALID_RIPAS_MASK;

	assert((s2tte & S2TT_DESC_VALID_MASK) == S2TTE_INVALID);

	return s2tte_create_assigned_dev(s2_ctx, pa, level, current_ripas) |
		s2tte_get_ap(s2_ctx, s2tte, true);
}

/*
 * Creates a valid assigned_dev_dev s2tte at @level with attributes passed in
 * @attr and the access permissions in @s2tte_ap
 *
 * Note that the execution permissions at @s2tte_ap will be overridden
 * to be disabled.
 */
static unsigned long create_assigned_dev_dev_attr(const struct s2tt_context *s2_ctx,
						  unsigned long s2tte,
						  unsigned long attr, long level,
						  unsigned long s2tte_ap)
{
	unsigned long pa, new_s2tte;
	bool lpa2 = s2_ctx->enable_lpa2;

	assert(level >= S2TT_MIN_DEV_BLOCK_LEVEL);
	assert(level <= S2TT_PAGE_LEVEL);

	pa = s2tte_to_pa(s2tte, level, lpa2);

	new_s2tte = attr | pa_to_s2tte(pa, lpa2) | s2tte_get_ap(s2_ctx, s2tte_ap, true);

	if (level == S2TT_PAGE_LEVEL) {
		return (new_s2tte | S2TTE_L3_PAGE);
	}

	return (new_s2tte | S2TTE_L012_BLOCK);
}

/*
 * Creates a valid assigned_dev_dev s2tte at @level with attributes passed in
 * @s2tte and the access permissions passed in @s2tte_ap.
 *
 * Note that the execution permissions at @s2tte_ap will be overridden
 * to be disabled.
 */
unsigned long s2tte_create_assigned_dev_dev(const struct s2tt_context *s2_ctx,
					    unsigned long s2tte, long level,
					    unsigned long s2tte_ap)
{
	unsigned long s2tte_mask = (S2TTE_DEV_ATTRS_MASK | S2TTE_MEMATTR_MASK);
	unsigned long attr;

	assert(s2_ctx != NULL);

	/* Add Shareability bits if FEAT_LPA2 is not enabled */
	if (!s2_ctx->enable_lpa2) {
		s2tte_mask |= S2TTE_SH_MASK;
	}

	/* Get attributes */
	attr = s2tte & s2tte_mask;

	return create_assigned_dev_dev_attr(s2_ctx, s2tte, attr, level, s2tte_ap);
}

/*
 * Creates a valid assigned_dev_dev s2tte at @level with attributes based on
 * device coherency passed in @type and the access permissions in @s2tte_ap.
 *
 * Note that the execution permissions at @s2tte_ap will be overridden
 * to be disabled.
 */
unsigned long s2tte_create_assigned_dev_dev_coh_type(const struct s2tt_context *s2_ctx,
						     unsigned long s2tte, long level,
						     enum dev_coh_type type,
						     unsigned long s2tte_ap)
{
	unsigned long attr;
	bool lpa2;

	assert(s2_ctx != NULL);
	assert(type < DEV_MEM_MAX);

	lpa2 = s2_ctx->enable_lpa2;

	if (type == DEV_MEM_COHERENT) {
		/* Coherent device */
		attr = S2TTE_DEV_COH_ATTRS;

		/* Add Shareability bits if FEAT_LPA2 is not enabled */
		if (!lpa2) {
			attr |= S2TTE_SH_IS;	/* Inner Shareable */
		}
	} else {
		/* Non-coherent device */
		attr = S2TTE_DEV_NCOH_ATTRS;

		/* Add Shareability bits if FEAT_LPA2 is not enabled */
		if (!lpa2) {
			attr |= S2TTE_SH_OS;	/* Outer Shareable */
		}
	}

	return create_assigned_dev_dev_attr(s2_ctx, s2tte, attr, level, s2tte_ap);
}

/*
 * Creates an assigned_ns s2tte at level @level.
 *
 * The following S2 TTE fields are provided through @s2tte argument:
 * - The physical address
 * - MemAttr
 * - Access permissions
 *   + RW when s2_ctx->indirect_s2ap == false.
 *   + Base Permission Indirection index when s2_ctx->indirect_s2ap == true.
 */
unsigned long s2tte_create_assigned_ns(const struct s2tt_context *s2_ctx,
				       unsigned long s2tte, long level,
				       unsigned long s2tte_ap)
{
	(void)s2tte_ap;
	assert(s2_ctx != NULL);

	/*
	 * We just mask out the DESC_TYPE below. We assume rest of the
	 * bits have been setup properly by the caller.
	 */
	unsigned long new_s2tte = s2tte & ~(S2TT_DESC_TYPE_MASK);

	assert(s2_ctx != NULL);
	assert(level >= S2TT_MIN_BLOCK_LEVEL);
	assert(level <= S2TT_PAGE_LEVEL);

	/* The Shareability bits need to be added if FEAT_LPA2 is not enabled */
	if (!s2_ctx->enable_lpa2) {
		new_s2tte |= S2TTE_SH_IS;
	}

	if (s2_ctx->indirect_s2ap) {
		assert(s2tte_get_pi_index(s2_ctx, s2tte) <=
					(unsigned long)S2AP_IND_BASE_PERM_IDX_RW);
		new_s2tte |= S2TTE_DIRTY_BIT;
		new_s2tte = s2tte_set_po_index(s2_ctx, new_s2tte,
					S2TTE_DEF_UNPROT_OVERLAY_IDX);
	} else {
		new_s2tte &= ~MASK(S2TTE_PERM_XN);
		new_s2tte |= S2TTE_PERM_XNU_XNP;
	}

	if (level == S2TT_PAGE_LEVEL) {
		return (new_s2tte | S2TTE_PAGE_NS);
	}
	return (new_s2tte | S2TTE_BLOCK_NS);
}

/*
 * Validate the portion of NS S2TTE that is provided by the host.
 */
bool host_ns_s2tte_is_valid(const struct s2tt_context *s2_ctx,
			    unsigned long s2tte, long level)
{
	bool lpa2;
	unsigned long mask;

	assert(s2_ctx != NULL);
	assert(level >= S2TT_MIN_BLOCK_LEVEL);

	lpa2 = s2_ctx->enable_lpa2;

	mask = s2tte_lvl_mask(level, lpa2) | S2TTE_NS_ATTR_MASK;

	if (s2_ctx->indirect_s2ap) {
		mask |= S2TTE_PI_INDEX_MASK;
	} else {
		mask |= S2TTE_RW_AP_MASK;
	}

	/*
	 * Test that all fields that are not controlled by the host are zero
	 * and that the output address is correctly aligned. Note that
	 * the host is permitted to map any physical address outside PAR.
	 * Note that this also checks for the case when FEAT_LPA2 is disabled
	 * for the Realm, then the PA in `s2tte` must be <= 48 bits wide.
	 */
	if ((s2tte & ~mask) != 0UL) {
		return false;
	}

	/*
	 * check if base perm set by host is valid
	 * ignore overlay perm, it is overwritten to 15
	 */
	if ((s2_ctx->indirect_s2ap) &&
			!s2ap_is_base_perm_index_valid(
					s2tte_get_pi_index(s2_ctx, s2tte))) {
		return false;
	}

	/*
	 * Only one value masked by S2TTE_MEMATTR_MASK is invalid/reserved.
	 */
	if ((s2tte & S2TTE_MEMATTR_MASK) == S2TTE_MEMATTR_FWB_RESERVED) {
		return false;
	}

	/*
	 * Note that all the values that are masked by S2TTE_RW_AP_MASK are valid.
	 */
	return true;
}

/*
 * Returns the portion of NS S2TTE that is set by the host.
 */
unsigned long host_ns_s2tte(const struct s2tt_context *s2_ctx,
			    unsigned long s2tte, long level)
{
	assert(s2_ctx != NULL);

	unsigned long mask = s2tte_lvl_mask(level, s2_ctx->enable_lpa2)
				| S2TTE_NS_ATTR_MASK;

	assert(level >= S2TT_MIN_BLOCK_LEVEL);

	if (s2_ctx->indirect_s2ap) {
		mask |= S2TTE_PI_INDEX_MASK;
	} else {
		mask |= S2TTE_RW_AP_MASK;
	}

	return (s2tte & mask);
}

/*
 * Creates a table s2tte at level @level with output address @pa.
 */
unsigned long s2tte_create_table(const struct s2tt_context *s2_ctx,
				 unsigned long pa, long level)
{
	(void)level;
	__unused long min_starting_level;

	assert(s2_ctx != NULL);

	min_starting_level = s2_ctx->enable_lpa2 ?
			S2TT_MIN_STARTING_LEVEL_LPA2 : S2TT_MIN_STARTING_LEVEL;

	assert(level < S2TT_PAGE_LEVEL);
	assert(level >= min_starting_level);
	assert(GRANULE_ALIGNED(pa));

	return (pa_to_s2tte(pa, s2_ctx->enable_lpa2) | S2TTE_TABLE);
}

/*
 * Returns true if s2tte has defined RIPAS value, namely if it is one of:
 * - unassigned_empty
 * - unassigned_ram
 * - unassigned_destroyed
 * - assigned_empty
 * - assigned_ram
 * - assigned_destroyed
 * - assigned_dev
 */
bool s2tte_has_ripas(const struct s2tt_context *s2_ctx,
		     unsigned long s2tte, long level)
{
	return (((s2tte & S2TTE_NS) == 0UL) && !s2tte_is_table(s2_ctx,
							       s2tte, level));
}

/*
 * Returns true if @s2tte has HIPAS=UNASSIGNED and RIPAS=@ripas.
 */
static inline bool s2tte_has_unassigned_ripas(unsigned long s2tte,
					      unsigned long ripas)
{
	return (((s2tte & S2TTE_INVALID_RIPAS_MASK) == ripas) &&
		  s2tte_has_hipas(s2tte, S2TTE_INVALID_HIPAS_UNASSIGNED));
}

/*
 * Returns true if @s2tte has HIPAS=ASSIGNED and RIPAS=@ripas.
 */
static inline bool s2tte_has_assigned_ripas(unsigned long s2tte,
					    unsigned long ripas)
{
	assert((s2tte & S2TT_DESC_VALID_MASK) == S2TTE_INVALID);
	assert(ripas != S2TTE_INVALID_RIPAS_RAM);

	return (((s2tte & S2TTE_INVALID_RIPAS_MASK) == ripas) &&
		  s2tte_has_hipas(s2tte, S2TTE_INVALID_HIPAS_ASSIGNED));
}

/*
 * Returns true if @s2tte has HIPAS=ASSIGNED_DEV and RIPAS=@ripas.
 */
static bool s2tte_has_assigned_dev_ripas(unsigned long s2tte, unsigned long ripas)
{
	assert((s2tte & S2TT_DESC_VALID_MASK) == S2TTE_INVALID);
	assert(ripas != S2TTE_INVALID_RIPAS_DEV);

	return ((s2tte & S2TTE_INVALID_RIPAS_MASK) == ripas) &&
		 s2tte_has_hipas(s2tte, S2TTE_INVALID_HIPAS_ASSIGNED_DEV);
}

/*
 * Returns true if @s2tte has HIPAS=ASSIGNED_DEV.
 */
bool s2tte_is_assigned_dev(const struct s2tt_context *s2_ctx,
			   unsigned long s2tte)
{
	(void)s2_ctx;

	return s2tte_has_hipas(s2tte, S2TTE_INVALID_HIPAS_ASSIGNED_DEV);
}

/*
 * Returns true if @s2tte has HIPAS=UNASSIGNED.
 */
bool s2tte_is_unassigned(const struct s2tt_context *s2_ctx, unsigned long s2tte)
{
	(void)s2_ctx;

	return s2tte_has_hipas(s2tte, S2TTE_INVALID_HIPAS_UNASSIGNED);
}

/*
 * Returns true if @s2tte is an unassigned_empty.
 */
bool s2tte_is_unassigned_empty(const struct s2tt_context *s2_ctx,
			       unsigned long s2tte)
{
	(void)s2_ctx;

	return (((s2tte & S2TTE_NS) == 0UL) &&
		  s2tte_has_unassigned_ripas(s2tte, S2TTE_INVALID_RIPAS_EMPTY));
}

/*
 * Returns true if @s2tte is an unassigned_ram.
 */
bool s2tte_is_unassigned_ram(const struct s2tt_context *s2_ctx,
			     unsigned long s2tte)
{
	(void)s2_ctx;

	return s2tte_has_unassigned_ripas(s2tte, S2TTE_INVALID_RIPAS_RAM);
}

/*
 * Returns true if @s2tte is unassigned_ns.
 */
bool s2tte_is_unassigned_ns(const struct s2tt_context *s2_ctx,
			    unsigned long s2tte)
{
	(void)s2_ctx;

	return (((s2tte & S2TTE_NS) != 0UL) &&
		  s2tte_has_hipas(s2tte, S2TTE_INVALID_HIPAS_UNASSIGNED));
}

/*
 * Returns true if @s2tte has RIPAS=DESTROYED.
 */
bool s2tte_is_unassigned_destroyed(const struct s2tt_context *s2_ctx,
				   unsigned long s2tte)
{
	(void)s2_ctx;

	return s2tte_has_unassigned_ripas(s2tte, S2TTE_INVALID_RIPAS_DESTROYED);
}

/*
 * Returns true if @s2tte is an assigned_destroyed.
 */
bool s2tte_is_assigned_destroyed(const struct s2tt_context *s2_ctx,
				 unsigned long s2tte, long level)
{
	(void)s2_ctx;
	(void)level;

	if ((s2tte & S2TT_DESC_VALID_MASK) != S2TTE_INVALID) {
		return false;
	}

	return s2tte_has_assigned_ripas(s2tte, S2TTE_INVALID_RIPAS_DESTROYED);
}

/*
 * Returns true if @s2tte is an assigned_empty.
 */
bool s2tte_is_assigned_empty(const struct s2tt_context *s2_ctx,
			     unsigned long s2tte, long level)
{
	(void)s2_ctx;
	(void)level;

	if ((s2tte & S2TT_DESC_VALID_MASK) != S2TTE_INVALID) {
		return false;
	}

	return s2tte_has_assigned_ripas(s2tte, S2TTE_INVALID_RIPAS_EMPTY);
}

static bool s2tte_check_assigned_ram_or_ns(const struct s2tt_context *s2_ctx,
					   unsigned long s2tte, long level,
					   unsigned long ns)
{
	(void)s2_ctx;
	unsigned long attr, desc_type;

	if ((s2tte & S2TTE_NS) != ns) {
		return false;
	}

	attr = s2tte & (S2TTE_DEV_ATTRS_MASK | S2TTE_MEMATTR_MASK);

	/* Return false for device memory */
	if ((attr == S2TTE_DEV_COH_ATTRS) || (attr == S2TTE_DEV_NCOH_ATTRS)) {
		return false;
	}

	desc_type = s2tte & S2TT_DESC_TYPE_MASK;

	/* Only pages at L3 and valid blocks at L2 and L1 allowed */
	if (level == S2TT_PAGE_LEVEL) {
		return (desc_type == S2TTE_L3_PAGE);
	}

	if ((level >= S2TT_MIN_BLOCK_LEVEL) && (desc_type == S2TTE_L012_BLOCK)) {
		return true;
	}

	return false;
}

/*
 * Returns true if @s2tte is an assigned_ram.
 */
bool s2tte_is_assigned_ram(const struct s2tt_context *s2_ctx,
			   unsigned long s2tte, long level)
{
	return s2tte_check_assigned_ram_or_ns(s2_ctx, s2tte, level, 0UL);
}

/*
 * Returns true if @s2tte is an assigned_ns s2tte.
 */
bool s2tte_is_assigned_ns(const struct s2tt_context *s2_ctx,
			  unsigned long s2tte, long level)
{
	return s2tte_check_assigned_ram_or_ns(s2_ctx, s2tte, level, S2TTE_NS);
}

/*
 * Returns true if @s2tte has HIPAS=ASSIGNED_DEV and RIPAS=RIPAS_DEV.
 */
bool s2tte_is_assigned_dev_dev(const struct s2tt_context *s2_ctx,
				unsigned long s2tte, long level)
{
	unsigned long attr;
	unsigned long desc_type = s2tte & S2TT_DESC_TYPE_MASK;
	bool lpa2;

	assert(s2_ctx != NULL);

	/* Only pages at L3 and valid blocks at L2 allowed */
	if (!(((level == S2TT_PAGE_LEVEL) && (desc_type == S2TTE_L3_PAGE)) ||
	      ((level == S2TT_MIN_DEV_BLOCK_LEVEL) && (desc_type == S2TTE_L012_BLOCK)))) {
		return false;
	}

	attr = s2tte & (S2TTE_DEV_ATTRS_MASK | S2TTE_MEMATTR_MASK);
	lpa2 = s2_ctx->enable_lpa2;

	/*
	 * Check that NS, AF and MemAttr[3:0] match with provided
	 * attributes. When LPA2 is not enabled, assert if shareability
	 * attrubutes are not set correctly.
	 */
	if (attr == S2TTE_DEV_COH_ATTRS) {
		if (!lpa2) {
			/* Coherent device, Inner Shareable */
			assert((s2tte & S2TTE_SH_MASK) == S2TTE_SH_IS);
		}
		return true;
	} else if (attr == S2TTE_DEV_NCOH_ATTRS) {
		if (!lpa2) {
			/* Non-coherent device, Outer Shareable */
			assert((s2tte & S2TTE_SH_MASK) == S2TTE_SH_OS);
		}
		return true;
	}
	return false;
}

/*
 * Returns true if @s2tte has HIPAS=ASSIGNED_DEV and RIPAS=RIPAS_EMPTY.
 */
bool s2tte_is_assigned_dev_empty(const struct s2tt_context *s2_ctx,
				 unsigned long s2tte, long level)
{
	(void)s2_ctx;
	(void)level;

	if ((s2tte & S2TT_DESC_VALID_MASK) != S2TTE_INVALID) {
		return false;
	}

	return s2tte_has_assigned_dev_ripas(s2tte, S2TTE_INVALID_RIPAS_EMPTY);
}

/*
 * Returns true if @s2tte is an dev_assigned_destroyed.
 */
bool s2tte_is_assigned_dev_destroyed(const struct s2tt_context *s2_ctx,
					unsigned long s2tte, long level)
{
	(void)s2_ctx;
	(void)level;

	if ((s2tte & S2TT_DESC_VALID_MASK) != S2TTE_INVALID) {
		return false;
	}

	return s2tte_has_assigned_dev_ripas(s2tte, S2TTE_INVALID_RIPAS_DESTROYED);
}

/*
 * Returns true if @s2tte is a table at level @level.
 */
bool s2tte_is_table(const struct s2tt_context *s2_ctx, unsigned long s2tte,
		    long level)
{
	(void)s2_ctx;

	return ((level < S2TT_PAGE_LEVEL) &&
		((s2tte & S2TT_DESC_TYPE_MASK) == S2TTE_L012_TABLE));
}

/*
 * Returns RIPAS of @s2tte.
 *
 * Caller should ensure that HIPAS=UNASSIGNED, ASSIGNED or ASSIGNED_DEV
 * The s2tte, if valid, should correspond to RIPAS_RAM or RIPAS_DEV.
 */
enum ripas s2tte_get_ripas(const struct s2tt_context *s2_ctx, unsigned long s2tte)
{
	(void)s2_ctx;
	__unused unsigned long desc_hipas;
	enum ripas desc_ripas;
	bool valid_desc = ((s2tte & S2TT_DESC_VALID_MASK) == S2TTE_VALID);

	/*
	 * If a valid S2TTE descriptor is passed, the RIPAS corresponds to
	 * RIPAS_RAM or RIPAS_DEV.
	 */
	if (valid_desc) {
		__unused unsigned long desc_type = s2tte & S2TT_DESC_TYPE_MASK;
		unsigned long attr = s2tte & (S2TTE_DEV_ATTRS_MASK |
						S2TTE_MEMATTR_MASK);

		assert((desc_type == S2TTE_L012_BLOCK) ||
			(desc_type == S2TTE_L3_PAGE));
		/*
		 * For device memory check that NS, AF and MemAttr[3:0]
		 * match with S2TTE_DEV_COH_ATTRS or S2TTE_DEV_NCOH_ATTRS
		 * attributes.
		 * Assume that shareability attributes and access permissions
		 * are set correctly.
		 */
		if ((attr == S2TTE_DEV_COH_ATTRS) ||
		    (attr == S2TTE_DEV_NCOH_ATTRS)) {
			return RIPAS_DEV;
		}
		return RIPAS_RAM;
	}

	desc_hipas = EXTRACT(S2TTE_INVALID_HIPAS, s2tte);

	/* Only HIPAS=UNASSIGNED, ASSIGNED or ASSIGNED_DEV are valid */
	assert((desc_hipas <= RMI_ASSIGNED_DEV) && (desc_hipas != RMI_TABLE));

	desc_ripas = (enum ripas)EXTRACT(S2TTE_INVALID_RIPAS, s2tte);
	assert(desc_ripas <= RIPAS_DESTROYED);

	return desc_ripas;
}

/*
 * Table containing label encodings for Overlay Access Permissions.
 * For compatibility with the S2AP library based on FEAT_S2PIE and FEAT_S2POE,
 * the encoded labels are equivalent to the ones on such features.
 */
static const struct s2tte_label_encoding ovr_encodings[S2AP_IND_PERM_COUNT] = {
	/*                     Label	       MRO R  W      EXEC	    */
	S2TTE_AP_LABEL_ENCODE(NO_ACCESS,	0, 0, 0, S2TTE_PERM_XNU_XNP),
	S2TTE_AP_LABEL_ENCODE(RESERVED_1,	0, 0, 0, S2TTE_PERM_XNU_XNP),
	S2TTE_AP_LABEL_ENCODE(MRO,		1, 0, 0, S2TTE_PERM_XNU_XNP),
	S2TTE_AP_LABEL_ENCODE(MRO_TL1,		1, 0, 0, S2TTE_PERM_XNU_XNP),
	S2TTE_AP_LABEL_ENCODE(WO,		0, 0, 1, S2TTE_PERM_XNU_XNP),
	S2TTE_AP_LABEL_ENCODE(RESERVED_5,	0, 0, 0, S2TTE_PERM_XNU_XNP),
	S2TTE_AP_LABEL_ENCODE(MRO_TL0,		1, 0, 0, S2TTE_PERM_XNU_XNP),
	S2TTE_AP_LABEL_ENCODE(MRO_TL01,		1, 0, 0, S2TTE_PERM_XNU_XNP),
	S2TTE_AP_LABEL_ENCODE(RO,		0, 1, 0, S2TTE_PERM_XNU_XNP),
	S2TTE_AP_LABEL_ENCODE(RO_uX,		0, 1, 0, S2TTE_PERM_XU_XNP),
	S2TTE_AP_LABEL_ENCODE(RO_pX,		0, 1, 0, S2TTE_PERM_XNU_XP),
	S2TTE_AP_LABEL_ENCODE(RO_upX,		0, 1, 0, S2TTE_PERM_XU_XP),
	S2TTE_AP_LABEL_ENCODE(RW,		0, 1, 1, S2TTE_PERM_XNU_XNP),
	S2TTE_AP_LABEL_ENCODE(RW_uX,		0, 1, 1, S2TTE_PERM_XU_XNP),
	S2TTE_AP_LABEL_ENCODE(RW_pX,		0, 1, 1, S2TTE_PERM_XNU_XP),
	S2TTE_AP_LABEL_ENCODE(RW_upX,		0, 1, 1, S2TTE_PERM_XU_XP)
};

/*
 * Table containig label encoding for Base Access Permissions as defined
 * by the RMM specification.
 * Note that the execution permissions in this table are just a bitmask.
 */
static const struct s2tte_label_encoding base_encodings[S2AP_IND_BASE_PERM_IDX_COUNT] = {
	/*                     Label	       MRO R  W      EXEC	    */
	S2TTE_AP_LABEL_ENCODE(BASE_NO_ACCESS,	0, 0, 0, MASK(S2TTE_PERM_XN)),
	S2TTE_AP_LABEL_ENCODE(BASE_RO,		0, 1, 0, MASK(S2TTE_PERM_XN)),
	S2TTE_AP_LABEL_ENCODE(BASE_WO,		0, 0, 1, MASK(S2TTE_PERM_XN)),
	S2TTE_AP_LABEL_ENCODE(BASE_RW,		0, 1, 1, MASK(S2TTE_PERM_XN)),
	S2TTE_AP_LABEL_ENCODE(BASE_RW_upX,	0, 1, 1, MASK(S2TTE_PERM_XN))
};

/*
 * Helper to provide the flattened Access Permissions given the base index,
 * the overlay index and the value for s2por_el2.
 */
static unsigned long s2tte_get_flattened_ap(unsigned long s2por_el2,
					    unsigned int base_idx,
					    unsigned int ovr_idx)
{
	unsigned int ovr_label_idx =
		(unsigned int)S2AP_IND_GET_PERM_VALUE(s2por_el2, ovr_idx);
	unsigned long base_ap = base_encodings[base_idx].value;
	unsigned long ovr_ap = ovr_encodings[ovr_label_idx].value;
	unsigned long flattened_ap = base_ap & ovr_ap;

	if (base_idx != (unsigned int)S2AP_IND_BASE_PERM_IDX_RW_upX) {
		/* Reset the base execution flags */
		flattened_ap &= ~MASK(S2TTE_PERM_XN);
		flattened_ap |= S2TTE_PERM_XNU_XNP;
	}

	return flattened_ap;
}

/*
 * Update a given S2TTE with the Access Permissions specified by the
 * value @index and the configuration @s2_ctx->overlay_perm.
 *
 * This API assumes that the parent RD is mapped.
 */
unsigned long s2tte_update_prot_ap(struct s2tt_context *s2_ctx,
				   unsigned long s2tte,
				   unsigned int base_index,
				   unsigned int overlay_index)
{
	unsigned long permissions;

	assert(s2_ctx != NULL);
	assert(s2ap_is_ovrl_perm_index_valid(overlay_index));
	assert(s2ap_is_base_perm_index_valid(base_index));

	if (s2_ctx->indirect_s2ap) {
		s2tte = s2tte_set_pi_index(s2_ctx, s2tte, base_index);
		return s2tte_set_po_index(s2_ctx, s2tte, overlay_index);
	}

	permissions = s2tt_ctx_get_overlay_perm_unlocked(s2_ctx);

	return (s2tte & ~S2TTE_PERM_MASK) |
		s2tte_get_flattened_ap(permissions, base_index, overlay_index);
}

/*
 * Populates @s2tt with unassigned_empty s2ttes with the given
 * access permissions extraced from given s2tte_ap.
 *
 * The granule is populated before it is made a table,
 * hence, don't use s2tte_write for access.
 */
void s2tt_init_unassigned_empty(const struct s2tt_context *s2_ctx,
				unsigned long *s2tt, unsigned long s2tte_ap)
{
	unsigned long s2tte = s2tte_create_unassigned_empty(s2_ctx, s2tte_ap);

	assert(s2tt != NULL);

	for (unsigned int i = 0U; i < S2TTES_PER_S2TT; i++) {
		s2tt[i] = s2tte;
	}

	dsb(ish);
}

/*
 * Populates @s2tt with unassigned_ram s2ttes with the access permissions @s2tte_ap.
 *
 * The granule is populated before it is made a table,
 * hence, don't use s2tte_write for access.
 */
void s2tt_init_unassigned_ram(const struct s2tt_context *s2_ctx,
			      unsigned long *s2tt, unsigned long s2tte_ap)
{
	unsigned long s2tte = s2tte_create_unassigned_ram(s2_ctx, s2tte_ap);

	assert(s2tt != NULL);

	for (unsigned int i = 0U; i < S2TTES_PER_S2TT; i++) {
		s2tt[i] = s2tte;
	}

	dsb(ish);
}

/*
 * Populates @s2tt with unassigned_ns s2ttes and the permissions
 * given by @s2tte_ap.
 *
 * The granule is populated before it is made a table,
 * hence, don't use s2tte_write for access.
 */
void s2tt_init_unassigned_ns(const struct s2tt_context *s2_ctx,
			     unsigned long *s2tt, unsigned long s2tte_ap)
{
	unsigned long s2tte = s2tte_create_unassigned_ns(s2_ctx, s2tte_ap);

	assert(s2tt != NULL);

	for (unsigned int i = 0U; i < S2TTES_PER_S2TT; i++) {
		s2tt[i] = s2tte;
	}

	dsb(ish);
}

/*
 * Populates @s2tt with s2ttes which have HIPAS=DESTROYED and
 * the given access permissions @s2tte_ap.
 *
 * The granule is populated before it is made a table,
 * hence, don't use s2tte_write for access.
 */
void s2tt_init_unassigned_destroyed(const struct s2tt_context *s2_ctx,
				    unsigned long *s2tt, unsigned long s2tte_ap)
{
	unsigned long s2tte =
		s2tte_create_unassigned_destroyed(s2_ctx, s2tte_ap);

	assert(s2tt != NULL);
	assert(s2_ctx != NULL);

	for (unsigned int i = 0U; i < S2TTES_PER_S2TT; i++) {
		s2tt[i] = s2tte;
	}

	dsb(ish);
}

static void init_assigned(const struct s2tt_context *s2_ctx,
			  unsigned long *s2tt, unsigned long pa, long level,
			  const long min_level, unsigned long s2tte_ap,
			  create_assigned_fn func)
{
	(void)min_level;

	assert(s2tt != NULL);
	assert(level >= min_level);
	assert(level <= S2TT_PAGE_LEVEL);
	assert(s2tte_is_addr_lvl_aligned(s2_ctx, pa, level));

	const unsigned long map_size = s2tte_map_size(level);

	for (unsigned int i = 0U; i < S2TTES_PER_S2TT; i++) {
		s2tt[i] = func(s2_ctx, pa, level, s2tte_ap);
		pa += map_size;
	}
	dsb(ish);
}

/*
 * Populates @s2tt with HIPAS=ASSIGNED, RIPAS=DESTROYED s2ttes that refer to a
 * contiguous memory block starting at @pa, mapped at level @level and with
 * the given access permissions by @s2tte_ap.
 *
 * The granule is populated before it is made a table,
 * hence, don't use s2tte_write for access.
 */
void s2tt_init_assigned_destroyed(const struct s2tt_context *s2_ctx,
				  unsigned long *s2tt, unsigned long pa,
				  long level, unsigned long s2tte_ap)
{
	init_assigned(s2_ctx, s2tt, pa, level, S2TT_MIN_BLOCK_LEVEL, s2tte_ap,
			s2tte_create_assigned_destroyed);
}

/*
 * Populates @s2tt with HIPAS=ASSIGNED, RIPAS=EMPTY s2ttes that refer to a
 * contiguous memory block starting at @pa, mapped at level @level and with
 * the given access permissions by @s2tte_ap.
 *
 * The granule is populated before it is made a table,
 * hence, don't use s2tte_write for access.
 */
void s2tt_init_assigned_empty(const struct s2tt_context *s2_ctx,
			      unsigned long *s2tt, unsigned long pa,
			      long level, unsigned long s2tte_ap)
{
	init_assigned(s2_ctx, s2tt, pa, level, S2TT_MIN_BLOCK_LEVEL, s2tte_ap,
			s2tte_create_assigned_empty);
}

/*
 * Populates @s2tt with assigned_ram s2ttes that refer to a
 * contiguous memory block starting at @pa, and mapped at level @level with
 * the access permissions @s2tte_ap.
 *
 * The granule is populated before it is made a table,
 * hence, don't use s2tte_write for access.
 */
void s2tt_init_assigned_ram(const struct s2tt_context *s2_ctx,
			    unsigned long *s2tt, unsigned long pa,
			    long level, unsigned long s2tte_ap)
{
	init_assigned(s2_ctx, s2tt, pa, level, S2TT_MIN_BLOCK_LEVEL, s2tte_ap,
			s2tte_create_assigned_ram);
}

/*
 * Populates @s2tt with NS attributes @attrs that refer to a
 * contiguous memory block starting at @pa, mapped at level @level.
 *
 * The granule is populated before it is made a table,
 * hence, don't use s2tte_write for access.
 *
 * Note that the @s2tte_ap parameter is included in order to make the API consistent
 * with the rest of s2tt_init_* and passed down to any API that would accept
 * it, although it is not used for the creation of an assigned NS s2tt.
 */
void s2tt_init_assigned_ns(const struct s2tt_context *s2_ctx,
			   unsigned long *s2tt, unsigned long attrs,
			   unsigned long pa, long level, unsigned long s2tte_ap)
{
	assert(s2tt != NULL);
	assert(level >= S2TT_MIN_BLOCK_LEVEL);
	assert(level <= S2TT_PAGE_LEVEL);
	assert(s2tte_is_addr_lvl_aligned(s2_ctx, pa, level));

	const unsigned long map_size = s2tte_map_size(level);
	unsigned long mask = S2TTE_NS_ATTR_MASK;

	mask |= (s2_ctx->indirect_s2ap) ?
		S2TTE_PI_INDEX_MASK : S2TTE_RW_AP_MASK;

	attrs &= mask;

	for (unsigned int i = 0U; i < S2TTES_PER_S2TT; i++) {
		s2tt[i] = s2tte_create_assigned_ns(s2_ctx,
				attrs | pa_to_s2tte(pa, s2_ctx->enable_lpa2),
				level, s2tte_ap);
		pa += map_size;
	}

	dsb(ish);
}

/*
 * Populates @s2tt with HIPAS=ASSIGNED_DEV, RIPAS=EMPTY s2ttes that refer to a
 * contiguous memory block starting at @pa, mapped at level @level and with the
 * given access permissions extracted from @s2tte_ap.
 *
 * The granule is populated before it is made a table,
 * hence, don't use s2tte_write for access.
 */
void s2tt_init_assigned_dev_empty(const struct s2tt_context *s2_ctx,
				  unsigned long *s2tt, unsigned long pa, long level,
				  unsigned long s2tte_ap)
{
	init_assigned(s2_ctx, s2tt, pa, level, S2TT_MIN_DEV_BLOCK_LEVEL, s2tte_ap,
			s2tte_create_assigned_dev_empty);
}

/*
 * Populates @s2tt with HIPAS=ASSIGNED_DEV, RIPAS=DESTROYED s2ttes that refer to a
 * contiguous memory block starting at @pa, mapped at level @level and with the
 * given access permissions extracted from @s2tte_ap.
 *
 * The granule is populated before it is made a table,
 * hence, don't use s2tte_write for access.
 */
void s2tt_init_assigned_dev_destroyed(const struct s2tt_context *s2_ctx,
					unsigned long *s2tt, unsigned long pa,
					long level, unsigned long s2tte_ap)
{
	init_assigned(s2_ctx, s2tt, pa, level, S2TT_MIN_DEV_BLOCK_LEVEL, s2tte_ap,
			s2tte_create_assigned_dev_destroyed);
}

/*
 * Populates @s2tt with assigned_dev_dev s2ttes that refer to a
 * contiguous memory block starting at @pa, and mapped at level @level with
 * the access permissions at @s2tte_ap.
 *
 * The granule is populated before it is made a table,
 * hence, don't use s2tte_write for access.
 */
void s2tt_init_assigned_dev_dev(const struct s2tt_context *s2_ctx,
				unsigned long *s2tt, unsigned long s2tte,
				unsigned long pa, long level,
				unsigned long s2tte_ap)
{
	unsigned long s2tte_mask = (S2TTE_DEV_ATTRS_MASK | S2TTE_MEMATTR_MASK);

	assert(s2tt != NULL);
	assert(level >= S2TT_MIN_DEV_BLOCK_LEVEL);
	assert(level <= S2TT_PAGE_LEVEL);
	assert(s2tte_is_addr_lvl_aligned(s2_ctx, pa, level));

	const unsigned long map_size = s2tte_map_size(level);

	/* Add Shareability bits if FEAT_LPA2 is not enabled */
	if (!s2_ctx->enable_lpa2) {
		s2tte_mask |= S2TTE_SH_MASK;
	}

	s2tte &= s2tte_mask;

	for (unsigned int i = 0U; i < S2TTES_PER_S2TT; i++) {
		s2tt[i] = s2tte_create_assigned_dev_dev(s2_ctx,
							s2tte | pa, level,
							s2tte_ap);
		pa += map_size;
	}

	dsb(ish);
}

/*
 * Returns true if s2tte is a live RTTE entry. i.e.,
 * HIPAS is ASSIGNED.
 *
 * NOTE: For now, only the RTTE with PA are live.
 * This could change with EXPORT/IMPORT support.
 */
bool s2tte_is_live(const struct s2tt_context *s2_ctx,
		   unsigned long s2tte, long level)
{
	return s2tte_has_pa(s2_ctx, s2tte, level);
}

/* Returns physical address of a S2TTE */
unsigned long s2tte_pa(const struct s2tt_context *s2_ctx, unsigned long s2tte,
		       long level)
{
	bool lpa2;
	__unused long min_starting_level;

	assert(s2_ctx != NULL);

	/* cppcheck-suppress misra-c2012-10.6 */
	min_starting_level = s2_ctx->enable_lpa2 ?
		S2TT_MIN_STARTING_LEVEL_LPA2 : S2TT_MIN_STARTING_LEVEL;
	assert(level >= min_starting_level);
	assert(level <= S2TT_PAGE_LEVEL);
	assert(s2tte_has_pa(s2_ctx, s2tte, level));

	lpa2 = s2_ctx->enable_lpa2;

	if (s2tte_is_table(s2_ctx, s2tte, level)) {
		return table_entry_to_phys(s2tte, lpa2);
	}

	return s2tte_to_pa(s2tte, level, lpa2);
}

bool s2tte_is_addr_lvl_aligned(const struct s2tt_context *s2_ctx,
			      unsigned long addr, long level)
{
	assert(s2_ctx != NULL);

	/* cppcheck-suppress misra-c2012-10.6 */
	__unused long min_starting_level = s2_ctx->enable_lpa2 ?
			S2TT_MIN_STARTING_LEVEL_LPA2 : S2TT_MIN_STARTING_LEVEL;
	unsigned long levels = (unsigned long)(S2TT_PAGE_LEVEL - level);
	unsigned long lsb = (levels * S2TTE_STRIDE) + GRANULE_SHIFT;
	unsigned long s2tte_oa_bits = s2_ctx->enable_lpa2 ?
			S2TTE_OA_BITS_LPA2 : S2TTE_OA_BITS;

	assert(level <= S2TT_PAGE_LEVEL);
	assert(level >= min_starting_level);

	return (addr == (addr & BIT_MASK_ULL((s2tte_oa_bits - 1U), lsb)));
}

typedef bool (*s2tte_type_checker)(const struct s2tt_context *s2_ctx,
				   unsigned long s2tte);

static bool table_is_uniform_unassigned_block(const struct s2tt_context *s2_ctx,
					      unsigned long *table,
					      s2tte_type_checker s2tte_is_x,
					      unsigned long *s2tte_ap)
{
	unsigned long s2tte = s2tte_read(&table[0U]);
	unsigned long ap = 0UL;

	if (!s2tte_is_x(s2_ctx, s2tte)) {
		return false;
	}

	if (s2tte_ap != NULL) {
		ap = s2tte_get_ap(s2_ctx, *s2tte_ap, false);

		/*
		 * Validate the AP of the first entry against the
		 * expected value.
		 */
		if (ap != s2tte_get_ap(s2_ctx, s2tte, false)) {
			return false;
		}
	}

	for (unsigned int i = 1U; i < S2TTES_PER_S2TT; i++) {
		s2tte = s2tte_read(&table[i]);

		if (!s2tte_is_x(s2_ctx, s2tte)) {
			return false;
		}

		if (s2tte_ap != NULL) {
			if (ap != s2tte_get_ap(s2_ctx, s2tte, false)) {
				return false;
			}
		}
	}

	return true;
}

/*
 * Returns true if all s2ttes in @table are unassigned_empty with
 * a given set of access permissions.
 */
bool s2tt_is_unassigned_empty_block(const struct s2tt_context *s2_ctx,
				    unsigned long *table, unsigned long s2tte_ap)
{
	assert(table != NULL);

	return table_is_uniform_unassigned_block(s2_ctx, table,
						 s2tte_is_unassigned_empty,
						 &s2tte_ap);
}

/*
 * Returns true if all s2ttes in @table are unassigned_ram and the
 * access permissions @s2tte_ap match the ones on the s2ttes.
 */
bool s2tt_is_unassigned_ram_block(const struct s2tt_context *s2_ctx,
				  unsigned long *table, unsigned long s2tte_ap)
{
	assert(table != NULL);

	return table_is_uniform_unassigned_block(s2_ctx, table,
						 s2tte_is_unassigned_ram,
						 &s2tte_ap);
}

/*
 * Returns true if all s2ttes in @table are unassigned_ns.
 * Note that @s2tte_ap is not used on this function, just used for consistency
 * with other similar APIs.
 */
bool s2tt_is_unassigned_ns_block(const struct s2tt_context *s2_ctx,
				 unsigned long *table, unsigned long s2tte_ap)
{
	(void)s2tte_ap;
	assert(table != NULL);

	return table_is_uniform_unassigned_block(s2_ctx, table,
						 s2tte_is_unassigned_ns, NULL);
}

/*
 * Returns true if all s2ttes in @table are unassigned_destroyed and
 * with the given access permissions.
 */
bool s2tt_is_unassigned_destroyed_block(const struct s2tt_context *s2_ctx,
					unsigned long *table, unsigned long s2tte_ap)
{
	assert(table != NULL);

	return table_is_uniform_unassigned_block(s2_ctx, table,
						 s2tte_is_unassigned_destroyed,
						 &s2tte_ap);
}

typedef bool (*s2tte_type_level_checker)(const struct s2tt_context *s2_ctx,
					 unsigned long s2tte, long level);

static bool table_maps_block(const struct s2tt_context *s2_ctx,
			     unsigned long *table,
			     long level,
			     s2tte_type_level_checker s2tte_is_x,
			     bool check_ns_attrs, unsigned long s2tte_ap,
			     bool dev)
{
	assert(table != NULL);
	assert(s2_ctx != NULL);

	unsigned long base_pa;
	unsigned long map_size = s2tte_map_size(level);
	unsigned long s2tte = s2tte_read(&table[0]);
	unsigned long s2tt_ns_attrs;
	unsigned int i;
	unsigned long expected_ap = 0UL;
	unsigned long ns_attr_mask = S2TTE_NS_ATTR_MASK;

	if (s2_ctx->enable_lpa2) {
		assert(level >= S2TT_MIN_STARTING_LEVEL_LPA2);
	} else {
		assert(level >= S2TT_MIN_STARTING_LEVEL);
	}

	assert(level <= S2TT_PAGE_LEVEL);

	if (!s2tte_is_x(s2_ctx, s2tte, level)) {
		return false;
	}

	expected_ap = s2tte_get_ap(s2_ctx, s2tte_ap, dev);

	/*
	 * Validate the AP on the first entry against the
	 * expected one.
	 */
	if (s2tte_get_ap(s2_ctx, s2tte, dev) != expected_ap) {
		return false;
	}

	base_pa = s2tte_pa(s2_ctx, s2tte, level);
	if (!s2tte_is_addr_lvl_aligned(s2_ctx, base_pa, level - 1L)) {
		return false;
	}

	ns_attr_mask |= (s2_ctx->indirect_s2ap) ?
		S2TTE_PI_INDEX_MASK : S2TTE_RW_AP_MASK;
	s2tt_ns_attrs = (s2tte & ns_attr_mask);

	for (i = 1U; i < S2TTES_PER_S2TT; i++) {
		unsigned long expected_pa = base_pa + (i * map_size);

		s2tte = s2tte_read(&table[i]);

		if (!s2tte_is_x(s2_ctx, s2tte, level)) {
			return false;
		}

		if (s2tte_pa(s2_ctx, s2tte, level) != expected_pa) {
			return false;
		}

		if (!check_ns_attrs) {
			if (expected_ap != s2tte_get_ap(s2_ctx, s2tte, dev)) {
				return false;
			}
		}

		if (check_ns_attrs) {
			unsigned long ns_attrs = (s2tte & ns_attr_mask);

			/*
			 * We match all the attributes in the S2TTE
			 * except for the AF bit.
			 */
			if (s2tt_ns_attrs != ns_attrs) {
				return false;
			}
		}
	}

	return true;
}

/*
 * Returns true if all s2ttes are assigned_empty,
 * refer to a contiguous block of granules aligned to @level - 1
 * and the access permissions are the same @s2tte_ap
 */
bool s2tt_maps_assigned_empty_block(const struct s2tt_context *s2_ctx,
				    unsigned long *table, long level,
				    unsigned long s2tte_ap)
{
	return table_maps_block(s2_ctx, table, level,
				s2tte_is_assigned_empty, false, s2tte_ap, false);
}

/*
 * Returns true if all s2ttes are assigned_ram and
 * refer to a contiguous block of granules aligned to @level - 1 and
 * with access permissions same as @s2tte_ap.
 */
bool s2tt_maps_assigned_ram_block(const struct s2tt_context *s2_ctx,
				  unsigned long *table, long level,
				  unsigned long s2tte_ap)
{
	return table_maps_block(s2_ctx, table, level,
				s2tte_is_assigned_ram, false, s2tte_ap, false);
}

/*
 * Returns true if
 *    - all s2ttes in @table are assigned_ns s2ttes and
 *    - they refer to a contiguous block of granules aligned to @level - 1 and
 *    - all the s2tte attributes in @table controlled by the host are identical.
 *
 * If @ap is not NULL, the access permissions/PIIIndex on the s2ttes
 * must match the ones @s2tte_ap.
 *
 * @pre: @table maps IPA outside PAR.
 */
bool s2tt_maps_assigned_ns_block(const struct s2tt_context *s2_ctx,
				 unsigned long *table, long level,
				 unsigned long s2tte_ap)
{
	return table_maps_block(s2_ctx, table, level,
				s2tte_is_assigned_ns, true, s2tte_ap, false);
}

/*
 * Returns true if all s2ttes are assigned_destroyed,
 * refer to a contiguous block of granules aligned to @level - 1
 * and the access permissions are the same @s2tte_ap
 */
bool s2tt_maps_assigned_destroyed_block(const struct s2tt_context *s2_ctx,
					unsigned long *table, long level,
					unsigned long s2tte_ap)
{
	return table_maps_block(s2_ctx, table, level,
				s2tte_is_assigned_destroyed, false, s2tte_ap, false);
}

/*
 * Returns true if all s2ttes are assigned_dev_empty, they refer to a contiguous
 * block of granules aligned to @level - 1 and the access permissions match
 * the ones @s2tte_ap.
 */
bool s2tt_maps_assigned_dev_empty_block(const struct s2tt_context *s2_ctx,
					unsigned long *table, long level,
					unsigned long s2tte_ap)
{
	return table_maps_block(s2_ctx, table, level,
				s2tte_is_assigned_dev_empty, false, s2tte_ap, true);
}

/*
 * Returns true if all s2ttes are assigned_dev_destroyed, they refer contiguous
 * block of granules aligned to @level - 1 and the access permissions match
 * the ones @s2tte_ap.
 */
bool s2tt_maps_assigned_dev_destroyed_block(const struct s2tt_context *s2_ctx,
					   unsigned long *table, long level,
					   unsigned long s2tte_ap)
{
	return table_maps_block(s2_ctx, table, level,
				s2tte_is_assigned_dev_destroyed, false, s2tte_ap, true);
}

/*
 * Returns true if all s2ttes are assigned_dev_dev, they refer to a contiguous
 * block of granules aligned to @level - 1 and the access permissions match the
 * ones @s2tte_ap.
 */
bool s2tt_maps_assigned_dev_dev_block(const struct s2tt_context *s2_ctx,
					unsigned long *table, long level,
					unsigned long s2tte_ap)
{
	return table_maps_block(s2_ctx, table, level,
				s2tte_is_assigned_dev_dev, false, s2tte_ap, true);
}

/*
 * Scan the RTT @s2tt (which is @wi.level), from the entry (@wi.index) and
 * skip the non-live entries (i.e., HIPAS=UNASSIGNED).
 * In other words, the scanning stops when a live RTTE is encountered or we
 * reach the end of this RTT.
 *
 * For now an RTTE can be considered non-live if it doesn't have a PA.
 * NOTE: This would change with EXPORT/IMPORT where we may have metadata stored
 * in the RTTE.
 *
 * @addr is not necessarily aligned to the wi.last_level (e.g., if we were called
 * with RMI_ERROR_RTT).
 *
 * Returns:
 * - If the entry @wi.index is live, returns @addr.
 * - If none of the entries in the @s2tt are "live", returns the address of the
 *   first entry in the next table.
 * - Otherwise, the address of the first live entry in @s2tt
 */
unsigned long s2tt_skip_non_live_entries(const struct s2tt_context *s2_ctx,
					 unsigned long addr,
					 unsigned long *table,
					 const struct s2tt_walk *wi)
{
	assert(table != NULL);
	assert(wi != NULL);
	assert(wi->index <= S2TTES_PER_S2TT);
	assert(wi->last_level <= S2TT_PAGE_LEVEL);
	assert(s2_ctx != NULL);

	unsigned long i, index = wi->index;
	long level = wi->last_level;
	unsigned long map_size;

	/* cppcheck-suppress misra-c2012-10.6 */
	__unused long min_starting_level = s2_ctx->enable_lpa2 ?
			S2TT_MIN_STARTING_LEVEL_LPA2 : S2TT_MIN_STARTING_LEVEL;

	assert(wi->last_level >= min_starting_level);

	/*
	 * If the entry for the map_addr is live,
	 * return @addr.
	 */
	if (s2tte_is_live(s2_ctx, s2tte_read(&table[index]), level)) {
		return addr;
	}

	/*
	 * Align the address DOWN to the map_size, as expected for the @level,
	 * so that we can compute the correct address by using the index.
	 */
	map_size = s2tte_map_size(level);
	addr &= ~(map_size - 1UL);

	/* Skip the "index" */
	for (i = index + 1UL; i < S2TTES_PER_S2TT; i++) {
		unsigned long s2tte = s2tte_read(&table[i]);

		if (s2tte_is_live(s2_ctx, s2tte, level)) {
			break;
		}
	}

	return (addr + ((i - index) * map_size));
}

/*
 * Initializes the s2tt library and any dependency, for the current PE.
 *
 * Note that this API musb be called for all the PEs during the warm boot path.
 */
void s2tt_init(void)
{
	s2ap_ind_perm_init();
}

/*
 * Reports whether the s2tt library supports Indirect Access Permissions.
 */
bool s2tt_indirect_ap_supported(void)
{
	return are_feat_s2pie_and_s2poe_present();
}
