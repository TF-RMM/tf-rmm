/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef S2TT_H
#define S2TT_H

#include <arch_features.h>
#include <granule_types.h>
#include <memory.h>
#include <stdbool.h>

/*
 * Stage 2 configuration of the Realm
 */
struct s2tt_context {
	/* Number of IPA bits */
	unsigned int ipa_bits;

	/* Starting level of the stage 2 translation */
	int s2_starting_level;

	/* Number of concatenated starting level rtts */
	unsigned int num_root_rtts;

	/* First level RTT, pointed to by Realm TTBR */
	struct granule *g_rtt;

	/* Virtual Machine Identifier */
	unsigned int vmid;

	/* If FEAT_LPA2 is enabled */
	bool enable_lpa2;

	/*
	 * TODO: we will need other translation regime state, e.g. TCR, MAIR(?).
	 */
};

#define S2TT_MIN_IPA_BITS		U(32)
#define S2TT_MAX_IPA_BITS		U(48)
#define S2TT_MAX_PA_BITS		U(48)

#define S2TT_MAX_IPA_BITS_LPA2		U(52)
#define S2TT_MAX_PA_BITS_LPA2		U(52)
#define S2TT_MAX_IPA_SIZE_LPA2		(UL(1) << S2TT_MAX_IPA_BITS_LPA2)

#define S2TT_MIN_STARTING_LEVEL		(0)
#define S2TT_MIN_STARTING_LEVEL_LPA2	(-1)
#define S2TT_PAGE_LEVEL			(3)
#define S2TT_MIN_BLOCK_LEVEL		(1)

/*
 * S2TTE_STRIDE: The number of bits resolved in a single level of translation
 * walk (except for the starting level which may resolve more or fewer bits).
 */
#define S2TTE_STRIDE		(U(GRANULE_SHIFT) - 3U)
#define S2TTES_PER_S2TT		(1UL << S2TTE_STRIDE)

/*
 * S2TTE_STRIDE_LM1: The number of bits resolved at Level -1 when FEAT_LPA2
 * is enabled. This value is equal to
 * MAX_IPA_BITS_LPA2 - ((4 * S2TTE_STRIDE) + GRANULE_SHIFT)
 * as Level -1 only has 4 bits for the index (bits [51:48]).
 */
#define S2TTE_STRIDE_LM1	(4U)
#define S2TTES_PER_S2TT_LM1	(1UL << S2TTE_STRIDE_LM1)

/*
 * The MMU is a separate observer, and requires that translation table updates
 * are made with single-copy-atomic stores, necessitating inline assembly. For
 * consistency we use accessors for both reads and writes of translation table
 * entries.
 */
static inline void __tte_write(uint64_t *ttep, uint64_t tte)
{
	SCA_WRITE64(ttep, tte);
	dsb(ish);
}
#define s2tte_write(s2ttep, s2tte)	__tte_write(s2ttep, s2tte)

static inline uint64_t __tte_read(uint64_t *ttep)
{
	return SCA_READ64(ttep);
}
#define s2tte_read(s2ttep)		__tte_read(s2ttep)

/***************************************************************************
 * Helpers for Stage 2 Translation Table Entries (S2TTE).
 **************************************************************************/
#define s2tte_map_size(level)						\
	(1ULL << (unsigned int)(((S2TT_PAGE_LEVEL - (level)) *		\
				(int)S2TTE_STRIDE) + (int)GRANULE_SHIFT))

bool s2tte_has_ripas(const struct s2tt_context *s2_ctx,
		     unsigned long s2tte, long level);

unsigned long s2tte_create_unassigned_empty(const struct s2tt_context *s2_ctx);
unsigned long s2tte_create_unassigned_ram(const struct s2tt_context *s2_ctx);
unsigned long s2tte_create_unassigned_ns(const struct s2tt_context *s2_ctx);
unsigned long s2tte_create_unassigned_destroyed(const struct s2tt_context *s2_ctx);

unsigned long s2tte_create_assigned_empty(const struct s2tt_context *s2_ctx,
					  unsigned long pa, long level);
unsigned long s2tte_create_assigned_ram(const struct s2tt_context *s2_ctx,
					unsigned long pa, long level);
unsigned long s2tte_create_assigned_ns(const struct s2tt_context *s2_ctx,
				       unsigned long s2tte, long level);
unsigned long s2tte_create_assigned_destroyed(const struct s2tt_context *s2_ctx,
					      unsigned long pa, long level);
unsigned long s2tte_create_assigned_unchanged(const struct s2tt_context *s2_ctx,
					      unsigned long s2tte,
					      unsigned long pa,
					      long level);
unsigned long s2tte_create_table(const struct s2tt_context *s2_ctx,
				 unsigned long pa, long level);

bool host_ns_s2tte_is_valid(const struct s2tt_context *s2_ctx,
			    unsigned long s2tte, long level);
unsigned long host_ns_s2tte(const struct s2tt_context *s2_ctx,
			    unsigned long s2tte, long level);

bool s2tte_is_unassigned(const struct s2tt_context *s2_ctx,
			 unsigned long s2tte);
bool s2tte_is_unassigned_empty(const struct s2tt_context *s2_ctx,
			       unsigned long s2tte);
bool s2tte_is_unassigned_ram(const struct s2tt_context *s2_ctx,
			     unsigned long s2tte);
bool s2tte_is_unassigned_ns(const struct s2tt_context *s2_ctx,
			    unsigned long s2tte);
bool s2tte_is_unassigned_destroyed(const struct s2tt_context *s2_ctx,
				   unsigned long s2tte);

bool s2tte_is_assigned_empty(const struct s2tt_context *s2_ctx,
			     unsigned long s2tte, long level);
bool s2tte_is_assigned_ram(const struct s2tt_context *s2_ctx,
			   unsigned long s2tte, long level);
bool s2tte_is_assigned_ns(const struct s2tt_context *s2_ctx,
			  unsigned long s2tte, long level);
bool s2tte_is_table(const struct s2tt_context *s2_ctx,
		    unsigned long s2tte, long level);
bool s2tte_is_assigned_destroyed(const struct s2tt_context *s2_ctx,
				 unsigned long s2tte, long level);

unsigned long s2tte_pa(const struct s2tt_context *s2_ctx,
		       unsigned long s2tte, long level);
bool s2tte_is_addr_lvl_aligned(const struct s2tt_context *s2_ctx,
			       unsigned long addr, long level);

enum ripas s2tte_get_ripas(const struct s2tt_context *s2_ctx,
			   unsigned long s2tte);

/***************************************************************************
 * Helpers for Stage 2 Translation Tables  (S2TT).
 **************************************************************************/

void s2tt_init_unassigned_empty(const struct s2tt_context *s2_ctx,
				unsigned long *s2tt);
void s2tt_init_unassigned_ram(const struct s2tt_context *s2_ctx,
			      unsigned long *s2tt);
void s2tt_init_unassigned_ns(const struct s2tt_context *s2_ctx,
			     unsigned long *s2tt);
void s2tt_init_unassigned_destroyed(const struct s2tt_context *s2_ctx,
				    unsigned long *s2tt);

void s2tt_init_assigned_empty(const struct s2tt_context *s2_ctx,
			      unsigned long *s2tt, unsigned long pa,
			      long level);
void s2tt_init_assigned_ram(const struct s2tt_context *s2_ctx,
			    unsigned long *s2tt, unsigned long pa, long level);
void s2tt_init_assigned_ns(const struct s2tt_context *s2_ctx,
			   unsigned long *s2tt, unsigned long attrs,
			   unsigned long pa, long level);
void s2tt_init_assigned_destroyed(const struct s2tt_context *s2_ctx,
				  unsigned long *s2tt, unsigned long pa,
				  long level);

void s2tt_invalidate_page(const struct s2tt_context *s2_ctx, unsigned long addr);
void s2tt_invalidate_block(const struct s2tt_context *s2_ctx, unsigned long addr);
void s2tt_invalidate_pages_in_block(const struct s2tt_context *s2_ctx,
				    unsigned long addr);

bool s2tt_is_unassigned_empty_block(const struct s2tt_context *s2_ctx,
				    unsigned long *table);
bool s2tt_is_unassigned_ram_block(const struct s2tt_context *s2_ctx,
				  unsigned long *table);
bool s2tt_is_unassigned_ns_block(const struct s2tt_context *s2_ctx,
				 unsigned long *table);
bool s2tt_is_unassigned_destroyed_block(const struct s2tt_context *s2_ctx,
					unsigned long *table);

bool s2tt_maps_assigned_empty_block(const struct s2tt_context *s2_ctx,
				    unsigned long *table, long level);
bool s2tt_maps_assigned_ram_block(const struct s2tt_context *s2_ctx,
				  unsigned long *table, long level);
bool s2tt_maps_assigned_ns_block(const struct s2tt_context *s2_ctx,
				 unsigned long *table, long level);
bool s2tt_maps_assigned_destroyed_block(const struct s2tt_context *s2_ctx,
					unsigned long *table, long level);

struct s2tt_walk {
	struct granule *g_llt;
	unsigned long index;
	long last_level;
};

void s2tt_walk_lock_unlock(const struct s2tt_context *s2_ctx,
			   unsigned long map_addr,
			   long level,
			   struct s2tt_walk *wi);

unsigned long s2tt_skip_non_live_entries(const struct s2tt_context *s2_ctx,
					 unsigned long addr,
					 unsigned long *table,
					 const struct s2tt_walk *wi);

#endif /* S2TT_H */
