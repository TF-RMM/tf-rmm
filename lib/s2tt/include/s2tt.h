/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef S2TT_H
#define S2TT_H

#include <arch_features.h>
#include <granule_types.h>
#include <memory.h>

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

	/*
	 * TODO: we will need other translation regime state, e.g. TCR, MAIR(?).
	 */
};

#define S2TT_MIN_IPA_BITS		32U
#define S2TT_MAX_IPA_BITS		48U

#define S2TT_MIN_STARTING_LEVEL		0
#define S2TT_PAGE_LEVEL			3
#define S2TT_MIN_BLOCK_LEVEL		2

/*
 * S2TTE_STRIDE: The number of bits resolved in a single level of translation
 * walk (except for the starting level which may resolve more or fewer bits).
 */
#define S2TTE_STRIDE		(GRANULE_SHIFT - 3U)
#define S2TTES_PER_S2TT		(1UL << S2TTE_STRIDE)

/*
 * At the moment, RMM doesn't support FEAT_LPA2 for stage 2 address
 * translation, so the maximum IPA size is 48 bits.
 */
static inline unsigned int s2tt_max_ipa_size(void)
{
	unsigned int ipa_size = arch_feat_get_pa_width();

	return (ipa_size > S2TT_MAX_IPA_BITS) ? S2TT_MAX_IPA_BITS : ipa_size;
}

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
#define s2tte_read(s2ttep)	__tte_read(s2ttep)

/***************************************************************************
 * Helpers for Stage 2 Translation Table Entries (S2TTE).
 **************************************************************************/
#define s2tte_map_size(level)						\
	(1ULL << (unsigned int)(((S2TT_PAGE_LEVEL - (level)) *		\
				(int)S2TTE_STRIDE) + (int)GRANULE_SHIFT))

bool s2tte_has_ripas(unsigned long s2tte, long level);

unsigned long s2tte_create_unassigned_empty(void);
unsigned long s2tte_create_unassigned_ram(void);
unsigned long s2tte_create_unassigned_ns(void);
unsigned long s2tte_create_unassigned_destroyed(void);

unsigned long s2tte_create_assigned_empty(unsigned long pa, long level);
unsigned long s2tte_create_assigned_ram(unsigned long pa, long level);
unsigned long s2tte_create_assigned_ns(unsigned long s2tte, long level);
unsigned long s2tte_create_assigned_destroyed(unsigned long pa, long level);
unsigned long s2tte_create_assigned_unchanged(unsigned long s2tte,
					      unsigned long pa,
					      long level);
unsigned long s2tte_create_table(unsigned long pa, long level);

bool host_ns_s2tte_is_valid(unsigned long s2tte, long level);
unsigned long host_ns_s2tte(unsigned long s2tte, long level);

bool s2tte_is_unassigned(unsigned long s2tte);
bool s2tte_is_unassigned_empty(unsigned long s2tte);
bool s2tte_is_unassigned_ram(unsigned long s2tte);
bool s2tte_is_unassigned_ns(unsigned long s2tte);
bool s2tte_is_unassigned_destroyed(unsigned long s2tte);
bool s2tte_is_table(unsigned long s2tte, long level);

bool s2tte_is_assigned_empty(unsigned long s2tte, long level);
bool s2tte_is_assigned_ram(unsigned long s2tte, long level);
bool s2tte_is_assigned_ns(unsigned long s2tte, long level);
bool s2tte_is_assigned_destroyed(unsigned long s2tte, long level);

unsigned long s2tte_pa(unsigned long s2tte, long level);
bool s2tte_is_addr_lvl_aligned(unsigned long addr, long level);

enum ripas s2tte_get_ripas(unsigned long s2tte);

/***************************************************************************
 * Helpers for Stage 2 Translation Tables  (S2TT).
 **************************************************************************/

void s2tt_init_unassigned_empty(unsigned long *s2tt);
void s2tt_init_unassigned_ram(unsigned long *s2tt);
void s2tt_init_unassigned_ns(unsigned long *s2tt);
void s2tt_init_unassigned_destroyed(unsigned long *s2tt);

void s2tt_init_assigned_empty(unsigned long *s2tt, unsigned long pa, long level);
void s2tt_init_assigned_ram(unsigned long *s2tt, unsigned long pa, long level);
void s2tt_init_assigned_ns(unsigned long *s2tt, unsigned long attrs,
			   unsigned long pa, long level);
void s2tt_init_assigned_destroyed(unsigned long *s2tt, unsigned long pa, long level);

void s2tt_invalidate_page(const struct s2tt_context *s2_ctx, unsigned long addr);
void s2tt_invalidate_block(const struct s2tt_context *s2_ctx, unsigned long addr);
void s2tt_invalidate_pages_in_block(const struct s2tt_context *s2_ctx,
				    unsigned long addr);

bool s2tt_is_unassigned_empty_block(unsigned long *table);
bool s2tt_is_unassigned_ram_block(unsigned long *table);
bool s2tt_is_unassigned_ns_block(unsigned long *table);
bool s2tt_is_unassigned_destroyed_block(unsigned long *table);

bool s2tt_maps_assigned_empty_block(unsigned long *table, long level);
bool s2tt_maps_assigned_ram_block(unsigned long *table, long level);
bool s2tt_maps_assigned_ns_block(unsigned long *table, long level);
bool s2tt_maps_assigned_destroyed_block(unsigned long *table, long level);

struct s2tt_walk {
	struct granule *g_llt;
	unsigned long index;
	long last_level;
};

void s2tt_walk_lock_unlock(struct granule *g_root,
			  int start_level,
			  unsigned long ipa_bits,
			  unsigned long map_addr,
			  long level,
			  struct s2tt_walk *wi);

unsigned long s2tt_skip_non_live_entries(unsigned long addr,
					 unsigned long *table,
					 const struct s2tt_walk *wi);

#endif /* S2TT_H */
