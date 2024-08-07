/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef S2TT_TESTS_BASE_G2
#define S2TT_TESTS_BASE_G2

/* s2tte_is_addr_lvl_aligned() */
void s2tte_is_addr_lvl_aligned_tc1(void);
void s2tte_is_addr_lvl_aligned_tc2(void);
void s2tte_is_addr_lvl_aligned_tc3(void);
void s2tte_is_addr_lvl_aligned_tc4(void);
void s2tte_is_addr_lvl_aligned_tc5(void);

/* s2tte_map_size() */
void s2tte_map_size_tc1(void);

/* s2tt_invalidate_page() */
void s2tt_invalidate_page_tc1(void);
void s2tt_invalidate_page_tc2(void);

/* s2tt_invalidate_block() */
void s2tt_invalidate_block_tc1(void);
void s2tt_invalidate_block_tc2(void);

/* s2tt_invalidate_pages_in_block() */
void s2tt_invalidate_pages_in_block_tc1(void);
void s2tt_invalidate_pages_in_block_tc2(void);

/* s2tt_is_unassigned_empty() */
void s2tt_is_unassigned_empty_block_tc1(void);
void s2tt_is_unassigned_empty_block_tc2(void);
void s2tt_is_unassigned_empty_block_tc3(void);

/* s2tt_is_unassigned_ram() */
void s2tt_is_unassigned_ram_block_tc1(void);
void s2tt_is_unassigned_ram_block_tc2(void);
void s2tt_is_unassigned_ram_block_tc3(void);

/* s2tt_is_unassigned_ns_block() */
void s2tt_is_unassigned_ns_block_tc1(void);
void s2tt_is_unassigned_ns_block_tc2(void);
void s2tt_is_unassigned_ns_block_tc3(void);

/* s2tt_is_unassigned_destroyed_block() */
void s2tt_is_unassigned_destroyed_block_tc1(void);
void s2tt_is_unassigned_destroyed_block_tc2(void);
void s2tt_is_unassigned_destroyed_block_tc3(void);

/* s2tt_maps_assigned_empty_block() */
void s2tt_maps_assigned_empty_block_tc1(void);
void s2tt_maps_assigned_empty_block_tc2(void);
void s2tt_maps_assigned_empty_block_tc3(void);
void s2tt_maps_assigned_empty_block_tc4(void);
void s2tt_maps_assigned_empty_block_tc5(void);
void s2tt_maps_assigned_empty_block_tc6(void);
void s2tt_maps_assigned_empty_block_tc7(void);

/* s2tt_maps_assigned_ram_block() */
void s2tt_maps_assigned_ram_block_tc1(void);
void s2tt_maps_assigned_ram_block_tc2(void);
void s2tt_maps_assigned_ram_block_tc3(void);
void s2tt_maps_assigned_ram_block_tc4(void);
void s2tt_maps_assigned_ram_block_tc5(void);
void s2tt_maps_assigned_ram_block_tc6(void);
void s2tt_maps_assigned_ram_block_tc7(void);

/* s2tt_maps_assigned_ns() */
void s2tt_maps_assigned_ns_block_tc1(void);
void s2tt_maps_assigned_ns_block_tc2(void);
void s2tt_maps_assigned_ns_block_tc3(void);
void s2tt_maps_assigned_ns_block_tc4(void);
void s2tt_maps_assigned_ns_block_tc5(void);
void s2tt_maps_assigned_ns_block_tc6(void);
void s2tt_maps_assigned_ns_block_tc7(void);
void s2tt_maps_assigned_ns_block_tc8(void);

/* s2tt_maps_assigned_destroyed() */
void s2tt_maps_assigned_destroyed_block_tc1(void);
void s2tt_maps_assigned_destroyed_block_tc2(void);
void s2tt_maps_assigned_destroyed_block_tc3(void);
void s2tt_maps_assigned_destroyed_block_tc4(void);
void s2tt_maps_assigned_destroyed_block_tc5(void);
void s2tt_maps_assigned_destroyed_block_tc6(void);
void s2tt_maps_assigned_destroyed_block_tc7(void);

/* s2tt_skip_non_live_entries() */
void s2tt_skip_non_live_entries_tc1(void);
void s2tt_skip_non_live_entries_tc2(void);
void s2tt_skip_non_live_entries_tc3(void);
void s2tt_skip_non_live_entries_tc4(void);
void s2tt_skip_non_live_entries_tc5(void);
void s2tt_skip_non_live_entries_tc6(void);
void s2tt_skip_non_live_entries_tc7(void);

/* s2tt_walk_lock_unlock() */
void s2tt_walk_lock_unlock_tc1(void);
void s2tt_walk_lock_unlock_tc2(void);
void s2tt_walk_lock_unlock_tc3(void);
void s2tt_walk_lock_unlock_tc4(void);
void s2tt_walk_lock_unlock_tc5(void);
void s2tt_walk_lock_unlock_tc6(void);
void s2tt_walk_lock_unlock_tc7(void);
void s2tt_walk_lock_unlock_tc8(void);
void s2tt_walk_lock_unlock_tc9(void);
void s2tt_walk_lock_unlock_tc10(void);
void s2tt_walk_lock_unlock_tc11(void);
void s2tt_walk_lock_unlock_tc12(void);

#endif /* S2TT_TESTS_BASE_G2 */
