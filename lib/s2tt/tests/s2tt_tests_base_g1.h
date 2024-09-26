/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef S2TT_TESTS_BASE_G1
#define S2TT_TESTS_BASE_G1

/* s2tte_create_unassigned_empty() */
void s2tte_create_unassigned_empty_tc1(void);

/* s2tte_create_unassigned_ram() */
void s2tte_create_unassigned_ram_tc1(void);

/* s2tte_create_unassigned_destroyed() */
void s2tte_create_unassigned_destroyed_tc1(void);

/* s2tte_create_unassigned_ns() */
void s2tte_create_unassigned_ns_tc1(void);

/* s2tte_create_assigned_destroyed() */
void s2tte_create_assigned_destroyed_tc1(void);
void s2tte_create_assigned_destroyed_tc2(void);
void s2tte_create_assigned_destroyed_tc3(void);
void s2tte_create_assigned_destroyed_tc4(void);
void s2tte_create_assigned_destroyed_tc5(void);

/* s2tte_create_assigned_empty() */
void s2tte_create_assigned_empty_tc1(void);
void s2tte_create_assigned_empty_tc2(void);
void s2tte_create_assigned_empty_tc3(void);
void s2tte_create_assigned_empty_tc4(void);
void s2tte_create_assigned_empty_tc5(void);

/* s2tte_create_assigned_ram() */
void s2tte_create_assigned_ram_tc1(void);
void s2tte_create_assigned_ram_tc2(void);
void s2tte_create_assigned_ram_tc3(void);
void s2tte_create_assigned_ram_tc4(void);
void s2tte_create_assigned_ram_tc5(void);

/* s2tte_create_assigned_ns)_ */
void s2tte_create_assigned_ns_tc1(void);
void s2tte_create_assigned_ns_tc2(void);
void s2tte_create_assigned_ns_tc3(void);

/* s2tte_create_assigned_unchanged() */
void s2tte_create_assigned_unchanged_tc1(void);
void s2tte_create_assigned_unchanged_tc2(void);
void s2tte_create_assigned_unchanged_tc3(void);
void s2tte_create_assigned_unchanged_tc4(void);
void s2tte_create_assigned_unchanged_tc5(void);
void s2tte_create_assigned_unchanged_tc6(void);

/* s2tte_create_table() */
void s2tte_create_table_tc1(void);
void s2tte_create_table_tc2(void);
void s2tte_create_table_tc3(void);
void s2tte_create_table_tc4(void);
void s2tte_create_table_tc5(void);

/* host_ns_s2tte() */
void host_ns_s2tte_tc1(void);
void host_ns_s2tte_tc2(void);
void host_ns_s2tte_tc3(void);
void host_ns_s2tte_tc4(void);

/* host_ns_s2tte_is_valid() */
void host_ns_s2tte_is_valid_tc1(void);
void host_ns_s2tte_is_valid_tc2(void);
void host_ns_s2tte_is_valid_tc3(void);
void host_ns_s2tte_is_valid_tc4(void);
void host_ns_s2tte_is_valid_tc5(void);
void host_ns_s2tte_is_valid_tc6(void);

/* s2tte_has_ripas() */
void s2tte_has_ripas_tc1(void);
void s2tte_has_ripas_tc2(void);

/* s2tte_is_unassigned() */
void s2tte_is_unassigned_tc1(void);

/* s2tte_is_unassigned_empty() */
void s2tte_is_unassigned_empty_tc1(void);

/* s2tte_is_unassigned_ram() */
void s2tte_is_unassigned_ram_tc1(void);

/* s2tte_is_unassigned_ns() */
void s2tte_is_unassigned_ns_tc1(void);

/* s2tte_is_unassigned_destroyed() */
void s2tte_is_unassigned_destroyed_tc1(void);

/* s2tte_is_assigned_empty() */
void s2tte_is_assigned_empty_tc1(void);

/* s2tte_is_assigned_ns() */
void s2tte_is_assigned_ns_tc1(void);
void s2tte_is_assigned_ns_tc2(void);

/* s2tte_is_assigned_ram() */
void s2tte_is_assigned_ram_tc1(void);
void s2tte_is_assigned_ram_tc2(void);

/* s2tte_is_assigned_destroyed() */
void s2tte_is_assigned_destroyed_tc1(void);

/* s2tte_is_table() */
void s2tte_is_table_tc1(void);

/* s2tte_get_ripas() */
void s2tte_get_ripas_tc1(void);
void s2tte_get_ripas_tc2(void);

/* s2tt_init_unassigned_empty() */
void s2tt_init_unassigned_empty_tc1(void);
void s2tt_init_unassigned_empty_tc2(void);

/* s2tt_init_unassigned_ram() */
void s2tt_init_unassigned_ram_tc1(void);
void s2tt_init_unassigned_ram_tc2(void);

/* s2tt_init_unassigned_ns() */
void s2tt_init_unassigned_ns_tc1(void);
void s2tt_init_unassigned_ns_tc2(void);

/* s2tt_init_unassigned_destroyed() */
void s2tt_init_unassigned_destroyed_tc1(void);
void s2tt_init_unassigned_destroyed_tc2(void);

/* s2tt_init_assigned_empty() */
void s2tt_init_assigned_empty_tc1(void);
void s2tt_init_assigned_empty_tc2(void);
void s2tt_init_assigned_empty_tc3(void);
void s2tt_init_assigned_empty_tc4(void);
void s2tt_init_assigned_empty_tc5(void);
void s2tt_init_assigned_empty_tc6(void);

/* s2tt_init_assigned_ram() */
void s2tt_init_assigned_ram_tc1(void);
void s2tt_init_assigned_ram_tc2(void);
void s2tt_init_assigned_ram_tc3(void);
void s2tt_init_assigned_ram_tc4(void);
void s2tt_init_assigned_ram_tc5(void);
void s2tt_init_assigned_ram_tc6(void);

/* s2tt_init_assigned_ns() */
void s2tt_init_assigned_ns_tc1(void);
void s2tt_init_assigned_ns_tc2(void);
void s2tt_init_assigned_ns_tc3(void);
void s2tt_init_assigned_ns_tc4(void);
void s2tt_init_assigned_ns_tc5(void);

/* s2tt_init_assigned_destroyed() */
void s2tt_init_assigned_destroyed_tc1(void);
void s2tt_init_assigned_destroyed_tc2(void);
void s2tt_init_assigned_destroyed_tc3(void);
void s2tt_init_assigned_destroyed_tc4(void);
void s2tt_init_assigned_destroyed_tc5(void);
void s2tt_init_assigned_destroyed_tc6(void);

/* s2tte_pa() */
void s2tte_pa_tc1(void);
void s2tte_pa_tc2(void);
void s2tte_pa_tc3(void);
void s2tte_pa_tc4(void);
void s2tte_pa_tc5(void);

#endif /* S2TT_TESTS_BASE_G1 */
