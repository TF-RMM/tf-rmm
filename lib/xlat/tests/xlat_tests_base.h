/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef XLAT_TESTS_BASE
#define XLAT_TESTS_BASE

void map_region_full_spec_tc1(void);
void map_region_tc1(void);
void map_region_flat_tc1(void);
void map_region_transient_tc1(void);

void xlat_ctx_cfg_init_tc1(void);
void xlat_ctx_cfg_init_tc2(void);
void xlat_ctx_cfg_init_tc3(void);
void xlat_ctx_cfg_init_tc4(void);
void xlat_ctx_cfg_init_tc5(void);
void xlat_ctx_cfg_init_tc6(void);
void xlat_ctx_cfg_init_tc7(void);
void xlat_ctx_cfg_init_tc8(void);
void xlat_ctx_cfg_init_tc9(void);
void xlat_ctx_cfg_init_tc10(void);
void xlat_ctx_cfg_init_tc11(void);
void xlat_ctx_cfg_init_tc12(void);
void xlat_ctx_cfg_init_tc13(void);
void xlat_ctx_cfg_init_tc14(void);

void xlat_ctx_init_tc1(void);
void xlat_ctx_init_tc2(void);
void xlat_ctx_init_tc3(void);
void xlat_ctx_init_tc4(void);
void xlat_ctx_init_tc5(void);

void xlat_get_llt_from_va_tc1(void);
void xlat_get_llt_from_va_tc2(void);
void xlat_get_llt_from_va_tc3(void);
void xlat_get_llt_from_va_tc4(void);
void xlat_get_llt_from_va_tc5(void);
void xlat_get_llt_from_va_tc6(void);
void xlat_get_llt_from_va_tc7(void);
void xlat_get_llt_from_va_tc8(void);
void xlat_get_llt_from_va_tc9(void);

void xlat_get_tte_ptr_tc1(void);
void xlat_get_tte_ptr_tc2(void);
void xlat_get_tte_ptr_tc3(void);
void xlat_get_tte_ptr_tc4(void);

void xlat_unmap_memory_page_tc1(void);
void xlat_unmap_memory_page_tc2(void);
void xlat_unmap_memory_page_tc3(void);

void xlat_map_memory_page_with_attrs_tc1(void);
void xlat_map_memory_page_with_attrs_tc2(void);
void xlat_map_memory_page_with_attrs_tc3(void);

void xlat_arch_setup_mmu_cfg_tc1(void);
void xlat_arch_setup_mmu_cfg_tc2(void);
void xlat_arch_setup_mmu_cfg_tc3(void);
void xlat_arch_setup_mmu_cfg_tc6(void);
void xlat_arch_setup_mmu_cfg_tc7(void);

void xlat_get_oa_from_tte_tc1(void);

/* xlat_map_l3_region and xlat_unmap_l3_region tests */
void xlat_map_l3_region_basic_tc1(void);
void xlat_map_l3_region_basic_tc2(void);
void xlat_map_l3_region_basic_tc3(void);
void xlat_map_l3_region_errors_tc1(void);
void xlat_map_l3_region_errors_tc2(void);
void xlat_unmap_l3_region_basic_tc1(void);
void xlat_unmap_l3_region_basic_tc2(void);
void xlat_unmap_l3_region_basic_tc3(void);
void xlat_unmap_l3_region_errors_tc1(void);
void xlat_va_alloc_boundaries_tc1(void);
void xlat_va_alloc_boundaries_tc2(void);
void xlat_va_alloc_boundaries_tc3(void);

/* VA allocation validation tests */
void xlat_va_alloc_flag_propagation_tc1(void);
void xlat_va_alloc_multi_l2_tc1(void);
void xlat_va_alloc_table_shape_tc1(void);
void xlat_va_alloc_multi_region_tc1(void);
void xlat_va_alloc_multi_region_tc2(void);
void xlat_va_alloc_search_reset_tc1(void);
void xlat_va_alloc_exhaust_va_space_tc1(void);
void xlat_va_alloc_va_end_boundary_tc1(void);

/* Stitch table tests */
void xlat_stitch_l1_success_tc1(void);
void xlat_stitch_l1_single_block_tc1(void);
void xlat_stitch_l1_multiple_blocks_tc1(void);
void xlat_stitch_l1_verify_transient_tc1(void);
void xlat_stitch_l1_at_boundaries_tc1(void);

#endif /* XLAT_TESTS_BASE */
