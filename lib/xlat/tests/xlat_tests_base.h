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
void xlat_arch_setup_mmu_cfg_tc4(void);
void xlat_arch_setup_mmu_cfg_tc5(void);
void xlat_arch_setup_mmu_cfg_tc6(void);
void xlat_arch_setup_mmu_cfg_tc7(void);

void xlat_get_oa_from_tte_tc1(void);

#endif /* XLAT_TESTS_BASE */
