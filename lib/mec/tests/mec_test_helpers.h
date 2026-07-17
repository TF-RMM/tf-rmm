/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

void mec_test_setup(void);
void mec_test_teardown(void);
void no_mec_test_setup(void);
void no_mec_test_teardown(void);
void no_sctlr2_mec_test_setup(void);
void no_sctlr2_mec_test_teardown(void);

int register_custom_mecid_a1_el2_callbacks(void);
bool check_mecid_a1_el2_modified_clear(void);
bool check_mecid_a1_el2_read_clear(void);

int register_custom_vmecid_p_el2_callbacks(void);
bool check_vmecid_p_el2_modified_clear(void);
bool check_vmecid_p_el2_read_clear(void);

void mec_test_realm_mecid_s2_init(unsigned int mecid);

void reset_mecidr_el2(unsigned int value);
void reset_firme_mecid_width(unsigned int width);
void set_firme_mecid_refresh(bool enable);
void set_firme_mecid_fr1(bool enable);
