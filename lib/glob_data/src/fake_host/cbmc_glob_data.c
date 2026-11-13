/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <glob_data.h>
#include <stdbool.h>
#include <tb_common.h>

unsigned long glob_data_get_fw_img_sequence(void)
{
	ASSERT(false, "glob_data_get_fw_img_sequence");
	return 0UL;
}

/* CBMC does not model EL3 signing; fail if a ticket is requested. */
uint64_t glob_data_next_token_sign_ticket(void)
{
	ASSERT(false, "glob_data_next_token_sign_ticket");
	return 0UL;
}

uintptr_t glob_data_init(struct glob_data *gl)
{
	ASSERT(false, "glob_data_init");
	return (uintptr_t)gl;
}

uintptr_t glob_data_get_smmu_driv_hdl_va(size_t *alloc_size)
{
	ASSERT(false, "glob_data_get_smmu_driv_hdl_va");
	return 0UL;
}

uintptr_t glob_data_get_vmids_va(size_t *alloc_size)
{
	ASSERT(false, "glob_data_get_vmids_va");
	return 0UL;
}

uintptr_t glob_data_get_mec_state_va(size_t *alloc_size)
{
	ASSERT(false, "glob_data_get_mec_state_va");
	return 0UL;
}

uintptr_t glob_data_get_tracking_region_data_va(size_t *alloc_size)
{
	ASSERT(false, "glob_data_get_tracking_region_data_va");
	return 0UL;
}

enum rmm_state glob_data_get_rmm_state(void)
{
	ASSERT(false, "glob_data_get_rmm_state");
	return RMM_STATE_INIT;
}

/* CBMC stub for the unsupported global RMM lifecycle transition. */
bool glob_data_transition_rmm_state(enum rmm_state expected,
				    enum rmm_state new_state)
{
	(void)expected;
	(void)new_state;
	ASSERT(false, "glob_data_transition_rmm_state");
	return false;
}

uintptr_t glob_data_get_sro_ctx_va(size_t *alloc_size)
{
	ASSERT(false, "glob_data_get_sro_ctx_va");
	return 0UL;
}

/* LFA policy counters are outside the supported CBMC entry points. */
int glob_data_lfa_disallow_get(void)
{
	ASSERT(false, "glob_data_lfa_disallow_get");
	return 0;
}

int glob_data_lfa_disallow_put(void)
{
	ASSERT(false, "glob_data_lfa_disallow_put");
	return 0;
}
