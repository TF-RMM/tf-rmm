/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <dev_granule.h>
#include <glob_data.h>
#include <granule.h>
#include <stdbool.h>
#include <tb_common.h>

/* The granules are directly allocated and initialized in host_cbmc layer*/
uintptr_t glob_data_get_granules_va(size_t *alloc_size)
{
	ASSERT(false, "glob_data_get_granules_va");
	return 0UL;
}

uintptr_t glob_data_get_dev_granules_va(size_t *alloc_size)
{
	ASSERT(false, "glob_data_get_dev_granules_va");
	return 0UL;
}

unsigned long glob_data_get_fw_img_sequence(void)
{
	ASSERT(false, "glob_data_get_fw_img_sequence");
	return 0UL;
}

uintptr_t glob_data_init(struct glob_data *gl,
		unsigned long max_granules, unsigned long max_dev_granules)
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

enum rmm_state glob_data_get_rmm_state(void)
{
	ASSERT(false, "glob_data_get_rmm_state");
	return RMM_STATE_INIT;
}

void glob_data_set_rmm_state(enum rmm_state state)
{
	ASSERT(false, "glob_data_set_rmm_state");
}

uintptr_t glob_data_get_sro_ctx_va(size_t *alloc_size)
{
	ASSERT(false, "glob_data_get_sro_ctx_va");
	return 0UL;
}
