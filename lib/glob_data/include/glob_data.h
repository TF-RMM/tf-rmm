/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef GLOBDATA_H
#define GLOBDATA_H

#include <mec.h>
#include <smc-rmi.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <utils_def.h>
#include <vmid.h>
#include <xlat_low_va.h>

#define GLOBDATA_VERSION		2UL
#define GLOB_DATA_MAX_SIZE		(round_up(sizeof(struct glob_data), GRANULE_SIZE))

/* NOLINTNEXTLINE(clang-analyzer-optin.performance.Padding) as fields are in logical order*/
struct glob_data {
	unsigned long version;

	struct xlat_low_va_info low_va_info;

	uintptr_t glob_data_pa;
	uintptr_t glob_data_va;
	size_t glob_data_size;

	/* PA, VA and allocation size of struct tracking_region_data. */
	uintptr_t tracking_region_data_pa;
	uintptr_t tracking_region_data_va;
	size_t tracking_region_data_sz;

	/* Memory for SMMU driver */
	uintptr_t smmu_driv_hdl_va;
	uintptr_t smmu_driv_hdl_pa;
	size_t smmu_driv_hdl_sz;

	/* Memory for SRO contexts */
	uintptr_t sro_ctxs_pa;
	uintptr_t sro_ctxs_va;
	uintptr_t sro_ctxs_sz;

	/* Memory for VMID bitmap */
	unsigned long vmid_bitmap[VMID_ARRAY_LONG_SIZE];

	/* Memory for MEC state */
	struct mec_state_s mec_state;

	/* RMM state */
	enum rmm_state rmm_state;

	/* Firmware image sequence*/
	unsigned long fw_img_sequence;
};

uintptr_t glob_data_init(struct glob_data *gl);
uintptr_t glob_data_get_smmu_driv_hdl_va(size_t *alloc_size);
uintptr_t glob_data_get_vmids_va(size_t *alloc_size);
uintptr_t glob_data_get_mec_state_va(size_t *alloc_size);
uintptr_t glob_data_get_tracking_region_data_va(size_t *alloc_size);
enum rmm_state glob_data_get_rmm_state(void);

/*
 * Atomically change the global RMM state from @expected to @new_state. This
 * serializes callers which claim an RMM lifecycle phase before modifying
 * shared initialization data.
 *
 * Return true when the transition is committed, or false when global data is
 * unavailable or the current state does not match @expected. The function
 * does not wait for a mismatched state to change.
 */
bool glob_data_transition_rmm_state(enum rmm_state expected,
				    enum rmm_state new_state);
uintptr_t glob_data_get_sro_ctx_va(size_t *alloc_size);
unsigned long glob_data_get_fw_img_sequence(void);

#endif /* GLOBDATA_H */
