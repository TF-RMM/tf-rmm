/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors
 * Copyright 2021 The Hafnium Authors.
 * SPDX-FileCopyrightText: Copyright (c) 2025 NVIDIA CORPORATION & AFFILIATES. All rights reserved.
 */

#ifndef SMMUV3_H
#define SMMUV3_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

struct smmu_list;

struct smmu_stg2_config {
	unsigned long s2ttb;
	unsigned long vtcr;
	unsigned int vmid;
	unsigned int mecid;
};

/*
 * CMD_SYNC completion state supplied by a caller that issues an SMMU TLB
 * invalidation. The completion array is written by each SMMU through MSI.
 *
 * Call smmuv3_cmd_sync_init() before passing this object to an invalidation
 * interface. Its members are driver-private after initialization.
 */
struct smmuv3_cmd_sync {
	uintptr_t completion_pa;
	unsigned int completion[RMM_MAX_SMMUS];
	bool init;
};

/*
 * Initialize CMD_SYNC completion state.
 *
 * Parameters:
 *   cmd_sync	 - Completion state to initialize.
 *   cmd_sync_pa	 - Non-zero physical address of cmd_sync in the SMMU's
 * 		   physical address space.
 *
 * Return:
 *   0		 - success.
 *   -EINVAL	 - cmd_sync or its physical address is invalid.
 */
int smmuv3_cmd_sync_init(struct smmuv3_cmd_sync *cmd_sync,
			 uintptr_t cmd_sync_pa);

/*
 * Check whether all CMD_SYNC commands submitted with @cmd_sync have
 * completed.
 *
 * Return:
 *   true	- no CMD_SYNC completion word is pending.
 *   false	- at least one CMD_SYNC completion word is pending.
 */
bool smmuv3_cmd_sync_is_complete(struct smmuv3_cmd_sync *cmd_sync);

/*
 * Set up the SMMU driver and allocate resources for the SMMU instances.
 *
 * Parameters:
 *   plat_smmu_list - Pointer to the platform SMMU list containing SMMU configuration.
 *   out_pa	    - Output parameter for the physical address of allocated resources.
 *   out_sz	    - Output parameter for the size of allocated resources.
 *
 * Return:
 *   Base virtual address of the driver handle on success.
 */
uintptr_t smmuv3_driver_setup(struct smmu_list *plat_smmu_list,
				uintptr_t *out_pa, size_t *out_sz);

/*
 * Initialize all SMMU instances.
 *
 * This function walks the SMMU layout installed by smmuv3_driver_setup(),
 * disables each SMMU, probes capabilities, initializes queues, creates
 * stream tables, and finally enables Realm translation.
 *
 * Parameters:
 *   driv_hdl	- Base VA of the driver handle.
 *   hdl_sz	- Size of the driver handle.
 *
 * Return:
 *   0		- success.
 *   -EINVAL	- invalid driv_hdl or hdl_sz.
 *   -ENOMEM	- memory mapping or allocation failure.
 *   -ENODEV	- no SMMUs are defined in the layout.
 *   -ENOTSUP	- a required hardware feature is not supported, including an
 *		  SMMU output address size narrower than the CPU PA range.
 *   -ETIMEDOUT	- SMMU command timeout.
 *   -EIO	- internal SMMU error while issuing commands.
 *
 * On -ENODEV and -ENOTSUP error, no STEs are programmed and the driver's
 * internal state remains unchanged.
 */
int smmuv3_init(uintptr_t driv_hdl, size_t hdl_sz);

/*
 * Configure stage-2 translation parameters for a given TDI identifier.
 *
 * Parameters:
 *   ecam_addr	- ECAM base address identifying the Root Complex.
 *   tdi_id	- TDI identifier whose Stream Table Entry (STE) is to be populated.
 *   s2_cfg	- Pointer to the stage-2 configuration containing VTCR, VMID,
 *		  and the base address of the stage-2 translation table.
 *   sid_ptr	- Pointer to return the derived StreamID on the selected SMMU
 *		  instance from the RequesterID (TDI identifier).
 *   idx_ptr	- Pointer to return the index of the SMMU instance in the
 *		  platform SMMU list.
 *
 * Return:
 *   0		- Success.
 *   -EINVAL	- ecam_addr, tdi_id or s2_cfg is invalid, or the STE is already valid.
 *		  In this case, no driver state or STE contents are modified.
 *   -ETIMEDOUT	- Timed out while issuing the SMMU command to write the STE.
 *   -EIO	- SMMU queue or command interface error.
 *
 * On -EINVAL error, no Stream Table Entry (STE) is programmed and the driver's
 * internal state remains unchanged.
 */
int smmuv3_configure_stream(unsigned long ecam_addr, unsigned int tdi_id,
			    struct smmu_stg2_config *s2_cfg,
			    unsigned int *sid_ptr, unsigned int *idx_ptr);

/*
 * Enable a previously configured Stream Table Entry (STE) for the given
 * StreamID.
 *
 * Parameters:
 *   smmu_idx	- Index of the SMMU instance.
 *   sid	- StreamID whose STE must be enabled.
 *
 * Return:
 *   0		- success.
 *   -EINVAL	- invalid smmu_idx or sid, or STE is already enabled.
 *		  No data structures are modified and no STE update occurs.
 *   -ETIMEDOUT	- command timeout while updating the STE.
 *   -EIO	- SMMU queue or command interface error.
 *
 * On -EINVAL error, no Stream Table Entry (STE) is programmed and the driver's
 * internal state remains unchanged.
 */
int smmuv3_enable_ste(unsigned int smmu_idx, unsigned int sid);

/*
 * Disable an active Stream Table Entry for the given StreamID.
 *
 * Parameters:
 *   smmu_idx	- Index of the SMMU instance.
 *   sid	- StreamID whose STE must be disabled.
 *
 * Return:
 *   0		- success.
 *   -EINVAL	- invalid smmu_idx or sid, or STE is already disabled.
 *                No shared driver structures or STEs are updated.
 *   -ETIMEDOUT	- command timeout.
 *   -EIO	- SMMU command or queue interface error.
 *
 * On -EINVAL error, no STEs are programmed and the driver's internal state
 * remains unchanged.
 */
int smmuv3_disable_ste(unsigned int smmu_idx, unsigned int sid);

/*
 * Release a previously allocated Stream Table Entry.
 *
 * Parameters:
 *   smmu_idx	- Index of the SMMU instance.
 *   sid	- StreamID whose STE must be removed.
 *
 * Return:
 *   0		- success.
 *   -EINVAL	- invalid smmu_idx or sid, STE not allocated, or STE still valid.
 *                No driver structures are modified in this case.
 *   -ETIMEDOUT	- SMMU invalidation timeout.
 *   -EIO	- command or queue hardware error.
 *
 * On -EINVAL error, no STEs are programmed and the driver's internal state
 * remains unchanged.
 * If there are no remaining users of the Level 1 Stream Table Descriptor,
 * it is cleared and the SMMU TLBs are invalidated.
 */
int smmuv3_release_ste(unsigned int smmu_idx, unsigned int sid);

/*
 * Perform a context-wide invalidation for all SMMUs that do not support
 * broadcast TLB maintenance.
 *
 * Parameters:
 *   cmd_sync	 - Initialized CMD_SYNC completion state. Each SMMU writes
 *		   its corresponding completion word through MSI when CMD_SYNC
 *		   completes.
 *
 * Return:
 *   0		 - success, or when broadcast TLB maintenance is supported
 *                 on all SMMUs and no local invalidation is required.
 *   -ETIMEDOUT	 - timeout during command processing.
 *   -EIO	 - internal SMMU error.
 */
int smmuv3_inv(struct smmuv3_cmd_sync *cmd_sync);

/*
 * Invalidate all TLB entries at all implemented stages for a VMID on a single SMMU.
 *
 * Parameters:
 *   smmu_idx	 - Index of SMMU instance.
 *   vmid	 - Virtual Machine Identifier.
 *   cmd_sync	 - Initialized CMD_SYNC completion state.
 *
 * Return:
 *   0		 - success, or when broadcast TLB maintenance is supported
 *                 on SMMU and no local invalidation is required.
 *   -EINVAL	 - invalid smmu_idx, no actions taken.
 *   -ETIMEDOUT	 - timeout during invalidation.
 *   -EIO	 - hardware or queue processing error.
 */
int smmuv3_inv_entries(unsigned int smmu_idx, unsigned int vmid,
			struct smmuv3_cmd_sync *cmd_sync);

/*
 * Invalidate @num_entrs TLB entries within a block region for VMID.
 *
 * Parameters:
 *   vmid	 - Virtual Machine Identifier.
 *   addr	 - Base address of the block.
 *   level	 - RTT mapped level.
 *   num_entrs	 - Number of entries to invalidate.
 *   leaf	 - If 'true', validate only cached entries
 *		   for the last level of translation table walk.
 *   cmd_sync	 - Initialized CMD_SYNC completion state.
 *
 * Return:
 *   0		 - success, or when broadcast TLB maintenance is supported
 *		   on all SMMUs and no local invalidation is required.
 *   -ETIMEDOUT	 - timeout in TLB invalidation command.
 *   -EIO	 - SMMU command/queue error.
 */
int smmuv3_inv_at_level(unsigned int vmid, unsigned long addr, long level,
			unsigned long num_entrs, bool leaf,
			struct smmuv3_cmd_sync *cmd_sync);

/*
 * Submit invalidations for @vmid_list without waiting for CMD_SYNC completion.
 *
 * The caller must not reuse @cmd_sync until
 * smmuv3_cmd_sync_is_complete() returns true.
 *
 * Parameters:
 *   vmid_list	 - Pointer to an array of VMIDs to invalidate for.
 *   addr	 - Base address of the block.
 *   level	 - RTT mapped level.
 *   num_entrs	 - Number of entries to invalidate.
 *   leaf	 - If 'true', invalidate only cached entries for the last
 *		   level of translation table walk.
 *   cmd_sync	 - Initialized CMD_SYNC completion state.
 *
 * Return:
 *   0		 - commands submitted, or no local invalidation is required.
 *   -ETIMEDOUT	 - timeout submitting a command to an SMMU queue.
 *   -EIO	 - SMMU command or queue error.
 */
int smmuv3_inv_at_level_per_vmids_submit(unsigned int *vmid_list,
					 unsigned int nvmids,
					 unsigned long addr, long level,
					 unsigned long num_entrs, bool leaf,
					 struct smmuv3_cmd_sync *cmd_sync);

/*
 * Invalidate @num_entrs TLB entries mapped within block entry for a list of VMIDs.
 *
 * Parameters:
 *   vmid_list	 - Pointer to an array of VMIDs to invalidate for.
 *   addr	 - Base address of the block.
 *   level	 - RTT mapped level.
 *   num_entrs	 - Number of entries to invalidate.
 *   leaf	 - If 'true', validate only cached entries
 *		   for the last level of translation table walk.
 *   cmd_sync	 - Initialized CMD_SYNC completion state.
 *
 * Return:
 *   0		 - success, or when broadcast TLB maintenance is supported
 *                 on all SMMUs and no local invalidation is required.
 *   -ETIMEDOUT	 - timeout in TLB invalidation command.
 *   -EIO	 - SMMU command or queue error.
 */
int smmuv3_inv_at_level_per_vmids(unsigned int *vmid_list, unsigned int nvmids,
				  unsigned long addr, long level,
				  unsigned long num_entrs, bool leaf,
				  struct smmuv3_cmd_sync *cmd_sync);

#endif /* SMMUV3_H */
