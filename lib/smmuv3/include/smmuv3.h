/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors
 * Copyright 2021 The Hafnium Authors.
 * SPDX-FileCopyrightText: Copyright (c) 2025 NVIDIA CORPORATION & AFFILIATES. All rights reserved.
 */

#ifndef SMMUV3_H
#define SMMUV3_H

#include <rmm_el3_ifc.h>

/* TODO: get SMMUv3 index from the Boot Manifest */
#define SMMU_IDX	0UL

struct smmu_stg2_config {
	unsigned long s2ttb;
	unsigned long vtcr;
	unsigned int vmid;
};

/*
 * Set up the SMMU driver and allocate resources for the SMMU instances.
 *
 * Parameters:
 *   plat_smmu_list - Pointer to the platform SMMU list containing SMMU configuration.
 *   out_pa         - Output parameter for the physical address of allocated resources.
 *   out_sz         - Output parameter for the size of allocated resources.
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
 *   driv_hdl       - Base VA of the driver handle.
 *   hdl_sz         - Size of the driver handle.
 *
 * Return:
 *   0          - success.
 *   -EINVAL    - invalid driv_hdl or hdl_sz.
 *   -ENOMEM    - memory mapping or allocation failure.
 *   -ENODEV    - no SMMUs are defined in the layout.
 *   -ENOTSUP   - a required hardware feature is not supported.
 *   -ETIMEDOUT - SMMU command timeout.
 *   -EIO       - internal SMMU error while issuing commands.
 *
 * On -ENODEV and -ENOTSUP error, no STEs are programmed and the driver's
 * internal state remains unchanged.
 */
int smmuv3_init(uintptr_t driv_hdl, size_t hdl_sz);

/*
 * Configure stage-2 translation parameters for a StreamID.
 *
 * Parameters:
 *   smmu_idx  - Index of the SMMU instance in the platform SMMU list.
 *   s2_cfg    - Pointer to stage-2 configuration describing VTCR, VMID, and
 *               the base address of the stage-2 translation table.
 *   sid       - StreamID whose STE must be populated.
 *
 * Return:
 *   0          - success.
 *   -EINVAL    - smmu_idx, sid, or s2_cfg is invalid, or STE is already valid.
 *                No driver state or STE contents are modified.
 *   -ETIMEDOUT - SMMU command timeout while writing the STE.
 *   -EIO       - SMMU queue or command interface error.
 *
 * On -EINVAL error, no Stream Table Entries (STEs) are programmed and the
 * driver's internal state remains unchanged.
 */
int smmuv3_configure_stream(unsigned long smmu_idx,
			    struct smmu_stg2_config *s2_cfg,
			    unsigned int sid);

/*
 * Enable a previously configured Stream Table Entry (STE) for the given
 * StreamID.
 *
 * Parameters:
 *   smmu_idx  - Index of the SMMU instance.
 *   sid       - StreamID whose STE must be enabled.
 *
 * Return:
 *   0          - success.
 *   -EINVAL    - invalid smmu_idx or sid, or STE is already enabled.
 *                No data structures are modified and no STE update occurs.
 *   -ETIMEDOUT - command timeout while updating the STE.
 *   -EIO       - SMMU queue or command interface error.
 *
 * On -EINVAL error, no STEs are programmed and the driver's internal state
 * remains unchanged.
 */
int smmuv3_enable_ste(unsigned long smmu_idx, unsigned int sid);

/*
 * Disable an active Stream Table Entry for the given StreamID.
 *
 * Parameters:
 *   smmu_idx  - Index of the SMMU instance.
 *   sid       - StreamID whose STE must be disabled.
 *
 * Return:
 *   0          - success.
 *   -EINVAL    - invalid smmu_idx or sid, or STE is already disabled.
 *                No shared driver structures or STEs are updated.
 *   -ETIMEDOUT - command timeout.
 *   -EIO       - SMMU command or queue interface error.
 *
 * On -EINVAL error, no STEs are programmed and the driver's internal state
 * remains unchanged.
 */
int smmuv3_disable_ste(unsigned long smmu_idx, unsigned int sid);

/*
 * Allocate the Stream Table Entry for a StreamID.
 *
 * Parameters:
 *   smmu_idx  - Index of the SMMU instance.
 *   sid       - StreamID requiring an STE.
 *
 * Return:
 *   0          - success.
 *   -EINVAL    - invalid smmu_idx or sid, driver state not modified.
 *   -ENOMEM    - the StreamID is already allocated or bitmap resources are exhausted.
 *   -ETIMEDOUT - timeout in SMMU invalidation or queue operations.
 *   -EIO       - SMMU command interface error.
 *
 * On -EINVAL and -ENOMEM errors, no STEs are programmed and the driver's
 * internal state remains unchanged.
 * This function initialises Level 1 Stream Table Descriptor if it has not yet
 * been set.
 * No STE content is written until the allocation succeeds.
 */
int smmuv3_allocate_ste(unsigned long smmu_idx, unsigned int sid);

/*
 * Release a previously allocated Stream Table Entry.
 *
 * Parameters:
 *   smmu_idx  - Index of the SMMU instance.
 *   sid       - StreamID whose STE must be removed.
 *
 * Return:
 *   0          - success.
 *   -EINVAL    - invalid smmu_idx or sid, STE not allocated, or STE still valid.
 *                No driver structures are modified in this case.
 *   -ETIMEDOUT - SMMU invalidation timeout.
 *   -EIO       - command or queue hardware error.
 *
 * On -EINVAL error, no STEs are programmed and the driver's internal state
 * remains unchanged.
 * If there are no remaining users of the Level 1 Stream Table Descriptor,
 * it is cleared and the SMMU TLBs are invalidated.
 */
int smmuv3_release_ste(unsigned long smmu_idx, unsigned int sid);

/*
 * Perform a context-wide invalidation for all SMMUs that do not support
 * broadcast TLB maintenance.
 *
 * Return:
 *   0          - success, or when broadcast TLB maintenance is supported
 *                on all SMMUs and no local invalidation is required.
 *   -ETIMEDOUT - timeout during command processing.
 *   -EIO       - internal SMMU error.
 */
int smmuv3_inv(void);

/*
 * Invalidate a single 4KB page in the stage-2 TLB for a VMID.
 *
 * Parameters:
 *   vmid  - Virtual Machine Identifier.
 *   addr  - Intermediate physical address (IPA) aligned to 4KB.
 *
 * Return:
 *   0          - success, or when broadcast TLB maintenance is supported
 *                on all SMMUs and no local invalidation is required.
 *   -EINVAL    - incorrect addr alignment, no actions taken.
 *   -ETIMEDOUT - timeout in TLB invalidation command.
 *   -EIO       - SMMU command/queue error.
 */
int smmuv3_inv_page(unsigned int vmid, unsigned long addr);

/*
 * Invalidate a 4KB block of IPA space for a VMID.
 *
 * Parameters:
 *   vmid  - Virtual Machine Identifier.
 *   addr  - Base address of block aligned to 4KB.
 *
 * Return:
 *   0          - success, or when broadcast TLB maintenance is supported
 *                on all SMMUs and no local invalidation is required.
 *   -EINVAL    - incorrect addr alignment, no actions taken.
 *   -ETIMEDOUT - timeout in TLB invalidation command.
 *   -EIO       - SMMU command/queue error.
 */
int smmuv3_inv_block(unsigned int vmid, unsigned long addr);

/*
 * Invalidate all pages within a 2MB block.
 *
 * Parameters:
 *   vmid  - Virtual Machine Identifier.
 *   addr  - Base address of the block aligned to 2MB.
 *
 * Return:
 *   0          - success, or when broadcast TLB maintenance is supported
 *                on all SMMUs and no local invalidation is required.
 *   -EINVAL    - incorrect addr alignment, no actions taken.
 *   -ETIMEDOUT - timeout in TLB invalidation command.
 *   -EIO       - SMMU command/queue error.
 */
int smmuv3_inv_pages_in_block(unsigned int vmid, unsigned long addr);

/*
 * Invalidate all TLB entries at all implemented stages for a VMID on a single SMMU.
 *
 * Parameters:
 *   smmu_idx  - Index of SMMU instance.
 *   vmid      - Virtual Machine Identifier.
 *
 * Return:
 *   0          - success, or when broadcast TLB maintenance is supported
 *                on SMMU and no local invalidation is required.
 *   -EINVAL    - invalid smmu_idx, no actions taken.
 *   -ETIMEDOUT - timeout during invalidation.
 *   -EIO       - hardware or queue processing error.
 */
int smmuv3_inv_entries(unsigned long smmu_idx, unsigned int vmid);

#endif /* SMMUV3_H */
