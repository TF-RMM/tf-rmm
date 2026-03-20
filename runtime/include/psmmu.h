/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors
 */

#ifndef PSMMU_H
#define PSMMU_H

/*
 * Activate a PSMMU.
 *
 * Parameters:
 *   psmmu_ptr	- Physical address of PSMMU identified by the base physical address of
 *		  SMMUv3_PAGE_0 for the Non-secure SMMU instance.
 *   params_ptr	- Physical address of PSMMU parameters.
 *
 * Return:
 *		- Command result.
 */
unsigned long smc_psmmu_activate(unsigned long psmmu_ptr,
				 unsigned long params_ptr);

/*
 * Deactivate a PSMMU.
 *
 * Parameters:
 *   psmmu_ptr	- Physical address of PSMMU identified by the base physical address of
 *		  SMMUv3_PAGE_0 for the Non-secure SMMU instance.
 *
 * Return:
 *		- Command result.
 */
unsigned long smc_psmmu_deactivate(unsigned long psmmu_ptr);

/*
 * Create a PSMMU Level 2 Stream Table.
 *
 * Parameters:
 *   psmmu_ptr	- Physical address of PSMMU identified by the base physical address of
 *		  SMMUv3_PAGE_0 for the Non-secure SMMU instance.
 *   sid	- Base of StreamID range described by the Level 2 Stream Table.
 *
 * Return:
 *		- Command result.
 */
unsigned long smc_psmmu_st_l2_create(unsigned long psmmu_ptr, unsigned long sid);

/*
 * Destroy a PSMMU Level 2 Stream Table.
 *
 * Parameters:
 *   psmmu_ptr	- Physical address of PSMMU identified by the base physical address of
 *		  SMMUv3_PAGE_0 for the Non-secure SMMU instance.
 *   sid	- Base of StreamID range described by the Level 2 Stream Table.
 *
 * Return:
 *		- Command result.
 */
unsigned long smc_psmmu_st_l2_destroy(unsigned long psmmu_ptr, unsigned long sid);

#endif /* PSMMU_H */
