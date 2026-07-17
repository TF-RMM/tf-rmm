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
 *   res	- Pointer to a structure where the command result will be stored.
 *
 * Return:
 *		- Command result.
 */
void smc_psmmu_activate(unsigned long psmmu_ptr, unsigned long params_ptr,
			struct smc_result *res);

/*
 * Deactivate a PSMMU.
 *
 * Parameters:
 *   psmmu_ptr	- Physical address of PSMMU identified by the base physical address of
 *		  SMMUv3_PAGE_0 for the Non-secure SMMU instance.
 *   res	- Pointer to a structure where the command result will be stored.
 *
 * Return:
 *		- Command result.
 */
void smc_psmmu_deactivate(unsigned long psmmu_ptr, struct smc_result *res);

/*
 * Create a PSMMU Level 2 Stream Table.
 *
 * Parameters:
 *   psmmu_ptr	- Physical address of PSMMU identified by the base physical address of
 *		  SMMUv3_PAGE_0 for the Non-secure SMMU instance.
 *   sid	- Base of StreamID range described by the Level 2 Stream Table.
 *   res	- Pointer to a structure where the command result will be stored.
 *
 * Return:
 *		- Command result.
 */
void smc_psmmu_st_l2_create(unsigned long psmmu_ptr, unsigned long sid,
				struct smc_result *res);

/*
 * Destroy a PSMMU Level 2 Stream Table.
 *
 * Parameters:
 *   psmmu_ptr	- Physical address of PSMMU identified by the base physical address of
 *		  SMMUv3_PAGE_0 for the Non-secure SMMU instance.
 *   sid	- Base of StreamID range described by the Level 2 Stream Table.
 *   res	- Pointer to a structure where the command result will be stored.
 *
 * Return:
 *		- Command result.
 */
void smc_psmmu_st_l2_destroy(unsigned long psmmu_ptr, unsigned long sid,
				struct smc_result *res);

void psmmu_activate_start(unsigned long fid, struct smc_result *res);
void psmmu_activate_finish(unsigned long fid, struct smc_result *res);
void psmmu_deactivate_start(unsigned long fid, struct smc_result *res);
void psmmu_deactivate_finish(unsigned long fid, struct smc_result *res);
void psmmu_create_l2_start(unsigned long fid, struct smc_result *res);
void psmmu_create_l2_finish(unsigned long fid, struct smc_result *res);
void psmmu_destroy_l2_start(unsigned long fid, struct smc_result *res);
void psmmu_destroy_l2_finish(unsigned long fid, struct smc_result *res);

#endif /* PSMMU_H */
