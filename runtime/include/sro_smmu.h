/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors
 */

#ifndef SRO_SMMU_H
#define SRO_SMMU_H

/*
 * Possible states of the SRO flow for
 * - RMI_PSMMU_ACTIVATE
 * - RMI_PSMMU_DEACTIVATE
 * - RMI_PSMMU_ST_L2_CREATE
 * - RMI_PSMMU_ST_L2_DESTROY
 */
enum smmu_sro_stage {
	SRO_ACTIVATE_START,
	SRO_ACTIVATE_FINISH,
	SRO_DEACTIVATE_START,
	SRO_DEACTIVATE_FINISH,
	SRO_CREATE_L2_START,
	SRO_CREATE_L2_FINISH,
	SRO_DESTROY_L2_START,
	SRO_DESTROY_L2_FINISH,
	SRO_RECLAIM_START,
	SRO_RECLAIM_FINISH,
	SRO_SMMU_NUM_STATES
};

struct sro_context;

void smmu_continue_handler(unsigned long fid, struct smc_result *res);
void smmu_prepare_donate(struct sro_context *sro, enum smmu_sro_stage stage_id,
			 struct smc_result *res);
void smmu_prepare_reclaim(struct sro_context *sro, enum smmu_sro_stage stage_id,
			  unsigned long err_code, bool seal_ctx, struct smc_result *res);
int smmu_memory_donate(struct sro_context *sro, struct smc_result *res);
void smmu_reclaim_start(unsigned long fid, struct smc_result *res);
void smmu_memory_reclaim(enum smmu_sro_stage stage_id, struct smc_result *res);
void smmu_reclaim_finish(unsigned long fid, struct smc_result *res);

#endif /* SRO_SMMU_H */
