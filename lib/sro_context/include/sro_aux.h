/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef SRO_AUX_H
#define SRO_AUX_H

#include <smc-rmi.h>
#include <smc.h>
#include <stdbool.h>

#define SRO_AUX_GRANULES_MAX		U(32)

COMPILER_ASSERT(SRO_AUX_GRANULES_MAX >= MAX_REC_AUX_GRANULES);
COMPILER_ASSERT(SRO_AUX_GRANULES_MAX >= PDEV_PARAM_AUX_GRANULES_MAX);

struct sro_context;

/* Prototype of the handles to use for SRO operations */
/* cppcheck-suppress misra-c2012-2.3 */
typedef void (*sro_handle_cb)(unsigned long fid, struct smc_result *res);

enum sro_obj_cb_id {
	SRO_OBJ_MEM_RECLAIM,
	SRO_OBJ_MEM_DONATE,
	SRO_OBJ_CREATE_CONTINUE,
	SRO_OBJ_DESTROY_FINISH
};

/*
 * Common state for SRO flows that donate and reclaim auxiliary granules.
 */
struct sro_aux_op_ctx {
	/* Index of the callback to invoke */
	enum sro_obj_cb_id cb_id;

	/* Address of object granule associated with the aux flow */
	unsigned long obj_addr;

	/* Error condition in case the object creation flow fails */
	unsigned long ret_err;

	/* List of PAs for the auxiliary granules donated by the host */
	uintptr_t aux_granules_pa[SRO_AUX_GRANULES_MAX];

	/* Number of granules requested */
	unsigned long requested_aux_granules;

	/* Number of granules donated or reclaimed so far */
	unsigned long total_transferred;

	/* The state of the aux granule that is donated */
	unsigned char aux_granule_state;
};

/*
 * Initialize a donated-auxiliary-memory flow and return the first donate
 * request to the host.
 */
void sro_aux_op_init_donate(struct sro_context *sro,
			    struct smc_result *res,
			    unsigned long obj_addr,
			    unsigned long requested_aux_granules,
			    unsigned char aux_granule_state);

/*
 * Start reclaiming previously donated auxiliary granules.
 */
void sro_aux_op_start_reclaim(struct sro_context *sro,
			      struct smc_result *res,
			      unsigned long obj_addr,
			      bool seal_ctx,
			      unsigned long err_code,
			      unsigned long num_granules,
			      unsigned char aux_granule_state);

/*
 * SRO handle callback for RMI_OP_MEM_RECLAIM.
 */
void sro_obj_memory_reclaim(unsigned long fid, struct smc_result *res);

/*
 * SRO handle callback for RMI_OP_MEM_DONATE during object creation.
 */
void sro_obj_memory_donate(unsigned long fid, struct smc_result *res);

/*
 * Complete an auxiliary-granule flow with the stored error status.
 */
void sro_aux_op_reclaim_finish(unsigned long fid, struct smc_result *res);

#endif /* SRO_AUX_H */
