/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

/* This file is only used for CBMC analysis. */

#ifdef CBMC

#include <rec.h>
#include <rsi-handler.h>
#include <tb_common.h>

void handle_rsi_vdev_dma_enable(struct rec *rec,
				struct rmi_rec_exit *rec_exit,
				struct rsi_result *res)
{
	ASSERT(false, "handle_rsi_vdev_dma_enable");
}

bool finish_rsi_vdev_dma_enable(struct rec *rec,
				bool *request_finished)
{
	ASSERT(false, "finish_rsi_vdev_dma_enable");
	return true;
}

void handle_rsi_vdev_dma_disable(struct rec *rec,
				struct rmi_rec_exit *rec_exit,
				struct rsi_result *res)
{
	ASSERT(false, "handle_rsi_vdev_dma_disable");
}

bool finish_rsi_vdev_dma_disable(struct rec *rec,
				bool *request_finished)
{
	ASSERT(false, "finish_rsi_vdev_dma_disable");
	return true;
}

void handle_rsi_vdev_get_info(struct rec *rec,
			      struct rmi_rec_exit *rec_exit,
			      struct rsi_result *res)
{
	ASSERT(false, "handle_rsi_vdev_get_info");
}

bool finish_rsi_vdev_get_info(struct rec *rec,
			      struct rmi_rec_exit *rec_exit,
			      bool *request_finished)
{
	ASSERT(false, "finish_rsi_vdev_get_info");
	return true;
}

void handle_rsi_vdev_validate_mapping(struct rec *rec,
				      struct rmi_rec_exit *rec_exit,
				      struct rsi_result *res)
{
	ASSERT(false, "handle_rsi_vdev_validate_mapping");
}

bool finish_rsi_vdev_validate_mapping(struct rec *rec,
				      struct rmi_rec_exit *rec_exit,
				      bool *request_finished)
{
	ASSERT(false, "finish_rsi_vdev_validate_mapping");
	return true;
}

#endif /* CBMC */
