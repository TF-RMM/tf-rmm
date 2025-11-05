/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <assert.h>
#include <dev.h>
#include <rsi-handler.h>

void handle_rsi_rdev_get_info(struct rec *rec, struct rsi_result *res)
{
	(void)rec;
	(void)res;
	assert(false);
}

void handle_rsi_rdev_get_instance_id(struct rec *rec,
				     struct rmi_rec_exit *rec_exit,
				     struct rsi_result *res)
{
	(void)rec;
	(void)rec_exit;
	(void)res;
	assert(false);
}

void handle_rsi_rdev_validate_mapping(struct rec *rec,
				      struct rmi_rec_exit *rec_exit,
				      struct rsi_result *res)
{
	(void)rec;
	(void)rec_exit;
	(void)res;
	assert(false);
}

void handle_rsi_rdev_continue(struct rec *rec, struct rmi_rec_exit *rec_exit,
			      struct rsi_result *res)
{
	(void)rec;
	(void)rec_exit;
	(void)res;
	assert(false);
}

void rdev_state_transition(struct realm_device *rdev,
			   unsigned long dev_comm_state)
{
	(void)rdev;
	(void)dev_comm_state;
	assert(false);
}

/*
 * Called from REC enter to check if RDEV communication request is completed by
 * the VDEV
 */
void handle_rsi_rdev_complete(struct rec *rec)
{
	(void)rec;
	assert(false);
}
