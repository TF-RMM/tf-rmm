/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef RSI_HOST_CALL_H
#define RSI_HOST_CALL_H

#include <rsi-walk.h>
#include <smc-rmi.h>

struct rmi_rec_entry;
struct rmi_rec_exit;

struct rsi_host_call_result {
	/*
	 * Result of RTT walk performed by RSI command.
	 */
	struct rsi_walk_result walk_result;

	/*
	 * If @walk_result.abort is false,
	 * @smc_result contains X0 value to be returned to the Realm.
	 */
	unsigned long smc_result;
};

struct rsi_host_call_result handle_rsi_host_call(struct rec *rec,
						 struct rmi_rec_exit *rec_exit);

struct rsi_walk_result complete_rsi_host_call(struct rec *rec,
					      struct rmi_rec_entry *rec_entry);

#endif /* RSI_HOST_CALL_H */
