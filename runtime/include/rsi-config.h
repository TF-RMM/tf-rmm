/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef RSI_CONFIG_H
#define RSI_CONFIG_H

#include <rsi-walk.h>
#include <smc.h>

struct rec;

struct rsi_config_result {
	/*
	 * Result of RTT walk performed by RSI command.
	 */
	struct rsi_walk_result walk_result;

	/*
	 * If @walk_result.abort is false, @smc_res contains GPR values to be
	 * returned to the Realm.
	 */
	struct smc_result smc_res;
};

struct rsi_config_result handle_rsi_realm_config(struct rec *rec);

#endif /* RSI_CONFIG_H */
