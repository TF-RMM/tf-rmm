/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef REALM_ATTEST_H
#define REALM_ATTEST_H

#include <rsi-walk.h>
#include <stdbool.h>

struct rec;

struct attest_result {
	/*
	 * If true, RMM should repeat the operation.
	 *
	 * If false, contents of @access are valid.
	 */
	bool incomplete;

	/*
	 * Result of RTT walk performed by RSI command.
	 */
	struct rsi_walk_result walk_result;

	/*
	 * If @incomplete is false and @walk_result.abort is false,
	 * @smc_result contains GPR values to be returned to the Realm.
	 */
	struct smc_result smc_res;
};

unsigned long handle_rsi_read_measurement(struct rec *rec);
unsigned long handle_rsi_extend_measurement(struct rec *rec);
unsigned long handle_rsi_attest_token_init(struct rec *rec);
void handle_rsi_attest_token_continue(struct rec *rec,
				      struct attest_result *res);

#endif /* REALM_ATTEST_H */
