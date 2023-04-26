/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef RSI_HANDLER_H
#define RSI_HANDLER_H

#include <rsi-walk.h>
#include <smc.h>

/*
 * Result of an RSI command which performed an RTT walk.
 */
struct rsi_result {
	/*
	 * Result of RTT walk performed by RSI command.
	 */
	struct rsi_walk_result walk_result;

	/*
	 * If @walk_result.abort is false,
	 * @smc_res contains GPR values to be returned to the Realm.
	 */
	struct smc_result smc_res;
};

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

unsigned long handle_rsi_version(void);
struct rsi_result handle_rsi_realm_config(struct rec *rec);
struct rsi_result handle_rsi_host_call(struct rec *rec,
				       struct rmi_rec_exit *rec_exit);
bool handle_rsi_ipa_state_set(struct rec *rec, struct rmi_rec_exit *rec_exit);
struct rsi_walk_smc_result handle_rsi_ipa_state_get(struct rec *rec);
unsigned long handle_rsi_read_measurement(struct rec *rec);
unsigned long handle_rsi_extend_measurement(struct rec *rec);
unsigned long handle_rsi_attest_token_init(struct rec *rec);
void attest_realm_token_sign_continue_start(void);
void handle_rsi_attest_token_continue(struct rec *rec,
				      struct attest_result *res);
void attest_realm_token_sign_continue_finish(void);

#endif /* RSI_HANDLER_H */
