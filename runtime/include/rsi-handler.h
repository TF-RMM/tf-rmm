/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef RSI_HANDLER_H
#define RSI_HANDLER_H

#include <rsi-walk.h>
#include <smc.h>

struct rec;
struct rmi_rec_exit;

/*
 * If set, update REC registers to values provided by the handler.
 */
#define FLAG_UPDATE_REC		1U

/*
 * If set, exit to Host.  Otherwise, return to Realm.
 */
#define FLAG_EXIT_TO_HOST	2U

/*
 * If set, present emulated Stage 2 abort to Host.
 */
#define FLAG_STAGE_2_ABORT	4U

/*
 * If set, handler has changed the active Plane.
 */
#define FLAG_PLANE_CHANGED	8U

enum rsi_action {
	/*
	 * Update REC registers to values provided by the handler,
	 * and return to Realm.
	 */
	UPDATE_REC_RETURN_TO_REALM	= FLAG_UPDATE_REC,

	/*
	 * Leave REC registers unchanged, and exit to Host,
	 * with rec_exit fields populated by the handler.
	 */
	EXIT_TO_HOST			= FLAG_EXIT_TO_HOST,

	/*
	 * Update REC registers to values provided by the handler,
	 * with rec_exit fields and exit to Host, with rec_exit
	 * fields populated by the handler.
	 */
	UPDATE_REC_EXIT_TO_HOST		= FLAG_UPDATE_REC |
					  FLAG_EXIT_TO_HOST,

	/*
	 * Exit to Host, indicating a Stage 2 translation fault
	 * encountered by the handler.
	 */
	STAGE_2_TRANSLATION_FAULT	= FLAG_EXIT_TO_HOST |
					  FLAG_STAGE_2_ABORT,

	/*
	 * Active Plane in Realm changed and the new Plane GPRS have been
	 * programmed by the handler.
	 */
	PLANE_CHANGED_RETURN_TO_REALM	= FLAG_PLANE_CHANGED
};

/*
 * Result of RSI command handler
 */
struct rsi_result {
	/*
	 * Action which should be taken following execution of the handler.
	 */
	enum rsi_action action;

	/*
	 * If the handler performed an RTT walk,
	 * @rtt_level is the level at which the walk terminated.
	 */
	unsigned long rtt_level;

	/*
	 * If @action is RETURN_TO_REALM,
	 * @smc_result contains GPR values to be returned to the Realm.
	 */
	struct smc_result smc_res;
};

void handle_rsi_version(struct rec *rec, struct rsi_result *res);
void handle_rsi_features(struct rec *rec, struct rsi_result *res);
void handle_rsi_realm_config(struct rec *rec, struct rsi_result *res);
void handle_rsi_host_call(struct rec *rec, struct rmi_rec_exit *rec_exit,
			  struct rsi_result *res);
void handle_rsi_ipa_state_set(struct rec *rec, struct rmi_rec_exit *rec_exit,
			      struct rsi_result *res);
void handle_rsi_ipa_state_get(struct rec *rec, struct rsi_result *res);
void handle_rsi_measurement_read(struct rec *rec, struct rsi_result *res);
void handle_rsi_measurement_extend(struct rec *rec, struct rsi_result *res);
void handle_rsi_attest_token_init(struct rec *rec, struct rsi_result *res);
void handle_rsi_attest_token_continue(struct rec *rec,
				      struct rmi_rec_exit *rec_exit,
				      struct rsi_result *res);
void handle_psci(struct rec *rec, struct rmi_rec_exit *rec_exit,
		 struct rsi_result *res);
void handle_rsi_mem_get_perm_value(struct rec *rec, struct rsi_result *res);
void handle_rsi_mem_set_perm_value(struct rec *rec, struct rsi_result *res);
void handle_rsi_mem_set_perm_index(struct rec *rec,
				   struct rmi_rec_exit *rec_exit,
				   struct rsi_result *res);
void handle_rsi_plane_enter(struct rec *rec, struct rsi_result *res);
void handle_rsi_plane_sysreg_read(struct rec *rec, struct rsi_result *res);
void handle_rsi_plane_sysreg_write(struct rec *rec, struct rsi_result *res);
void handle_rsi_rdev_get_instance_id(struct rec *rec,
				     struct rmi_rec_exit *rec_exit,
				     struct rsi_result *res);
void handle_rsi_rdev_get_info(struct rec *rec, struct rsi_result *res);
void handle_rsi_rdev_get_state(struct rec *rec, struct rsi_result *res);
void handle_rsi_rdev_get_measurements(struct rec *rec,
				      struct rmi_rec_exit *rec_exit,
				      struct rsi_result *res);
void handle_rsi_rdev_lock(struct rec *rec, struct rmi_rec_exit *rec_exit,
			  struct rsi_result *res);
void handle_rsi_rdev_start(struct rec *rec, struct rmi_rec_exit *rec_exit,
			   struct rsi_result *res);
void handle_rsi_rdev_stop(struct rec *rec, struct rmi_rec_exit *rec_exit,
			  struct rsi_result *res);
void handle_rsi_rdev_get_interface_report(struct rec *rec,
					  struct rmi_rec_exit *rec_exit,
					  struct rsi_result *res);
void handle_rsi_rdev_continue(struct rec *rec, struct rmi_rec_exit *rec_exit,
			      struct rsi_result *res);
void handle_rsi_rdev_validate_mapping(struct rec *rec,
				      struct rmi_rec_exit *rec_exit,
				      struct rsi_result *res);
#endif /* RSI_HANDLER_H */
