/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <attestation.h>
#include <debug.h>
#include <granule.h>
#include <measurement.h>
#include <realm.h>
#include <rsi-handler.h>
#include <smc-rsi.h>
#include <smc.h>
#include <string.h>
#include <utils_def.h>

#define MAX_EXTENDED_SIZE	(64U)
#define MAX_MEASUREMENT_WORDS	(MAX_MEASUREMENT_SIZE / sizeof(unsigned long))
/*
 * Return the Realm Personalization Value.
 *
 * Arguments:
 * rd    - The Realm descriptor.
 * claim_ptr - The start address of the Realm Personalization Value claim
 * claim_len - The length of the Realm Personalization Value claim
 */
static void get_rpv(struct rd *rd, void **claim_ptr, size_t *claim_len)
{
	*claim_ptr = (uint8_t *)&(rd->rpv[0]);
	*claim_len = RPV_SIZE;
}

/*
 * Function to continue with the sign operation
 */
static void attest_token_continue_sign_state(
					struct rec_attest_data *attest_data,
					struct rsi_result *res)
{
	/*
	 * Sign and finish creating the token.
	 */
	enum attest_token_err_t ret =
		attest_realm_token_sign(&(attest_data->token_sign_ctx.ctx),
					&(attest_data->rmm_realm_token_len));
	if ((ret == ATTEST_TOKEN_ERR_COSE_SIGN_IN_PROGRESS) ||
		(ret == ATTEST_TOKEN_ERR_SUCCESS)) {
		/*
		 * Return to RSI handler function after each iteration
		 * to check is there anything else to do (pending IRQ)
		 * or next signing iteration can be executed.
		 */
		res->smc_res.x[0] = RSI_INCOMPLETE;

		/* If this was the last signing cycle */
		if (ret == ATTEST_TOKEN_ERR_SUCCESS) {
			attest_data->token_sign_ctx.state =
				ATTEST_SIGN_TOKEN_WRITE_IN_PROGRESS;
		}
	} else {
		/* Accessible only in case of failure during token signing */
		ERROR("FATAL_ERROR: Realm token creation failed\n");
		panic();
	}
}

/*
 * Function to continue with the token write operation
 */
static void attest_token_continue_write_state(struct rec *rec,
					      struct rsi_result *res)
{
	struct granule *gr;
	uintptr_t realm_att_token;
	unsigned long realm_att_token_ipa = rec->regs[1];
	unsigned long offset = rec->regs[2];
	unsigned long size = rec->regs[3];
	enum s2_walk_status walk_status;
	struct s2_walk_result walk_res = { 0UL };
	size_t attest_token_len, length;
	struct rec_attest_data *attest_data = rec->aux_data.attest_data;
	uintptr_t cca_token_buf = rec->aux_data.cca_token_buf;

	/*
	 * Translate realm granule IPA to PA. If returns with
	 * WALK_SUCCESS then the last level page table (llt),
	 * which holds the realm_att_token_buf mapping, is locked.
	 */
	walk_status = realm_ipa_to_pa(rec, realm_att_token_ipa, &walk_res);

	/* Walk parameter validity was checked by RSI_ATTESTATION_TOKEN_INIT */
	assert(walk_status != WALK_INVALID_PARAMS);

	if (walk_status == WALK_FAIL) {
		if (walk_res.ripas_val == RIPAS_EMPTY) {
			res->smc_res.x[0] = RSI_ERROR_INPUT;
		} else {
			/*
			 * Translation failed, IPA is not mapped.
			 * Return to NS host to fix the issue.
			 */
			res->action = STAGE_2_TRANSLATION_FAULT;
			res->rtt_level = walk_res.rtt_level;
		}
		return;
	}

	if (size == 0UL) {
		res->smc_res.x[0] = RSI_SUCCESS;
		return;
	}

	/* Map realm data granule to RMM address space */
	gr = find_granule(walk_res.pa);
	realm_att_token = (uintptr_t)granule_map(gr, SLOT_RSI_CALL);
	assert(realm_att_token != 0UL);

	if (attest_data->token_sign_ctx.copied_len == 0UL) {
		attest_token_len = attest_cca_token_create(
					(void *)cca_token_buf,
					REC_ATTEST_TOKEN_BUF_SIZE,
					&attest_data->rmm_realm_token_buf,
					attest_data->rmm_realm_token_len);

		if (attest_token_len == 0UL) {
			res->smc_res.x[0] = RSI_ERROR_INPUT;

			/* The signing has failed. Reset the state. */
			attest_data->token_sign_ctx.state =
						ATTEST_SIGN_NOT_STARTED;
			goto out_unmap;
		}

		attest_data->token_sign_ctx.cca_token_len = attest_token_len;
	} else {
		attest_token_len = attest_data->token_sign_ctx.cca_token_len;
	}

	length = (size < attest_token_len) ? size : attest_token_len;

	/* Copy attestation token */
	(void)memcpy((void *)(realm_att_token + offset),
		     (void *)(cca_token_buf +
				attest_data->token_sign_ctx.copied_len),
		     length);

	attest_token_len -= length;

	if (attest_token_len != 0UL) {
		attest_data->token_sign_ctx.cca_token_len = attest_token_len;
		attest_data->token_sign_ctx.copied_len += length;

		res->smc_res.x[0] = RSI_INCOMPLETE;
	} else {

		/* The signing has succeeded. Reset the state. */
		attest_data->token_sign_ctx.state = ATTEST_SIGN_NOT_STARTED;
		res->smc_res.x[0] = RSI_SUCCESS;
	}

	res->smc_res.x[1] = length;

out_unmap:
	/* Unmap realm granule */
	buffer_unmap((void *)realm_att_token);

	/* Unlock last level page table (walk_res.g_llt) */
	granule_unlock(walk_res.llt);
}

void handle_rsi_attest_token_init(struct rec *rec, struct rsi_result *res)
{
	struct rd *rd;
	struct rec_attest_data *attest_data;
	void *rpv_ptr;
	size_t rpv_len;
	int att_ret;

	assert(rec != NULL);

	attest_data = rec->aux_data.attest_data;
	res->action = UPDATE_REC_RETURN_TO_REALM;

	/*
	 * Calling RSI_ATTESTATION_TOKEN_INIT any time aborts any ongoing
	 * operation.
	 * TODO: This can be moved to attestation lib
	 */
	if (attest_data->token_sign_ctx.state != ATTEST_SIGN_NOT_STARTED) {
		int restart;

		attest_data->token_sign_ctx.state = ATTEST_SIGN_NOT_STARTED;
		restart = attestation_heap_reinit_pe(rec->aux_data.attest_heap_buf,
							REC_HEAP_SIZE);
		if (restart != 0) {
			/* There is no provision for this failure so panic */
			panic();
		}
	}

	/*
	 * rd lock is acquired so that measurement cannot be updated
	 * simultaneously by another rec
	 */
	granule_lock(rec->realm_info.g_rd, GRANULE_STATE_RD);
	rd = granule_map(rec->realm_info.g_rd, SLOT_RD);
	assert(rd != NULL);

	/* Save challenge value in the context */
	(void)memcpy((void *)attest_data->token_sign_ctx.challenge,
		     (const void *)&rec->regs[1],
		     ATTEST_CHALLENGE_SIZE);

	get_rpv(rd, &rpv_ptr, &rpv_len);
	att_ret = attest_realm_token_create(rd->algorithm, rd->measurement,
					    MEASUREMENT_SLOT_NR,
					    rpv_ptr,
					    rpv_len,
					    &attest_data->token_sign_ctx,
					    attest_data->rmm_realm_token_buf,
					    sizeof(attest_data->rmm_realm_token_buf));
	buffer_unmap(rd);
	granule_unlock(rec->realm_info.g_rd);

	if (att_ret != 0) {
		ERROR("FATAL_ERROR: Realm token creation failed\n");
		panic();
	}

	attest_data->token_sign_ctx.copied_len = 0UL;
	attest_data->token_sign_ctx.state = ATTEST_SIGN_IN_PROGRESS;

	res->smc_res.x[0] = RSI_SUCCESS;
}

/*
 * Return 'false' if no IRQ is pending,
 * return 'true' if there is an IRQ pending, and need to return to Host.
 */
static bool check_pending_irq(void)
{
	return (read_isr_el1() != 0UL);
}

void handle_rsi_attest_token_continue(struct rec *rec,
				      struct rmi_rec_exit *rec_exit,
				      struct rsi_result *res)
{
	struct rec_attest_data *attest_data;
	unsigned long realm_buf_ipa, offset, size;

	assert(rec != NULL);
	assert(rec_exit != NULL);

	attest_data = rec->aux_data.attest_data;
	res->action = UPDATE_REC_RETURN_TO_REALM;

	realm_buf_ipa = rec->regs[1];
	offset = rec->regs[2];
	size = rec->regs[3];

	if (!GRANULE_ALIGNED(realm_buf_ipa) ||
	    (offset >= GRANULE_SIZE) ||
	   ((offset + size) > GRANULE_SIZE) ||
	   ((offset + size) < offset)) {
		res->smc_res.x[0] = RSI_ERROR_INPUT;
		return;
	}

	if (!addr_in_rec_par(rec, realm_buf_ipa)) {
		res->smc_res.x[0] = RSI_ERROR_INPUT;
		return;
	}

	if (attest_data->token_sign_ctx.state == ATTEST_SIGN_NOT_STARTED) {
		/*
		 * Before this call the initial attestation token call
		 * (SMC_RSI_ATTEST_TOKEN_INIT) must have been executed
		 * successfully.
		 */
		res->smc_res.x[0] = RSI_ERROR_STATE;
		return;
	}

	while (attest_data->token_sign_ctx.state == ATTEST_SIGN_IN_PROGRESS) {
		attest_token_continue_sign_state(attest_data, res);
		if (check_pending_irq()) {
			res->action = UPDATE_REC_EXIT_TO_HOST;
			rec_exit->exit_reason = RMI_EXIT_IRQ;
			return;
		}
	}

	/* Any other state is considered an error */
	assert(attest_data->token_sign_ctx.state ==
					ATTEST_SIGN_TOKEN_WRITE_IN_PROGRESS);

	attest_token_continue_write_state(rec, res);
}

void handle_rsi_measurement_extend(struct rec *rec, struct rsi_result *res)
{
	struct granule *g_rd;
	struct rd *rd;
	unsigned long index;
	unsigned long rd_addr;
	size_t size;
	void *extend_measurement;
	unsigned char *current_measurement;
	int __unused meas_ret;

	assert(rec != NULL);

	res->action = UPDATE_REC_RETURN_TO_REALM;

	/*
	 * rd lock is acquired so that measurement cannot be updated
	 * simultaneously by another rec
	 */
	rd_addr = granule_addr(rec->realm_info.g_rd);
	g_rd = find_lock_granule(rd_addr, GRANULE_STATE_RD);

	assert(g_rd != NULL);

	rd = granule_map(rec->realm_info.g_rd, SLOT_RD);
	assert(rd != NULL);

	/*
	 * X1:     index
	 * X2:     size
	 * X3-X10: measurement value
	 */
	index = rec->regs[1];

	if ((index == RIM_MEASUREMENT_SLOT) ||
	    (index >= MEASUREMENT_SLOT_NR)) {
		res->smc_res.x[0] = RSI_ERROR_INPUT;
		goto out_unmap_rd;
	}

	size  = rec->regs[2];

	if (size > MAX_EXTENDED_SIZE) {
		res->smc_res.x[0] = RSI_ERROR_INPUT;
		goto out_unmap_rd;
	}

	extend_measurement = &rec->regs[3];
	current_measurement = rd->measurement[index];

	measurement_extend(rd->algorithm,
			   current_measurement,
			   extend_measurement,
			   size,
			   current_measurement);

	res->smc_res.x[0] = RSI_SUCCESS;

out_unmap_rd:
	buffer_unmap(rd);
	granule_unlock(g_rd);
}

void handle_rsi_measurement_read(struct rec *rec, struct rsi_result *res)
{
	struct rd *rd;
	unsigned long idx;
	unsigned int i, cnt;
	unsigned long *measurement_value_part;

	assert(rec != NULL);

	res->action = UPDATE_REC_RETURN_TO_REALM;

	/* X1: Index */
	idx = rec->regs[1];

	if (idx >= MEASUREMENT_SLOT_NR) {
		res->smc_res.x[0] = RSI_ERROR_INPUT;
		return;
	}

	/*
	 * rd lock is acquired so that measurement cannot be updated
	 * simultaneously by another rec
	 */
	granule_lock(rec->realm_info.g_rd, GRANULE_STATE_RD);
	rd = granule_map(rec->realm_info.g_rd, SLOT_RD);
	assert(rd != NULL);

	/* Number of 8-bytes words in measurement */
	cnt = (unsigned int)(measurement_get_size(rd->algorithm) /
						sizeof(unsigned long));

	assert(cnt >= (SMC_RESULT_REGS - 1U));
	assert(cnt < ARRAY_LEN(rec->regs));

	/* Copy the part of the measurement to res->smc_res.x[] */
	for (i = 0U; i < (SMC_RESULT_REGS - 1U); i++) {
		measurement_value_part = (unsigned long *)
			&(rd->measurement[idx][i * sizeof(unsigned long)]);
		res->smc_res.x[i + 1U] = *measurement_value_part;
	}

	/* Copy the rest of the measurement to the rec->regs[] */
	for (; i < cnt; i++) {
		measurement_value_part = (unsigned long *)
			&(rd->measurement[idx][i * sizeof(unsigned long)]);
		rec->regs[i + 1U] = *measurement_value_part;
	}

	/* Zero-initialize unused area */
	for (; i < MAX_MEASUREMENT_WORDS; i++) {
		rec->regs[i + 1U] = 0UL;
	}

	buffer_unmap(rd);
	granule_unlock(rec->realm_info.g_rd);

	res->smc_res.x[0] = RSI_SUCCESS;
}
