/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <buffer.h>
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
	enum attest_token_err_t ret;

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

	/* If size of buffer is 0, then return early. */
	if (size == 0UL) {
		res->smc_res.x[0] = RSI_INCOMPLETE;
		goto out_unlock;
	}

	/* Map realm data granule to RMM address space */
	gr = find_granule(walk_res.pa);
	realm_att_token = (uintptr_t)buffer_granule_map(gr, SLOT_REALM);
	assert(realm_att_token != 0UL);

	if (attest_data->rmm_cca_token_copied_len == 0UL) {
		ret = attest_cca_token_create(
				&rec->attest_app_data,
				&attest_token_len);

		if (ret != ATTEST_TOKEN_ERR_SUCCESS) {
			res->smc_res.x[0] = RSI_ERROR_INPUT;
			goto out_unmap;
		}

		attest_data->rmm_cca_token_len = attest_token_len;
	} else {
		attest_token_len = attest_data->rmm_cca_token_len;
	}

	length = (size < attest_token_len) ? size : attest_token_len;

	/* Copy attestation token */
	struct attest_heap_shared *heap_shared = app_get_heap_ptr(&rec->attest_app_data);
	(void)memcpy((void *)(realm_att_token + offset),
		     (void *)(&heap_shared->cca_attest_token_buf[
				attest_data->rmm_cca_token_copied_len]),
		     length);

	attest_token_len -= length;

	if (attest_token_len != 0UL) {
		attest_data->rmm_cca_token_len = attest_token_len;
		attest_data->rmm_cca_token_copied_len += length;

		res->smc_res.x[0] = RSI_INCOMPLETE;
	} else {
		res->smc_res.x[0] = RSI_SUCCESS;
		/* Token creation is complete, reset realm token length */
		attest_data->rmm_realm_token_len = 0;
	}

	res->smc_res.x[1] = length;

out_unmap:
	/* Unmap realm granule */
	buffer_unmap((void *)realm_att_token);
out_unlock:
	/* Unlock last level page table (walk_res.g_llt) */
	granule_unlock(walk_res.llt);
}

void handle_rsi_attest_token_init(struct rec *rec, struct rsi_result *res)
{
	struct rd *rd;
	struct rec_attest_data *attest_data;
	enum attest_token_err_t ret;

	assert(rec != NULL);

	attest_data = rec->aux_data.attest_data;
	res->action = UPDATE_REC_RETURN_TO_REALM;

	/* Initialize length fields in attestation data */
	attest_data->rmm_realm_token_len = 0;
	attest_data->rmm_cca_token_copied_len = 0;
	attest_data->rmm_cca_token_len = 0;

	/*
	 * Calling RSI_ATTESTATION_TOKEN_INIT any time aborts any ongoing
	 * operation.
	 */
	ret = attest_token_sign_ctx_init(&rec->attest_app_data,
						granule_addr(rec->g_rec));
	if (ret != ATTEST_TOKEN_ERR_SUCCESS) {
		ERROR("Failed to initialize attestation token context.\n");
		res->smc_res.x[0] = RSI_ERROR_UNKNOWN;
		return;
	}

	/*
	 * rd lock is acquired so that measurement cannot be updated
	 * simultaneously by another rec
	 */
	granule_lock(rec->realm_info.g_rd, GRANULE_STATE_RD);
	rd = buffer_granule_map(rec->realm_info.g_rd, SLOT_RD);
	assert(rd != NULL);

	ret = attest_realm_token_create(&rec->attest_app_data,
			     rd->algorithm, rd->measurement,
			     &(rd->rpv[0]),
			     (const void *)&rec->regs[1]);
	buffer_unmap(rd);
	granule_unlock(rec->realm_info.g_rd);

	if (ret != ATTEST_TOKEN_ERR_SUCCESS) {
		ERROR("Realm token creation failed.\n");
		res->smc_res.x[0] = RSI_ERROR_UNKNOWN;
		return;
	}

	res->smc_res.x[0] = RSI_SUCCESS;
	res->smc_res.x[1] = ATTEST_TOKEN_BUF_SIZE;
}

/*
 * Return 'false' if no IRQ is pending,
 * return 'true' if there is an IRQ pending, and need to return to Host.
 */
static bool check_pending_irq(void)
{
	return (read_isr_el1() != 0UL);
}

static __unused int write_response_to_rec(struct rec *curr_rec,
				uintptr_t resp_granule)
{
	struct granule *rec_granule = NULL;
	struct rec *rec = NULL;
	struct app_data_cfg *attest_app_data;
	bool unmap_unlock_needed = false;
	int ret = 0;

	/*
	 * Check if the granule is the same as the current REC. If it is, the current
	 * code path is guaranteed to have a reference on the REC and the REC
	 * cannot be deleted. It also means that the REC is mapped at the usual
	 * SLOT_REC, so we can avoid locking and mapping the REC and the AUX
	 * granules.
	 */
	if (resp_granule != granule_addr(curr_rec->g_rec)) {

		rec_granule = find_lock_granule(
				resp_granule, GRANULE_STATE_REC);
		if (rec_granule == NULL) {
			/*
			 * REC must have been destroyed, drop the response.
			 */
			VERBOSE("REC granule %lx not found\n", resp_granule);
			return 0;
		}

		rec = buffer_granule_map(rec_granule, SLOT_EL3_TOKEN_SIGN_REC);
		assert(rec != NULL);

		unmap_unlock_needed = true;
	} else {
		rec = curr_rec;
	}
	attest_app_data = &(rec->attest_app_data);

	if (attest_el3_token_write_response_to_ctx(attest_app_data, resp_granule) != 0) {
		ret = -EPERM;
	}

	if (unmap_unlock_needed) {
		buffer_unmap(rec);
		granule_unlock(rec_granule);
	}

	return ret;
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

	/* Sign the token */
	while (attest_data->rmm_realm_token_len == 0U) {
		enum attest_token_err_t ret;

		ret = attest_realm_token_sign(&rec->attest_app_data,
					&(attest_data->rmm_realm_token_len));

		if (ret == ATTEST_TOKEN_ERR_INVALID_STATE) {
			/*
			 * Before this call the initial attestation token call
			 * (SMC_RSI_ATTEST_TOKEN_INIT) must have been executed
			 * successfully.
			 */
			res->smc_res.x[0] = RSI_ERROR_STATE;
			return;
		} else if ((ret != ATTEST_TOKEN_ERR_COSE_SIGN_IN_PROGRESS) &&
			(ret != ATTEST_TOKEN_ERR_SUCCESS)) {
			/* Accessible only in case of failure during token signing */
			ERROR("Realm token signing failed.\n");
			res->smc_res.x[0] = RSI_ERROR_UNKNOWN;
			return;
		}

		res->smc_res.x[0] = RSI_INCOMPLETE;

		/*
		 * Return to RSI handler function after each iteration
		 * to check is there anything else to do (pending IRQ)
		 * or next signing iteration can be executed.
		 */
		if (check_pending_irq()) {
			res->action = UPDATE_REC_EXIT_TO_HOST;
			rec_exit->exit_reason = RMI_EXIT_IRQ;
			return;
		}

#if ATTEST_EL3_TOKEN_SIGN
		/*
		 * Pull response from EL3, find the corresponding rec granule
		 * and attestation context, and have the attestation library
		 * write the response to the context.
		 */
		uintptr_t granule = 0UL;
		int el3_token_sign_ret;

		el3_token_sign_ret = attest_el3_token_sign_pull_response_from_el3(&granule);
		if (el3_token_sign_ret == -EAGAIN) {
			continue;
		}

		if (el3_token_sign_ret != 0) {
			ERROR("Failed to pull response from EL3: %d\n", el3_token_sign_ret);
			res->smc_res.x[0] = RSI_ERROR_UNKNOWN;
			return;
		}

		el3_token_sign_ret = write_response_to_rec(rec, granule);
		if (el3_token_sign_ret != 0) {
			ERROR("Failed to write response to REC: %d\n", el3_token_sign_ret);
			res->smc_res.x[0] = RSI_ERROR_UNKNOWN;
			return;
		}
#endif
		/*
		 * If there are no interrupts pending, then continue to pull
		 * requests from EL3 until this RECs request is done.
		 */
	}

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

	assert(rec != NULL);

	res->action = UPDATE_REC_RETURN_TO_REALM;

	/*
	 * rd lock is acquired so that measurement cannot be updated
	 * simultaneously by another rec
	 */
	rd_addr = granule_addr(rec->realm_info.g_rd);
	g_rd = find_lock_granule(rd_addr, GRANULE_STATE_RD);

	assert(g_rd != NULL);

	rd = buffer_granule_map(rec->realm_info.g_rd, SLOT_RD);
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

	measurement_extend(&rec->attest_app_data,
			   rd->algorithm,
			   current_measurement,
			   extend_measurement,
			   size,
			   current_measurement,
			   MAX_MEASUREMENT_SIZE);

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
	rd = buffer_granule_map(rec->realm_info.g_rd, SLOT_RD);
	assert(rd != NULL);

	/* Number of 8-bytes words in measurement */
	cnt = (unsigned int)(measurement_get_size(rd->algorithm) /
						sizeof(unsigned long));

	assert(cnt >= (SMC_RESULT_REGS - 1U));
	assert(cnt < ARRAY_SIZE(rec->regs));

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
