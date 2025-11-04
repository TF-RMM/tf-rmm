/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <assert.h>
#include <debug.h>
#include <errno.h>
#include <rmm_el3_ifc.h>

/* cppcheck-suppress misra-c2012-8.7 */
int rmm_el3_ifc_rp_ide_key_prog(unsigned long ecam_addr, unsigned long rp_id,
				unsigned long stream_info, struct el3_ifc_rp_ide_key *key,
				struct el3_ifc_rp_ide_iv *iv)
{
	int rc;
	struct smc_args args;
	struct smc_result res;

	args = SMC_ARGS_9(
		ecam_addr,
		rp_id,
		stream_info,
		key->kq_w0,
		key->kq_w1,
		key->kq_w2,
		key->kq_w3,
		iv->iq_w0,
		iv->iq_w1
	);

	monitor_call_with_arg_res(SMC_RMM_RP_IDE_KEY_PROG, &args, &res);
	/* coverity[uninit_use:SUPPRESS] */
	rc = (int)res.x[0];
	if ((rc == E_RMM_OK) || (rc == E_RMM_FAULT) || (rc == E_RMM_INVAL) ||
	    (rc == E_RMM_AGAIN) || (rc == E_RMM_IN_PROGRESS)) {
		return rc;
	}

	return E_RMM_UNK;
}

/* cppcheck-suppress misra-c2012-8.7 */
int rmm_el3_ifc_rp_ide_key_set_go(unsigned long ecam_addr, unsigned long rp_id,
				  unsigned long stream_info)
{
	int rc;

	rc = (int)monitor_call(SMC_RMM_RP_IDE_KEY_SET_GO, ecam_addr, rp_id,
			       stream_info, 0UL, 0UL, 0UL);
	if ((rc == E_RMM_OK) || (rc == E_RMM_FAULT) || (rc == E_RMM_INVAL) ||
	    (rc == E_RMM_AGAIN) || (rc == E_RMM_IN_PROGRESS)) {
		return rc;
	}

	return E_RMM_UNK;
}

/* cppcheck-suppress misra-c2012-8.7 */
int rmm_el3_ifc_rp_ide_key_set_stop(unsigned long ecam_addr, unsigned long rp_id,
				    unsigned long stream_info)
{
	int rc;

	rc = (int)monitor_call(SMC_RMM_RP_IDE_KEY_SET_STOP, ecam_addr, rp_id,
			       stream_info, 0UL, 0UL, 0UL);
	if ((rc == E_RMM_OK) || (rc == E_RMM_FAULT) || (rc == E_RMM_INVAL) ||
	    (rc == E_RMM_AGAIN) || (rc == E_RMM_IN_PROGRESS)) {
		return rc;
	}

	return E_RMM_UNK;
}
