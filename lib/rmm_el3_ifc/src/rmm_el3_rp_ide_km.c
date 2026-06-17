/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <assert.h>
#include <debug.h>
#include <errno.h>
#include <firme.h>
#include <rmm_el3_ifc.h>

static int el3_ifc_rp_ide_key_prog(unsigned long ecam_addr, unsigned long rp_id,
				   unsigned long kslot, unsigned long kdir,
				   unsigned long ide_sub_sid,
				   unsigned long ide_sid,
				   struct el3_ifc_rp_ide_key *key,
				   struct el3_ifc_rp_ide_iv *iv)
{
	int rc;
	struct smc_args args;
	struct smc_result res;
	unsigned long stream_info;

	stream_info = EL3_IFC_IDE_MAKE_STREAM_INFO((uint8_t)kslot, (uint8_t)kdir,
						   (uint8_t)ide_sub_sid,
						   (uint8_t)ide_sid);

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

	return rc;
}

static int firme_rp_ide_key_prog(unsigned long ecam_addr, unsigned long rp_id,
				 unsigned long kslot, unsigned long kdir,
				 unsigned long ide_sub_sid,
				 unsigned long ide_sid,
				 struct el3_ifc_rp_ide_key *key)
{
	uint64_t firme_rc;
	struct smc_args args;
	struct smc_result res;
	unsigned long keyset_id;

	keyset_id = FIRME_IDE_MAKE_KEYSET_ID((uint8_t)kslot, (uint8_t)kdir,
					     (uint8_t)ide_sub_sid,
					     (uint8_t)ide_sid, (uint8_t)
					     (uint16_t)rp_id, (uint8_t)0);

	args = SMC_ARGS_8(ecam_addr, 0, keyset_id, key->kq_w0, key->kq_w1,
			  key->kq_w2, key->kq_w3, 0UL);

	monitor_call_with_arg_res(SMC_FIRME_IDE_KEYSET_PROG, &args, &res);
	/* coverity[uninit_use:SUPPRESS] */
	firme_rc = res.x[0];

	return firme_errno_to_rmm_errno(firme_rc);
}

static int el3_ifc_rp_ide_key_go(unsigned long ecam_addr, unsigned long rp_id,
				 unsigned long kslot, unsigned long kdir,
				 unsigned long ide_sub_sid,
				 unsigned long ide_sid)
{
	unsigned long stream_info;
	int rc;

	stream_info = EL3_IFC_IDE_MAKE_STREAM_INFO((uint8_t)kslot, (uint8_t)kdir,
						   (uint8_t)ide_sub_sid,
						   (uint8_t)ide_sid);

	rc = (int)monitor_call(SMC_RMM_RP_IDE_KEY_SET_GO, ecam_addr, rp_id,
			       stream_info, 0UL, 0UL, 0UL);

	return rc;
}

static int firme_rp_ide_key_go(unsigned long ecam_addr, unsigned long rp_id,
			       unsigned long kslot, unsigned long kdir,
			       unsigned long ide_sub_sid,
			       unsigned long ide_sid)
{
	unsigned long keyset_id;
	uint64_t firme_rc;

	keyset_id = FIRME_IDE_MAKE_KEYSET_ID((uint8_t)kslot, (uint8_t)kdir,
					     (uint8_t)ide_sub_sid,
					     (uint8_t)ide_sid, (uint8_t)
					     (uint16_t)rp_id, (uint8_t)0);

	firme_rc = monitor_call(SMC_FIRME_IDE_KEYSET_GO, ecam_addr, 0,
				keyset_id, 0UL, 0UL, 0UL);

	return firme_errno_to_rmm_errno(firme_rc);
}

static int el3_ifc_rp_ide_key_stop(unsigned long ecam_addr, unsigned long rp_id,
				   unsigned long kslot, unsigned long kdir,
				   unsigned long ide_sub_sid,
				   unsigned long ide_sid)
{
	unsigned long stream_info;
	int rc;

	stream_info = EL3_IFC_IDE_MAKE_STREAM_INFO((uint8_t)kslot, (uint8_t)kdir,
						   (uint8_t)ide_sub_sid,
						   (uint8_t)ide_sid);

	rc = (int)monitor_call(SMC_RMM_RP_IDE_KEY_SET_STOP, ecam_addr, rp_id,
			       stream_info, 0UL, 0UL, 0UL);

	return rc;
}

static int firme_rp_ide_key_stop(unsigned long ecam_addr, unsigned long rp_id,
				 unsigned long kslot, unsigned long kdir,
				 unsigned long ide_sub_sid,
				 unsigned long ide_sid)
{
	unsigned long keyset_id;
	uint64_t firme_rc;

	keyset_id = FIRME_IDE_MAKE_KEYSET_ID((uint8_t)kslot, (uint8_t)kdir,
					     (uint8_t)ide_sub_sid,
					     (uint8_t)ide_sid, (uint8_t)
					     (uint16_t)rp_id, (uint8_t)0);

	firme_rc = monitor_call(SMC_FIRME_IDE_KEYSET_STOP, ecam_addr, 0,
				keyset_id, 0UL, 0UL, 0UL);

	return firme_errno_to_rmm_errno(firme_rc);
}

/* cppcheck-suppress misra-c2012-8.7 */
int rmm_el3_ifc_rp_ide_key_prog(unsigned long ecam_addr, unsigned long rp_id,
				unsigned long kslot, unsigned long kdir,
				unsigned long ide_sub_sid,
				unsigned long ide_sid,
				struct el3_ifc_rp_ide_key *key,
				struct el3_ifc_rp_ide_iv *iv)
{
	int rc;

	if (firme_supports_ide_service()) {
		rc = firme_rp_ide_key_prog(ecam_addr, rp_id, kslot, kdir,
					   ide_sub_sid, ide_sid, key);

		if ((rc == E_RMM_OK) || (rc == E_RMM_INVAL) ||
		    (rc == E_RMM_NOTSUP) || (rc == E_RMM_BUSY)) {
			return rc;
		}
	} else {
		rc = el3_ifc_rp_ide_key_prog(ecam_addr, rp_id, kslot, kdir,
					     ide_sub_sid, ide_sid, key, iv);

		/*
		 * Convert E_RMM_AGAIN to E_RMM_BUSY for legacy SMC IDE KM
		 * interface to have unified error handling by the caller.
		 */
		if (rc == E_RMM_AGAIN) {
			rc = E_RMM_BUSY;
		}

		if ((rc == E_RMM_OK) || (rc == E_RMM_FAULT) ||
		    (rc == E_RMM_INVAL) || (rc == E_RMM_BUSY) ||
		    (rc == E_RMM_IN_PROGRESS)) {
			return rc;
		}
	}

	return E_RMM_UNK;
}

/* cppcheck-suppress misra-c2012-8.7 */
int rmm_el3_ifc_rp_ide_key_set_go(unsigned long ecam_addr, unsigned long rp_id,
				  unsigned long kslot, unsigned long kdir,
				  unsigned long ide_sub_sid,
				  unsigned long ide_sid)
{
	int rc;

	if (firme_supports_ide_service()) {
		rc = firme_rp_ide_key_go(ecam_addr, rp_id, kslot, kdir,
					 ide_sub_sid, ide_sid);

		if ((rc == E_RMM_OK) || (rc == E_RMM_INVAL) ||
		    (rc == E_RMM_NOTSUP) || (rc == E_RMM_BUSY) ||
		    (rc == E_RMM_DENIED)) {
			return rc;
		}
	} else {
		rc = el3_ifc_rp_ide_key_go(ecam_addr, rp_id, kslot, kdir,
					   ide_sub_sid, ide_sid);

		/*
		 * Convert E_RMM_AGAIN to E_RMM_BUSY for legacy SMC IDE KM
		 * interface to have unified error handling by the caller.
		 */
		if (rc == E_RMM_AGAIN) {
			rc = E_RMM_BUSY;
		}

		if ((rc == E_RMM_OK) || (rc == E_RMM_FAULT) ||
		    (rc == E_RMM_INVAL) || (rc == E_RMM_BUSY) ||
		    (rc == E_RMM_IN_PROGRESS)) {
			return rc;
		}
	}

	return E_RMM_UNK;
}

/* cppcheck-suppress misra-c2012-8.7 */
int rmm_el3_ifc_rp_ide_key_set_stop(unsigned long ecam_addr, unsigned long rp_id,
				    unsigned long kslot, unsigned long kdir,
				    unsigned long ide_sub_sid,
				    unsigned long ide_sid)
{
	int rc;

	if (firme_supports_ide_service()) {
		rc = firme_rp_ide_key_stop(ecam_addr, rp_id, kslot, kdir,
					   ide_sub_sid, ide_sid);

		if ((rc == E_RMM_OK) || (rc == E_RMM_INVAL) ||
		    (rc == E_RMM_NOTSUP) || (rc == E_RMM_BUSY) ||
		    (rc == E_RMM_DENIED)) {
			return rc;
		}
	} else {
		rc = el3_ifc_rp_ide_key_stop(ecam_addr, rp_id, kslot, kdir,
					     ide_sub_sid, ide_sid);

		/*
		 * Convert E_RMM_AGAIN to E_RMM_BUSY for legacy SMC IDE KM
		 * interface to have unified error handling by the caller.
		 */
		if (rc == E_RMM_AGAIN) {
			rc = E_RMM_BUSY;
		}

		if ((rc == E_RMM_OK) || (rc == E_RMM_FAULT) ||
		    (rc == E_RMM_INVAL) || (rc == E_RMM_BUSY) ||
		    (rc == E_RMM_IN_PROGRESS)) {
			return rc;
		}
	}

	return E_RMM_UNK;
}
