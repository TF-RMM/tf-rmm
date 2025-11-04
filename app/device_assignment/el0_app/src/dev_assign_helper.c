/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <assert.h>
#include <debug.h>
#include <dev_assign_helper.h>
#include <stdbool.h>
/*
 * Compute hash using PSA helpers. This helper is used by DA ABIs to
 * incrementally compute hash as device response is processed by RMM.
 *
 * TODO: make arguments generic so that this function is independent of crypto
 * library used. Currently it is PSA Crypto.
 *
 * In:
 *	algo		- The hash algorithm to compute
 *	op		- Hash state data structure
 *	op_flags	- Hash operations to perform SETUP|UPDATE|FINISH
 *	src		- Source buffer containing the message to hash.
 *	src_len		- Length of 'src' buffer
 *	hash_size	- Size of the hash buffer in bytes.
 * Out:
 *	op		- Holds the updated hash state
 *	hash		- Buffer where the hash is to be written.
 *	hash_length	- Hash length set when op_flags has FINISH
 */
/* cppcheck-suppress misra-c2012-8.7 */
int dev_assign_hash_extend(psa_algorithm_t algo, psa_hash_operation_t *op,
			uint8_t op_flags, const uint8_t *src,
			size_t src_length, uint8_t *hash, size_t hash_size,
			size_t *hash_length)
{
	psa_status_t psa_rc;
	int rc = -1;

	/* Make sure that only valid flags are passed */
	if ((op_flags & (~HASH_OP_VALID_FLAGS)) != 0U) {
		ERROR("%s called with invalid flag(s) %x\n", __func__, op_flags);
		goto out_err;
	}

	/* Make sure that no invalid flag combination is passed */
	if (op_flags == (HASH_OP_FLAG_SETUP | HASH_OP_FLAG_FINISH)) {
		ERROR("%s called with incompatible flag(s) %x\n", __func__, op_flags);
		goto out_err;
	}

	if ((op_flags & HASH_OP_FLAG_SETUP) != 0U) {
		psa_rc = psa_hash_setup(op, algo);
		if (psa_rc != PSA_SUCCESS) {
			ERROR("%s: psa_hash_setup failed: %d\n", __func__, psa_rc);
			goto out_psa_err;
		}
	}
	if ((op_flags & HASH_OP_FLAG_UPDATE) != 0U) {
		psa_rc = psa_hash_update(op, src, src_length);
		if (psa_rc != PSA_SUCCESS) {
			ERROR("%s: psa_hash_update failed: %d\n", __func__, psa_rc);
			goto out_psa_err;
		}
	}
	if ((op_flags & HASH_OP_FLAG_FINISH) != 0U) {
		psa_rc = psa_hash_finish(op, hash, hash_size, hash_length);
		if (psa_rc != PSA_SUCCESS) {
			ERROR("%s: psa_hash_finish failed: %d\n", __func__, psa_rc);
			goto out_psa_err;
		}
	}
	rc = 0;
out_psa_err:
	if (rc == -1) {
		(void)psa_hash_abort(op);
	}
out_err:
	return rc;
}
