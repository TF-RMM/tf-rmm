/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef DEV_ASSIGN_HELPER_H
#define DEV_ASSIGN_HELPER_H

#include <psa/crypto.h>

#define HASH_OP_FLAG_SETUP		0x1U
#define HASH_OP_FLAG_UPDATE		0x2U
#define HASH_OP_FLAG_FINISH		0x4U

#define HASH_OP_VALID_FLAGS		(HASH_OP_FLAG_SETUP	| \
					 HASH_OP_FLAG_UPDATE	| \
					 HASH_OP_FLAG_FINISH)


/*
 * Extend a hash with algorithm 'hash_algo' and with hash 'op'
 *
 *	algo		- The hash algorithm to compute
 *	op		- Hash state data structure
 *	op_flags	- Hash operations to perform SETUP|UPDATE|FINISH
 *	src		- Source buffer containing the message to hash.
 *	src_len		- Length of 'src' buffer
 *	hash_size	- Size of the hash buffer in bytes.
 */
int dev_assign_hash_extend(psa_algorithm_t algo, psa_hash_operation_t *op,
			uint8_t op_flags, const uint8_t *src,
			size_t src_length, uint8_t *hash, size_t hash_size,
			size_t *hash_length);

#endif /* DEV_ASSIGN_HELPER_H */
