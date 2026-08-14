/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef STATUS_H
#define STATUS_H

#include <assert.h>
#include <smc-rmi.h>

/* Logical representation of RmiResultDataIncomplete. */
struct rmi_result_data_incomplete {
	unsigned char mem;	/* 2-bit RmiOpMemReq field */
	unsigned char cancel;	/* 1-bit RmiOpCanCancel field */
};

/* Logical representation of RmiResultDataLevel. */
struct rmi_result_data_level {
	unsigned char level;	/* 8-bit level field */
};

/*
 * Logical representation of an RmiResult.
 *
 * The status is the discriminator for @data. RMI_INCOMPLETE selects
 * @incomplete, while RMI_ERROR_DPT, RMI_ERROR_RTT, RMI_ERROR_RTT_AUX and
 * RMI_ERROR_PSMMU_ST select @level. For all other status values the data is
 * RmiResultDataNull and no union member is active.
 *
 * This is not the RMI wire representation. Use the packing helpers below to
 * encode it into the 64-bit value returned in x0.
 */
typedef struct {
	unsigned char status;	/* 8-bit RmiStatusCode field */
	union {
		struct rmi_result_data_incomplete incomplete;
		struct rmi_result_data_level level;
	} data;
} return_code_t;

/*
 * Convenience function for creating a return_code_t with null data.
 */
static inline return_code_t make_return_code(unsigned int status)
{
	return_code_t return_code = { 0, { { 0, 0 } } };

	return_code.status = (unsigned char)status;
	return return_code;
}

static inline return_code_t make_return_code_level(unsigned int status,
						   unsigned char level)
{
	return_code_t return_code = make_return_code(status);

	assert((status == RMI_ERROR_DPT) ||
	       (status == RMI_ERROR_RTT) ||
	       (status == RMI_ERROR_RTT_AUX) ||
	       (status == RMI_ERROR_PSMMU_ST));

	return_code.data.level.level = level;
	return return_code;
}

static inline return_code_t make_return_code_incomplete(unsigned long mem,
							unsigned long cancel)
{
	return_code_t return_code = make_return_code(RMI_INCOMPLETE);

	assert(mem <= RMI_OP_MEM_REQ_RECLAIM);
	assert(cancel <= RMI_OP_CAN_CANCEL);

	return_code.data.incomplete.mem = (unsigned char)mem;
	return_code.data.incomplete.cancel = (unsigned char)cancel;
	return return_code;
}

/*
 * Pack a return_code_t into a binary format, suitable for storing in a
 * register before exit from the RMM.
 */
static inline unsigned long pack_struct_return_code(return_code_t return_code)
{
	unsigned long result = INPLACE(RMI_RESULT_STATUS, return_code.status);

	assert(return_code.status < RMI_ERROR_COUNT_MAX);

	switch ((unsigned int)return_code.status) {
	case RMI_INCOMPLETE:
		assert(return_code.data.incomplete.mem <=
		       RMI_OP_MEM_REQ_RECLAIM);
		assert(return_code.data.incomplete.cancel <= RMI_OP_CAN_CANCEL);

		result |= INPLACE(RMI_OP_MEM_REQ,
				  return_code.data.incomplete.mem);
		result |= INPLACE(RMI_OP_CAN_CANCEL_BIT,
				  return_code.data.incomplete.cancel);
		break;
	case RMI_ERROR_DPT:
	case RMI_ERROR_RTT:
	case RMI_ERROR_RTT_AUX:
	case RMI_ERROR_PSMMU_ST:
		result |= INPLACE(RMI_RESULT_LEVEL, return_code.data.level.level);
		break;
	default:
		/* RmiResultDataNull is MBZ. */
		break;
	}

	return result;
}

/*
 * Pack RmiResultDataLevel into the binary RmiResult representation.
 */
static inline unsigned long pack_return_code_level(unsigned int status,
						   unsigned char level)
{
	return pack_struct_return_code(make_return_code_level(status, level));
}

/*
 * Pack RmiResultDataIncomplete into the binary RmiResult representation.
 */
static inline unsigned long pack_return_code_incomplete(unsigned long mem,
							unsigned long cancel)
{
	return pack_struct_return_code(
			make_return_code_incomplete(mem, cancel));
}

/*
 * Unpacks a return code.
 */
static inline return_code_t unpack_return_code(unsigned long error_code)
{
	unsigned int status =
		(unsigned int)EXTRACT(RMI_RESULT_STATUS, error_code);
	return_code_t return_code = make_return_code(status);

	switch (status) {
	case RMI_INCOMPLETE:
		return_code.data.incomplete.mem =
			(unsigned char)EXTRACT(RMI_OP_MEM_REQ, error_code);
		return_code.data.incomplete.cancel =
			(unsigned char)EXTRACT(RMI_OP_CAN_CANCEL_BIT, error_code);
		break;
	case RMI_ERROR_DPT:
	case RMI_ERROR_RTT:
	case RMI_ERROR_RTT_AUX:
	case RMI_ERROR_PSMMU_ST:
		return_code.data.level.level =
			(unsigned char)EXTRACT(RMI_RESULT_LEVEL, error_code);
		break;
	default:
		/* RmiResultDataNull has no fields to decode. */
		break;
	}

	return return_code;
}

#define MAX_ERR 4095

#endif /* STATUS_H */
