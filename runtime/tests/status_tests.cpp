/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <CppUTest/TestHarness.h>

extern "C" {
#include <status.h>
}

TEST_GROUP(status_tests) {
};

TEST(status_tests, null_data_is_mbz)
{
	return_code_t result = make_return_code(RMI_ERROR_INPUT);
	unsigned long encoded = pack_struct_return_code(result);
	return_code_t decoded = unpack_return_code(encoded);

	UNSIGNED_LONGS_EQUAL(RMI_ERROR_INPUT, encoded);
	CHECK_EQUAL(RMI_ERROR_INPUT, decoded.status);
}

TEST(status_tests, level_round_trip)
{
	const unsigned int statuses[] = {
		RMI_ERROR_RTT,
		RMI_ERROR_RTT_AUX,
		RMI_ERROR_PSMMU_ST
	};
	const unsigned char level = 0xABU;

	for (unsigned int status : statuses) {
		unsigned long encoded = pack_return_code_level(status, level);
		return_code_t decoded = unpack_return_code(encoded);

		UNSIGNED_LONGS_EQUAL(status |
				     INPLACE(RMI_RESULT_LEVEL, level),
				     encoded);
		CHECK_EQUAL(status, decoded.status);
		CHECK_EQUAL(level, decoded.data.level.level);
	}
}

TEST(status_tests, level_addr_round_trip)
{
	const unsigned int statuses[] = {
		RMI_ERROR_DPT,
		RMI_ERROR_GPT,
		RMI_ERROR_TRACKING
	};
	const unsigned char level = 0xABU;
	const unsigned long addr = UL(0x123456789) << GRANULE_SHIFT;

	for (unsigned int status : statuses) {
		unsigned long encoded =
			pack_return_code_level_addr(status, level, addr);
		return_code_t decoded = unpack_return_code(encoded);

		UNSIGNED_LONGS_EQUAL(
			status |
			INPLACE(RMI_RESULT_LEVEL, level) |
			INPLACE(RMI_RESULT_ADDR, addr >> GRANULE_SHIFT),
			encoded);
		CHECK_EQUAL(status, decoded.status);
		CHECK_EQUAL(level, decoded.data.level_addr.level);
		UNSIGNED_LONGS_EQUAL(addr, decoded.data.level_addr.addr);
	}
}

TEST(status_tests, incomplete_round_trip)
{
	for (unsigned int mem = RMI_OP_MEM_REQ_NONE;
	     mem <= RMI_OP_MEM_REQ_RECLAIM; ++mem) {
		for (unsigned int cancel = RMI_OP_CANNOT_CANCEL;
		     cancel <= RMI_OP_CAN_CANCEL; ++cancel) {
			unsigned long encoded =
				pack_return_code_incomplete(mem, cancel);
			return_code_t decoded = unpack_return_code(encoded);

			UNSIGNED_LONGS_EQUAL(
				RMI_INCOMPLETE |
				INPLACE(RMI_OP_MEM_REQ, mem) |
				INPLACE(RMI_OP_CAN_CANCEL_BIT, cancel),
				encoded);
			CHECK_EQUAL(RMI_INCOMPLETE, decoded.status);
			CHECK_EQUAL(mem, decoded.data.incomplete.mem);
			CHECK_EQUAL(cancel, decoded.data.incomplete.cancel);
		}
	}
}
