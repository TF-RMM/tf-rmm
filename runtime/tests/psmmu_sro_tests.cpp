/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <CppUTest/TestHarness.h>

extern "C" {
#include <arch_helpers.h>
#include <debug.h>
#include <granule.h>
#include <host_utils.h>
#include <psmmu.h>
#include <smc-handler.h>
#include <smc-rmi.h>
#include <smc.h>
#include <smmuv3_psmmu.h>
#include <sro_context.h>
#include <status.h>
#include <stdlib.h>
#include <string.h>
#include <test_helpers.h>
#include <utils_def.h>
#include <xlat_defs.h>
}

/*
 * Helper to encode an RmiAddrRangeDesc4KB entry.
 */
static unsigned long encode_addr_desc(uintptr_t base, unsigned long count,
				      unsigned long state)
{
	return INPLACE(RMI_ADDR_RDESC_4K_SZ, RMI_PAGE_L3) |
	       INPLACE(RMI_ADDR_RDESC_4K_CNT, count) |
	       INPLACE(RMI_ADDR_RDESC_4K_ADDR, base >> GRANULE_SHIFT) |
	       INPLACE(RMI_ADDR_RDESC_4K_ST, state);
}

/*
 * Delegate a contiguous range of granules.
 * Returns true on success.
 */
static bool delegate_range(uintptr_t start, uintptr_t end)
{
	struct smc_result res = {};
	uintptr_t cur = start;

	while (cur < end) {
		smc_granule_range_delegate(cur, end, &res);
		if (res.x[0] != RMI_SUCCESS) {
			return false;
		}
		cur = res.x[1];
	}
	return true;
}

/*
 * Get the NS base PA of the first SMMU (used as psmmu_ptr).
 */
static unsigned long get_psmmu_ptr(void)
{
	return host_util_get_smmu_ns_base(0U);
}

/*
 * Helper: perform a full donation phase for smc_psmmu_activate.
 *
 * After calling smc_psmmu_activate, the SRO flow requests multiple
 * memory ranges (L1 ST, CMDQ, EVTQ). This helper drives
 * the entire donation state machine until it reaches MEM_REQ_NONE
 * (ready for OP_CONTINUE).
 *
 * Returns the handle for subsequent OP_CONTINUE or OP_MEM_RECLAIM.
 */
static unsigned long drive_activate_donations(unsigned long psmmu_ptr,
					      uintptr_t ns_buf)
{
	struct smc_result res = {};
	struct psmmu_params params = {};
	unsigned long *addr_list = (unsigned long *)ns_buf;

	/* Write params into an NS granule */
	uintptr_t params_pa = test_helpers_allocate_granules(1U);
	(void)memset((void *)params_pa, 0, GRANULE_SIZE);
	(void)memcpy((void *)params_pa, &params, sizeof(params));

	smc_psmmu_activate(psmmu_ptr, params_pa, &res);

	return_code_t rc = unpack_return_code(res.x[0]);
	CHECK_EQUAL(RMI_INCOMPLETE, rc.status);
	CHECK_EQUAL(RMI_OP_MEM_REQ_DONATE,
		    (unsigned long)EXTRACT(RMI_OP_MEM_REQ, res.x[0]));

	unsigned long handle = res.x[1];
	unsigned long donate_req = res.x[2];

	/* Drive the donation loop until MEM_REQ_NONE */
	while (true) {
		unsigned long mem_req = EXTRACT(RMI_OP_MEM_REQ, res.x[0]);

		if (mem_req == RMI_OP_MEM_REQ_NONE) {
			break;
		}

		CHECK_EQUAL(RMI_OP_MEM_REQ_DONATE, mem_req);

		donate_req = res.x[2];
		unsigned long blk_sz = EXTRACT(RMI_OP_DONATE_BLK_SIZE, donate_req);
		unsigned long blk_count = EXTRACT(RMI_OP_DONATE_BLK_COUNT, donate_req);
		unsigned long contig = EXTRACT(RMI_OP_DONATE_MEM_CONTIG, donate_req);

		unsigned long blk_size_bytes =
			XLAT_BLOCK_SIZE((int)XLAT_TABLE_LEVEL_MAX - (int)blk_sz);
		unsigned long num_granules =
			(blk_count * blk_size_bytes) / GRANULE_SIZE;

		uintptr_t aux_base;
		if (contig == RMI_OP_MEM_CONTIG) {
			aux_base = test_helpers_allocate_granules_aligned(
					(unsigned int)num_granules);
		} else {
			aux_base = test_helpers_allocate_granules(
					(unsigned int)num_granules);
		}
		CHECK_TRUE(delegate_range(aux_base,
					  aux_base + num_granules * GRANULE_SIZE));

		if (contig == RMI_OP_MEM_CONTIG) {
			/* Single descriptor covering the entire range */
			addr_list[0] = INPLACE(RMI_ADDR_RDESC_4K_SZ, blk_sz) |
				       INPLACE(RMI_ADDR_RDESC_4K_CNT, blk_count) |
				       INPLACE(RMI_ADDR_RDESC_4K_ADDR,
					       aux_base >> GRANULE_SHIFT) |
				       INPLACE(RMI_ADDR_RDESC_4K_ST,
					       RMI_OP_MEM_DELEGATED);
			smc_op_mem_donate(handle, ns_buf, 1UL, &res);
		} else {
			/* One descriptor per granule */
			for (unsigned long i = 0; i < num_granules; i++) {
				addr_list[i] = encode_addr_desc(
					aux_base + i * GRANULE_SIZE,
					1UL, RMI_OP_MEM_DELEGATED);
			}
			smc_op_mem_donate(handle, ns_buf, num_granules, &res);
		}

		rc = unpack_return_code(res.x[0]);
		CHECK_EQUAL(RMI_INCOMPLETE, rc.status);
	}

	return handle;
}

/* ================================================================
 * Test Group
 * ================================================================
 */
TEST_GROUP(psmmu_sro_tests) {
	TEST_SETUP()
	{
		test_helpers_init();
		test_helpers_rmm_start(false);
		host_util_set_cpuid(0U);
		test_helpers_expect_assert_fail(false);
	}
	TEST_TEARDOWN()
	{
		/* Reset PSMMU state to INACTIVE for test isolation */
		struct smmuv3_dev *smmu = smmuv3_psmmu_find(get_psmmu_ptr());
		if (smmu != NULL) {
			smmuv3_psmmu_reset(smmu);
		}
	}
};

/* ----------------------------------------------------------------
 * TC1: PSMMU_ACTIVATE with invalid psmmu_ptr → RMI_ERROR_INPUT.
 * ----------------------------------------------------------------
 */
TEST(psmmu_sro_tests, activate_invalid_psmmu_ptr)
{
	struct smc_result res = {};
	uintptr_t params_pa = test_helpers_allocate_granules(1U);

	(void)memset((void *)params_pa, 0, GRANULE_SIZE);

	smc_psmmu_activate(0xDEADBEEFUL, params_pa, &res);
	CHECK_EQUAL(RMI_ERROR_INPUT, res.x[0]);
}

/* ----------------------------------------------------------------
 * TC2: PSMMU_ACTIVATE happy path - full donation and continue.
 *
 * Drives the entire activate flow:
 *   smc_psmmu_activate → INCOMPLETE + DONATE
 *   OP_MEM_DONATE × N  → INCOMPLETE (multiple ranges)
 *   OP_CONTINUE        → RMI_SUCCESS
 * ----------------------------------------------------------------
 */
TEST(psmmu_sro_tests, activate_happy_path)
{
	unsigned long psmmu_ptr = get_psmmu_ptr();
	uintptr_t ns_buf = test_helpers_allocate_granules(1U);

	unsigned long handle = drive_activate_donations(psmmu_ptr, ns_buf);

	/* OP_CONTINUE to finalize activation */
	struct smc_result res = {};
	smc_op_continue(handle, 0UL, &res);
	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
}

/* ----------------------------------------------------------------
 * TC3: PSMMU_DEACTIVATE after successful activation.
 *
 * Activates the PSMMU, then deactivates it:
 *   smc_psmmu_deactivate → INCOMPLETE + RECLAIM
 *   OP_MEM_RECLAIM       → INCOMPLETE + NONE
 *   OP_CONTINUE          → RMI_SUCCESS
 * ----------------------------------------------------------------
 */
TEST(psmmu_sro_tests, deactivate_happy_path)
{
	unsigned long psmmu_ptr = get_psmmu_ptr();
	uintptr_t ns_buf = test_helpers_allocate_granules(1U);

	/* Activate first */
	unsigned long handle = drive_activate_donations(psmmu_ptr, ns_buf);
	struct smc_result res = {};
	smc_op_continue(handle, 0UL, &res);
	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);

	/* Now deactivate */
	smc_psmmu_deactivate(psmmu_ptr, &res);
	return_code_t rc = unpack_return_code(res.x[0]);
	CHECK_EQUAL(RMI_INCOMPLETE, rc.status);
	CHECK_EQUAL(RMI_OP_MEM_REQ_RECLAIM,
		    (unsigned long)EXTRACT(RMI_OP_MEM_REQ, res.x[0]));

	handle = res.x[1];

	/* Reclaim all donated memory */
	smc_op_mem_reclaim(handle, ns_buf, 4UL, &res);
	rc = unpack_return_code(res.x[0]);
	CHECK_EQUAL(RMI_INCOMPLETE, rc.status);
	CHECK_EQUAL(RMI_OP_MEM_REQ_NONE,
		    (unsigned long)EXTRACT(RMI_OP_MEM_REQ, res.x[0]));

	/* Finish deactivation */
	smc_op_continue(handle, 0UL, &res);
	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
}

/* ----------------------------------------------------------------
 * TC4: PSMMU_ACTIVATE donation failure triggers reclaim.
 *
 * Start activate, donate correctly for L1_ST, then send a non-delegated
 * granule for CMDQ. This causes the driver to trigger reclaim of all
 * previously donated memory.
 * ----------------------------------------------------------------
 */
TEST(psmmu_sro_tests, activate_donation_failure_triggers_reclaim)
{
	unsigned long psmmu_ptr = get_psmmu_ptr();
	uintptr_t ns_buf = test_helpers_allocate_granules(1U);
	unsigned long *addr_list = (unsigned long *)ns_buf;
	struct smc_result res = {};
	struct psmmu_params params = {};

	/* Write params into an NS granule */
	uintptr_t params_pa = test_helpers_allocate_granules(1U);
	(void)memset((void *)params_pa, 0, GRANULE_SIZE);
	(void)memcpy((void *)params_pa, &params, sizeof(params));

	smc_psmmu_activate(psmmu_ptr, params_pa, &res);
	return_code_t rc = unpack_return_code(res.x[0]);
	CHECK_EQUAL(RMI_INCOMPLETE, rc.status);

	unsigned long handle = res.x[1];
	unsigned long donate_req = res.x[2];

	/* Donate the first range (L1 ST) successfully */
	unsigned long blk_sz = EXTRACT(RMI_OP_DONATE_BLK_SIZE, donate_req);
	unsigned long blk_count = EXTRACT(RMI_OP_DONATE_BLK_COUNT, donate_req);
	unsigned long blk_size_bytes =
		XLAT_BLOCK_SIZE((int)XLAT_TABLE_LEVEL_MAX - (int)blk_sz);
	unsigned long num_granules = (blk_count * blk_size_bytes) / GRANULE_SIZE;

	uintptr_t aux_base = test_helpers_allocate_granules_aligned((unsigned int)num_granules);
	CHECK_TRUE(delegate_range(aux_base,
				  aux_base + num_granules * GRANULE_SIZE));

	addr_list[0] = INPLACE(RMI_ADDR_RDESC_4K_SZ, blk_sz) |
		       INPLACE(RMI_ADDR_RDESC_4K_CNT, blk_count) |
		       INPLACE(RMI_ADDR_RDESC_4K_ADDR,
			       aux_base >> GRANULE_SHIFT) |
		       INPLACE(RMI_ADDR_RDESC_4K_ST, RMI_OP_MEM_DELEGATED);

	smc_op_mem_donate(handle, ns_buf, 1UL, &res);
	rc = unpack_return_code(res.x[0]);
	CHECK_EQUAL(RMI_INCOMPLETE, rc.status);

	/* Next range should be requested (CMDQ - non-contiguous) */
	unsigned long mem_req = EXTRACT(RMI_OP_MEM_REQ, res.x[0]);
	CHECK_EQUAL(RMI_OP_MEM_REQ_DONATE, mem_req);

	/*
	 * Send a non-delegated granule for CMDQ.
	 * This should fail and trigger reclaim.
	 */
	donate_req = res.x[2];
	blk_sz = EXTRACT(RMI_OP_DONATE_BLK_SIZE, donate_req);
	blk_count = EXTRACT(RMI_OP_DONATE_BLK_COUNT, donate_req);
	blk_size_bytes = XLAT_BLOCK_SIZE((int)XLAT_TABLE_LEVEL_MAX - (int)blk_sz);
	num_granules = (blk_count * blk_size_bytes) / GRANULE_SIZE;
	CHECK_EQUAL(1UL, num_granules);

	uintptr_t bad_page = test_helpers_allocate_granules(1U);
	/* NOT delegated — this will fail the donation */

	addr_list[0] = encode_addr_desc(bad_page, 1UL, RMI_OP_MEM_DELEGATED);

	smc_op_mem_donate(handle, ns_buf, 1UL, &res);
	rc = unpack_return_code(res.x[0]);
	CHECK_EQUAL(RMI_INCOMPLETE, rc.status);

	/* Should request RECLAIM now */
	mem_req = EXTRACT(RMI_OP_MEM_REQ, res.x[0]);
	CHECK_EQUAL(RMI_OP_MEM_REQ_RECLAIM, mem_req);

	/*
	 * Perform the reclaim.
	 * Total donated: 2 (L1_ST) granules.
	 * They may be coalesced into fewer descriptors.
	 */
	smc_op_mem_reclaim(handle, ns_buf, 2UL, &res);
	rc = unpack_return_code(res.x[0]);
	CHECK_EQUAL(RMI_INCOMPLETE, rc.status);
	CHECK_EQUAL(RMI_OP_MEM_REQ_NONE,
		    (unsigned long)EXTRACT(RMI_OP_MEM_REQ, res.x[0]));

	/* At least one descriptor should have been returned */
	CHECK_TRUE(res.x[1] > 0UL);

	/* Verify total granules in descriptors sum to 2 */
	unsigned long total_grans = 0UL;
	for (unsigned long i = 0UL; i < res.x[1]; i++) {
		unsigned long desc = addr_list[i];
		unsigned long blk_sz = EXTRACT(RMI_ADDR_RDESC_4K_SZ, desc);
		unsigned long blk_cnt = EXTRACT(RMI_ADDR_RDESC_4K_CNT, desc);
		unsigned long blk_bytes =
			XLAT_BLOCK_SIZE((int)XLAT_TABLE_LEVEL_MAX - (int)blk_sz);
		total_grans += (blk_cnt * blk_bytes) / GRANULE_SIZE;
	}
	CHECK_EQUAL(2UL, total_grans);

	/* OP_CONTINUE should return the error */
	smc_op_continue(handle, 0UL, &res);
	CHECK_EQUAL(RMI_ERROR_INPUT, res.x[0]);
}

/* ----------------------------------------------------------------
 * TC5: ST_L2_CREATE happy path - donate and continue.
 *
 * Requires the PSMMU to be in ACTIVE state first.
 *   smc_psmmu_st_l2_create → INCOMPLETE + DONATE
 *   OP_MEM_DONATE          → INCOMPLETE + NONE
 *   OP_CONTINUE            → RMI_SUCCESS
 * ----------------------------------------------------------------
 */
TEST(psmmu_sro_tests, st_l2_create_happy_path)
{
	unsigned long psmmu_ptr = get_psmmu_ptr();
	uintptr_t ns_buf = test_helpers_allocate_granules(1U);

	/* First activate the PSMMU */
	unsigned long handle = drive_activate_donations(psmmu_ptr, ns_buf);
	struct smc_result res = {};
	smc_op_continue(handle, 0UL, &res);
	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);

	/* Now create an L2 stream table for SID 0 */
	smc_psmmu_st_l2_create(psmmu_ptr, 0UL, &res);
	return_code_t rc = unpack_return_code(res.x[0]);
	CHECK_EQUAL(RMI_INCOMPLETE, rc.status);
	CHECK_EQUAL(RMI_OP_MEM_REQ_DONATE,
		    (unsigned long)EXTRACT(RMI_OP_MEM_REQ, res.x[0]));

	handle = res.x[1];
	unsigned long donate_req = res.x[2];
	unsigned long blk_count = EXTRACT(RMI_OP_DONATE_BLK_COUNT, donate_req);
	CHECK_EQUAL(1UL, blk_count);

	/* Donate 1 granule for the L2 stream table */
	uintptr_t l2_pa = test_helpers_allocate_granules(1U);
	CHECK_TRUE(delegate_range(l2_pa, l2_pa + GRANULE_SIZE));

	unsigned long *addr_list = (unsigned long *)ns_buf;
	addr_list[0] = encode_addr_desc(l2_pa, 1UL, RMI_OP_MEM_DELEGATED);

	smc_op_mem_donate(handle, ns_buf, 1UL, &res);
	rc = unpack_return_code(res.x[0]);
	CHECK_EQUAL(RMI_INCOMPLETE, rc.status);
	CHECK_EQUAL(RMI_OP_MEM_REQ_NONE,
		    (unsigned long)EXTRACT(RMI_OP_MEM_REQ, res.x[0]));

	/* OP_CONTINUE to finalize L2 creation */
	smc_op_continue(handle, 0UL, &res);
	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
}

/* ----------------------------------------------------------------
 * TC6: ST_L2_DESTROY happy path - reclaim and continue.
 *
 * After creating an L2 stream table, destroy it:
 *   smc_psmmu_st_l2_destroy → INCOMPLETE + RECLAIM
 *   OP_MEM_RECLAIM          → INCOMPLETE + NONE
 *   OP_CONTINUE             → RMI_SUCCESS
 * ----------------------------------------------------------------
 */
TEST(psmmu_sro_tests, st_l2_destroy_happy_path)
{
	unsigned long psmmu_ptr = get_psmmu_ptr();
	uintptr_t ns_buf = test_helpers_allocate_granules(1U);

	/* Activate the PSMMU */
	unsigned long handle = drive_activate_donations(psmmu_ptr, ns_buf);
	struct smc_result res = {};
	smc_op_continue(handle, 0UL, &res);
	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);

	/* Create L2 for SID 0 */
	smc_psmmu_st_l2_create(psmmu_ptr, 0UL, &res);
	return_code_t rc = unpack_return_code(res.x[0]);
	CHECK_EQUAL(RMI_INCOMPLETE, rc.status);

	handle = res.x[1];
	uintptr_t l2_pa = test_helpers_allocate_granules(1U);
	CHECK_TRUE(delegate_range(l2_pa, l2_pa + GRANULE_SIZE));

	unsigned long *addr_list = (unsigned long *)ns_buf;
	addr_list[0] = encode_addr_desc(l2_pa, 1UL, RMI_OP_MEM_DELEGATED);
	smc_op_mem_donate(handle, ns_buf, 1UL, &res);
	rc = unpack_return_code(res.x[0]);
	CHECK_EQUAL(RMI_INCOMPLETE, rc.status);
	smc_op_continue(handle, 0UL, &res);
	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);

	/* Now destroy L2 for SID 0 */
	smc_psmmu_st_l2_destroy(psmmu_ptr, 0UL, &res);
	rc = unpack_return_code(res.x[0]);
	CHECK_EQUAL(RMI_INCOMPLETE, rc.status);
	CHECK_EQUAL(RMI_OP_MEM_REQ_RECLAIM,
		    (unsigned long)EXTRACT(RMI_OP_MEM_REQ, res.x[0]));

	handle = res.x[1];

	/* Reclaim the L2 granule */
	smc_op_mem_reclaim(handle, ns_buf, 1UL, &res);
	rc = unpack_return_code(res.x[0]);
	CHECK_EQUAL(RMI_INCOMPLETE, rc.status);
	CHECK_EQUAL(RMI_OP_MEM_REQ_NONE,
		    (unsigned long)EXTRACT(RMI_OP_MEM_REQ, res.x[0]));

	/* Verify we got the L2 granule address back */
	unsigned long desc = addr_list[0];
	unsigned long reclaimed_addr = RMI_ADDR_RDESC_4K_GET_ADDR(desc);
	CHECK_EQUAL(l2_pa, reclaimed_addr);

	/* Finish */
	smc_op_continue(handle, 0UL, &res);
	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
}

/* ----------------------------------------------------------------
 * TC7: ST_L2_CREATE with non-delegated granule → reclaim path.
 *
 * Send a non-delegated granule for the L2 table. The donation
 * fails but since only 1 granule is involved (and it wasn't
 * transitioned), there's nothing to reclaim. The SRO flow
 * exits with an error on OP_CONTINUE.
 * ----------------------------------------------------------------
 */
TEST(psmmu_sro_tests, st_l2_create_non_delegated_granule)
{
	unsigned long psmmu_ptr = get_psmmu_ptr();
	uintptr_t ns_buf = test_helpers_allocate_granules(1U);

	/* Activate the PSMMU */
	unsigned long handle = drive_activate_donations(psmmu_ptr, ns_buf);
	struct smc_result res = {};
	smc_op_continue(handle, 0UL, &res);
	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);

	/* Create L2 for SID 0 */
	smc_psmmu_st_l2_create(psmmu_ptr, 0UL, &res);
	return_code_t rc = unpack_return_code(res.x[0]);
	CHECK_EQUAL(RMI_INCOMPLETE, rc.status);

	handle = res.x[1];

	/* Send a non-delegated granule (stays in NS state) */
	uintptr_t bad_pa = test_helpers_allocate_granules(1U);
	unsigned long *addr_list = (unsigned long *)ns_buf;
	addr_list[0] = encode_addr_desc(bad_pa, 1UL, RMI_OP_MEM_DELEGATED);

	smc_op_mem_donate(handle, ns_buf, 1UL, &res);
	rc = unpack_return_code(res.x[0]);
	CHECK_EQUAL(RMI_INCOMPLETE, rc.status);

	/*
	 * The L2 donation failed. Since there were no previously
	 * donated ranges, the code skips to RECLAIM_FINISH.
	 * OP_CONTINUE returns the error code.
	 */
	smc_op_continue(handle, 0UL, &res);
	CHECK_EQUAL(RMI_ERROR_INPUT, res.x[0]);
}

/* ----------------------------------------------------------------
 * TC8: ST_L2_CREATE with invalid SID → RMI_ERROR_INPUT (no SRO).
 * ----------------------------------------------------------------
 */
TEST(psmmu_sro_tests, st_l2_create_invalid_sid)
{
	unsigned long psmmu_ptr = get_psmmu_ptr();
	uintptr_t ns_buf = test_helpers_allocate_granules(1U);

	/* Activate the PSMMU */
	unsigned long handle = drive_activate_donations(psmmu_ptr, ns_buf);
	struct smc_result res = {};
	smc_op_continue(handle, 0UL, &res);
	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);

	/* Use an out-of-range SID (streamid_bits = 16 → max = 65535) */
	smc_psmmu_st_l2_create(psmmu_ptr, 0x10000UL, &res);
	CHECK_EQUAL(RMI_ERROR_INPUT, res.x[0]);
}

/* ----------------------------------------------------------------
 * TC9: PSMMU_DEACTIVATE when PSMMU is not in ACTIVE state.
 * ----------------------------------------------------------------
 */
TEST(psmmu_sro_tests, deactivate_not_active)
{
	unsigned long psmmu_ptr = get_psmmu_ptr();
	struct smc_result res = {};

	/* PSMMU starts in INACTIVE state; deactivate should fail */
	smc_psmmu_deactivate(psmmu_ptr, &res);
	CHECK_EQUAL(RMI_ERROR_INPUT, res.x[0]);
}

/* ----------------------------------------------------------------
 * TC10: ST_L2_DESTROY with invalid SID → RMI_ERROR_INPUT.
 * ----------------------------------------------------------------
 */
TEST(psmmu_sro_tests, st_l2_destroy_invalid_sid)
{
	unsigned long psmmu_ptr = get_psmmu_ptr();
	uintptr_t ns_buf = test_helpers_allocate_granules(1U);

	/* Activate the PSMMU */
	unsigned long handle = drive_activate_donations(psmmu_ptr, ns_buf);
	struct smc_result res = {};
	smc_op_continue(handle, 0UL, &res);
	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);

	/* Invalid SID */
	smc_psmmu_st_l2_destroy(psmmu_ptr, 0x10000UL, &res);
	CHECK_EQUAL(RMI_ERROR_INPUT, res.x[0]);
}

/* ----------------------------------------------------------------
 * TC11: Invalid handle passed to OP_MEM_DONATE during PSMMU
 *       activation → RMI_ERROR_INPUT.
 * ----------------------------------------------------------------
 */
TEST(psmmu_sro_tests, activate_donate_invalid_handle)
{
	unsigned long psmmu_ptr = get_psmmu_ptr();
	uintptr_t ns_buf = test_helpers_allocate_granules(1U);
	unsigned long *addr_list = (unsigned long *)ns_buf;
	struct smc_result res = {};
	struct psmmu_params params = {};

	uintptr_t params_pa = test_helpers_allocate_granules(1U);
	(void)memset((void *)params_pa, 0, GRANULE_SIZE);
	(void)memcpy((void *)params_pa, &params, sizeof(params));

	smc_psmmu_activate(psmmu_ptr, params_pa, &res);
	return_code_t rc = unpack_return_code(res.x[0]);
	CHECK_EQUAL(RMI_INCOMPLETE, rc.status);

	unsigned long handle = res.x[1];
	(void)handle;

	/* Donate with a bogus handle */
	uintptr_t aux_base = test_helpers_allocate_granules(1U);
	CHECK_TRUE(delegate_range(aux_base, aux_base + GRANULE_SIZE));
	addr_list[0] = encode_addr_desc(aux_base, 1UL, RMI_OP_MEM_DELEGATED);

	smc_op_mem_donate(0xDEADBEEFUL, ns_buf, 1UL, &res);
	CHECK_EQUAL(RMI_ERROR_INPUT, res.x[0]);
}

/* ----------------------------------------------------------------
 * TC12: OP_MEM_DONATE with empty list (count=0) during activation.
 *
 * An empty list donates zero bytes and makes no progress. The SRO
 * flow remains in INCOMPLETE state, still requesting donations.
 * After verifying, complete the activation normally.
 * ----------------------------------------------------------------
 */
TEST(psmmu_sro_tests, activate_donate_empty_list)
{
	unsigned long psmmu_ptr = get_psmmu_ptr();
	uintptr_t ns_buf = test_helpers_allocate_granules(1U);
	unsigned long *addr_list = (unsigned long *)ns_buf;
	struct smc_result res = {};
	struct psmmu_params params = {};

	uintptr_t params_pa = test_helpers_allocate_granules(1U);
	(void)memset((void *)params_pa, 0, GRANULE_SIZE);
	(void)memcpy((void *)params_pa, &params, sizeof(params));

	smc_psmmu_activate(psmmu_ptr, params_pa, &res);
	return_code_t rc = unpack_return_code(res.x[0]);
	CHECK_EQUAL(RMI_INCOMPLETE, rc.status);
	CHECK_EQUAL(RMI_OP_MEM_REQ_DONATE,
		    (unsigned long)EXTRACT(RMI_OP_MEM_REQ, res.x[0]));

	unsigned long handle = res.x[1];

	/* Donate with an empty list (count = 0) */
	smc_op_mem_donate(handle, ns_buf, 0UL, &res);
	rc = unpack_return_code(res.x[0]);
	CHECK_EQUAL(RMI_INCOMPLETE, rc.status);

	/* Flow still expects donations */
	CHECK_EQUAL(RMI_OP_MEM_REQ_DONATE,
		    (unsigned long)EXTRACT(RMI_OP_MEM_REQ, res.x[0]));

	/* Complete the activation by driving the remaining donations */
	while (true) {
		unsigned long mem_req = EXTRACT(RMI_OP_MEM_REQ, res.x[0]);

		if (mem_req == RMI_OP_MEM_REQ_NONE) {
			break;
		}

		unsigned long donate_req = res.x[2];
		unsigned long blk_sz = EXTRACT(RMI_OP_DONATE_BLK_SIZE, donate_req);
		unsigned long blk_count = EXTRACT(RMI_OP_DONATE_BLK_COUNT, donate_req);
		unsigned long contig = EXTRACT(RMI_OP_DONATE_MEM_CONTIG, donate_req);
		unsigned long blk_size_bytes =
			XLAT_BLOCK_SIZE((int)XLAT_TABLE_LEVEL_MAX - (int)blk_sz);
		unsigned long num_granules =
			(blk_count * blk_size_bytes) / GRANULE_SIZE;

		uintptr_t aux_base;
		if (contig == RMI_OP_MEM_CONTIG) {
			aux_base = test_helpers_allocate_granules_aligned(
					(unsigned int)num_granules);
		} else {
			aux_base = test_helpers_allocate_granules(
					(unsigned int)num_granules);
		}
		CHECK_TRUE(delegate_range(aux_base,
					  aux_base + num_granules * GRANULE_SIZE));

		if (contig == RMI_OP_MEM_CONTIG) {
			addr_list[0] = INPLACE(RMI_ADDR_RDESC_4K_SZ, blk_sz) |
				       INPLACE(RMI_ADDR_RDESC_4K_CNT, blk_count) |
				       INPLACE(RMI_ADDR_RDESC_4K_ADDR,
					       aux_base >> GRANULE_SHIFT) |
				       INPLACE(RMI_ADDR_RDESC_4K_ST,
					       RMI_OP_MEM_DELEGATED);
			smc_op_mem_donate(handle, ns_buf, 1UL, &res);
		} else {
			for (unsigned long i = 0; i < num_granules; i++) {
				addr_list[i] = encode_addr_desc(
					aux_base + i * GRANULE_SIZE,
					1UL, RMI_OP_MEM_DELEGATED);
			}
			smc_op_mem_donate(handle, ns_buf, num_granules, &res);
		}

		rc = unpack_return_code(res.x[0]);
		CHECK_EQUAL(RMI_INCOMPLETE, rc.status);
	}

	/* Finalize activation */
	smc_op_continue(handle, 0UL, &res);
	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
}
