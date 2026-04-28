/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <CppUTest/CommandLineTestRunner.h>
#include <CppUTest/TestHarness.h>

extern "C" {
#include <arch_helpers.h>
#include <debug.h>
#include <granule.h>
#include <host_utils.h>
#include <smc-handler.h>
#include <smc-rmi.h>
#include <smc.h>
#include <sro_context.h>
#include <status.h>
#include <stdlib.h>
#include <string.h>
#include <test_helpers.h>
#include <utils_def.h>
#include <xlat_defs.h>

/* Test-only API defined in sro.c */
sro_handle_cb sro_install_test_handler(unsigned long command, sro_handle_cb cb);
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
 * Encode an RmiAddrRangeDesc4KB with an explicit block size field.
 */
static unsigned long encode_addr_desc_blk(uintptr_t base, unsigned long count,
					  unsigned long state,
					  unsigned long blk_sz)
{
	return INPLACE(RMI_ADDR_RDESC_4K_SZ, blk_sz) |
	       INPLACE(RMI_ADDR_RDESC_4K_CNT, count) |
	       INPLACE(RMI_ADDR_RDESC_4K_ADDR, base >> GRANULE_SHIFT) |
	       INPLACE(RMI_ADDR_RDESC_4K_ST, state);
}

/*
 * Helper to get a granule physical address by index.
 */
static uintptr_t granule_addr(unsigned int idx)
{
	return host_util_get_granule_base() + (uintptr_t)idx * GRANULE_SIZE;
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
		if (cur == 0UL) {
			break;
		}
	}
	return true;
}

static unsigned int g_next_idx = 1U; /* skip granule 0 */

/*
 * Reserve 'n' contiguous granules and return the base PA.
 */
static uintptr_t reserve_granules(unsigned int n)
{
	unsigned int nr = test_helpers_get_nr_granules();

	CHECK_TRUE((g_next_idx + n) <= nr);
	uintptr_t base = granule_addr(g_next_idx);
	g_next_idx += n;
	return base;
}

/*
 * Minimal callback: accept the donation and signal success.
 * smc_op_mem_donate asserts "(res->x[1] * GRANULE_SIZE) <= total_mem"
 * after the callback, so x[1] must be the total number of granules
 * described by the addr_list (not the number of range descriptors).
 */
static void noop_donate_cb(unsigned long fid, struct smc_result *res)
{
	(void)fid;
	struct sro_context *sro = my_sro_ctx();
	unsigned long total_granules = 0UL;

	for (unsigned int i = 0U; i < sro->addr_list.count; i++) {
		unsigned long desc = sro->addr_list.range_desc[i];
		unsigned long cnt = EXTRACT(RMI_ADDR_RDESC_4K_CNT, desc);
		unsigned long sz = EXTRACT(RMI_ADDR_RDESC_4K_SZ, desc);

		total_granules += cnt *
			(XLAT_BLOCK_SIZE((int)XLAT_TABLE_LEVEL_MAX -
					 (int)sz) / GRANULE_SIZE);
	}

	res->x[0] = RMI_SUCCESS;
	res->x[1] = total_granules;
}

/*
 * Callback that signals SRO completion (SUCCESS).
 * Used by continue / cancel tests where the handler finishes.
 */
static void success_cb(unsigned long fid, struct smc_result *res)
{
	(void)fid;
	res->x[0] = RMI_SUCCESS;
}

/*
 * Callback that returns INCOMPLETE with no MEM_REQ.
 * Used to exercise seal-after-cancel paths.
 */
static void incomplete_cb(unsigned long fid, struct smc_result *res)
{
	(void)fid;
	res->x[0] = RMI_INCOMPLETE;
}

/*
 * Callback that returns INCOMPLETE with MEM_REQ_DONATE,
 * requesting 1 L3 page.  Sets next expected FID to MEM_DONATE.
 */
static void incomplete_donate_req_cb(unsigned long fid,
				     struct smc_result *res)
{
	(void)fid;
	res->x[0] = RMI_INCOMPLETE |
		    INPLACE(RMI_OP_MEM_REQ, RMI_OP_MEM_REQ_DONATE) |
		    INPLACE(RMI_OP_CAN_CANCEL_BIT, RMI_OP_CAN_CANCEL);
	res->x[1] = 0UL;
	res->x[2] = INPLACE(RMI_OP_DONATE_BLK_SIZE, RMI_PAGE_L3) |
		    INPLACE(RMI_OP_DONATE_BLK_COUNT, 1UL);
}

/*
 * Number of reclaim entries the reclaim_entries_cb callback should
 * produce, and the base address to use for the descriptors.
 */
static unsigned long g_reclaim_count;
static uintptr_t    g_reclaim_base;

/*
 * Reclaim callback: fills my_sro_ctx()->list_buffer with
 * g_reclaim_count entries and returns INCOMPLETE | MEM_REQ_RECLAIM.
 */
static void reclaim_entries_cb(unsigned long fid,
			       struct smc_result *res)
{
	(void)fid;
	struct sro_context *sro = my_sro_ctx();

	addr_list_init(&sro->addr_list, LIST_TYPE_OUTPUT);
	for (unsigned long i = 0UL; i < g_reclaim_count; i++) {
		sro->addr_list.range_desc[i] = encode_addr_desc(
				g_reclaim_base + i * GRANULE_SIZE,
				1UL, RMI_OP_MEM_DELEGATED);
	}
	sro->addr_list.count = g_reclaim_count;
	res->x[0] = RMI_INCOMPLETE |
		    INPLACE(RMI_OP_MEM_REQ, RMI_OP_MEM_REQ_RECLAIM) |
		    INPLACE(RMI_OP_CAN_CANCEL_BIT, RMI_OP_CAN_CANCEL);
	res->x[1] = g_reclaim_count;
}

/*
 * Reserve an SRO context for REC_CREATE, configure it to expect
 * OP_MEM_DONATE, seal it and return the handle.
 *
 * @xfer     : transfer_req — maximum total memory that can be donated.
 * @is_contig: whether donated memory must be contiguous.
 */
static unsigned long create_donate_ctx(unsigned long xfer, bool is_contig)
{
	unsigned long ret = sro_ctx_reserve(SMC_RMI_REC_CREATE, xfer,
					    false, is_contig,
					    SMC_RMI_OP_MEM_DONATE);

	CHECK_EQUAL(RMI_SUCCESS, ret);
	return (unsigned long)sro_ctx_seal();
}

/*
 * Find a sealed SRO context and release it.
 */
static void release_ctx(unsigned long handle)
{
	if (sro_ctx_find(handle)) {
		sro_ctx_release();
	}
}

/*
 * Create SRO context expecting OP_CONTINUE.
 */
static unsigned long create_continue_ctx(bool can_cancel)
{
	unsigned long ret = sro_ctx_reserve(SMC_RMI_REC_CREATE, 0UL,
					    can_cancel, false,
					    SMC_RMI_OP_CONTINUE);

	CHECK_EQUAL(RMI_SUCCESS, ret);
	return (unsigned long)sro_ctx_seal();
}

/*
 * Create SRO context expecting OP_MEM_RECLAIM.
 */
static unsigned long create_reclaim_ctx(void)
{
	unsigned long ret = sro_ctx_reserve(SMC_RMI_REC_CREATE, 0UL,
					    false, false,
					    SMC_RMI_OP_MEM_RECLAIM);

	CHECK_EQUAL(RMI_SUCCESS, ret);
	return (unsigned long)sro_ctx_seal();
}

/* ================================================================
 * Test Group for SRO input validation (donate, continue,
 * reclaim, cancel)
 *
 * Uses lightweight test callbacks installed in the SRO dispatch
 * table so that SRO entry points can be exercised in isolation
 * without going through the full REC_CREATE / REC_DESTROY flows.
 * ================================================================
 */

TEST_GROUP(sro_donate_tests) {
	sro_handle_cb m_orig;

	TEST_SETUP()
	{
		test_helpers_init();
		test_helpers_rmm_start(false);
		host_util_set_cpuid(0U);
		test_helpers_expect_assert_fail(false);

		/* Install the test callback in the REC_CREATE slot */
		m_orig = sro_install_test_handler(SMC_RMI_REC_CREATE,
						  noop_donate_cb);
	}
	TEST_TEARDOWN()
	{
		/* Restore the original handler */
		sro_install_test_handler(SMC_RMI_REC_CREATE, m_orig);
	}
};

/* ----------------------------------------------------------------
 * TC_DONATE_01: Invalid (bogus) handle → ERROR_INPUT.
 *
 *  sro_ctx_find() fails before any input validation.
 * ----------------------------------------------------------------
 */
TEST(sro_donate_tests, donate_invalid_handle)
{
	uintptr_t ns_buf = reserve_granules(1U);
	unsigned long *list = (unsigned long *)ns_buf;

	list[0] = encode_addr_desc(ns_buf, 1UL, RMI_OP_MEM_DELEGATED);

	struct smc_result res = {};
	smc_op_mem_donate(0xDEADBEEFUL, ns_buf, 1UL, &res);
	CHECK_EQUAL(RMI_ERROR_INPUT, res.x[0]);
}

/* ----------------------------------------------------------------
 * TC_DONATE_02: Unaligned list_addr → ERROR_INPUT.
 * ----------------------------------------------------------------
 */
TEST(sro_donate_tests, donate_unaligned_list_addr)
{
	unsigned long xfer = GRANULE_SIZE;
	unsigned long handle = create_donate_ctx(xfer, false);

	uintptr_t ns_buf = reserve_granules(1U);
	/* Misalign by 3 bytes */
	uintptr_t bad_addr = ns_buf + 3UL;

	struct smc_result res = {};
	smc_op_mem_donate(handle, bad_addr, 1UL, &res);
	CHECK_EQUAL(RMI_ERROR_INPUT, res.x[0]);

	release_ctx(handle);
}

/* ----------------------------------------------------------------
 * TC_DONATE_04: Contiguous context with list_count > 1 → ERROR_INPUT.
 *
 *  is_contig=true requires a single entry in the list.
 * ----------------------------------------------------------------
 */
TEST(sro_donate_tests, donate_contig_multi_entry)
{
	unsigned long xfer = 2UL * GRANULE_SIZE;
	unsigned long handle = create_donate_ctx(xfer, true);
	uintptr_t ns_buf = reserve_granules(1U);

	unsigned long *list = (unsigned long *)ns_buf;
	list[0] = encode_addr_desc(ns_buf, 1UL, RMI_OP_MEM_DELEGATED);
	list[1] = encode_addr_desc(ns_buf, 1UL, RMI_OP_MEM_DELEGATED);

	struct smc_result res = {};
	smc_op_mem_donate(handle, ns_buf, 2UL, &res);
	CHECK_EQUAL(RMI_ERROR_INPUT, res.x[0]);

	release_ctx(handle);
}

/* ----------------------------------------------------------------
 * TC_DONATE_05: List granule address is not in NS PAS → ERROR_INPUT.
 *
 *  A delegated granule is not NS, so find_granule check fails.
 * ----------------------------------------------------------------
 */
TEST(sro_donate_tests, donate_list_granule_not_ns)
{
	unsigned long xfer = GRANULE_SIZE;
	unsigned long handle = create_donate_ctx(xfer, false);

	uintptr_t del_buf = reserve_granules(1U);
	CHECK_TRUE(delegate_range(del_buf, del_buf + GRANULE_SIZE));

	struct smc_result res = {};
	smc_op_mem_donate(handle, del_buf, 1UL, &res);
	CHECK_EQUAL(RMI_ERROR_INPUT, res.x[0]);

	release_ctx(handle);
}

/* ----------------------------------------------------------------
 * TC_DONATE_06: Entry with CNT == 0 is skipped during validation.
 *
 *  Zero-count entries are allowed and silently skipped.
 * ----------------------------------------------------------------
 */
TEST(sro_donate_tests, donate_zero_cnt_entry)
{
	unsigned long xfer = GRANULE_SIZE;
	unsigned long handle = create_donate_ctx(xfer, false);
	uintptr_t ns_buf = reserve_granules(1U);

	unsigned long *list = (unsigned long *)ns_buf;
	/* CNT = 0 */
	list[0] = encode_addr_desc(ns_buf, 0UL, RMI_OP_MEM_DELEGATED);

	struct smc_result res = {};
	smc_op_mem_donate(handle, ns_buf, 1UL, &res);
	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
}

/* ----------------------------------------------------------------
 * TC_DONATE_07: Mixed valid/zero-count entries — valid entries
 *               are processed, zero-count entries are skipped.
 * ----------------------------------------------------------------
 */
TEST(sro_donate_tests, donate_mixed_zero_cnt)
{
	unsigned long xfer = 2UL * GRANULE_SIZE;
	unsigned long handle = create_donate_ctx(xfer, false);
	uintptr_t ns_buf = reserve_granules(1U);

	unsigned long *list = (unsigned long *)ns_buf;
	list[0] = encode_addr_desc(ns_buf, 1UL, RMI_OP_MEM_DELEGATED);
	list[1] = encode_addr_desc(ns_buf, 0UL, RMI_OP_MEM_DELEGATED);

	struct smc_result res = {};
	smc_op_mem_donate(handle, ns_buf, 2UL, &res);
	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
}

/* ----------------------------------------------------------------
 * TC_DONATE_08: Total transfer exceeds transfer_req → ERROR_INPUT.
 *
 *  Context allows 1 × GRANULE_SIZE; donation list claims 2.
 * ----------------------------------------------------------------
 */
TEST(sro_donate_tests, donate_transfer_exceeds_req)
{
	/* Allow only 1 granule worth of transfer */
	unsigned long xfer = GRANULE_SIZE;
	unsigned long handle = create_donate_ctx(xfer, false);
	uintptr_t ns_buf = reserve_granules(1U);

	unsigned long *list = (unsigned long *)ns_buf;
	/* Two entries, each CNT=1 → total = 2 × GRANULE_SIZE > xfer */
	list[0] = encode_addr_desc(ns_buf, 1UL, RMI_OP_MEM_DELEGATED);
	list[1] = encode_addr_desc(ns_buf, 1UL, RMI_OP_MEM_DELEGATED);

	struct smc_result res = {};
	smc_op_mem_donate(handle, ns_buf, 2UL, &res);
	CHECK_EQUAL(RMI_ERROR_INPUT, res.x[0]);

	release_ctx(handle);
}

/* ----------------------------------------------------------------
 * TC_DONATE_09: Entry address not aligned to block size → ERROR_INPUT.
 *
 *  Encode an entry with L2 (2 MB) block size.  The minimum alignment
 *  becomes 2 MB, but the entry address is only 4 KB-aligned.
 * ----------------------------------------------------------------
 */
TEST(sro_donate_tests, donate_entry_addr_unaligned_to_blk_size)
{
	/* L2 block size = 2 MB; allow enough transfer */
	unsigned long l2_blk_sz = 1UL;  /* blk_sz field 1 → XLAT level 2 */
	unsigned long l2_size = XLAT_BLOCK_SIZE(XLAT_TABLE_LEVEL_MAX -
						(int)l2_blk_sz);
	unsigned long xfer = l2_size;
	unsigned long handle = create_donate_ctx(xfer, false);
	uintptr_t ns_buf = reserve_granules(1U);

	/*
	 * The granule address is 4 KB-aligned but almost certainly
	 * not 2 MB-aligned, so the check will fail.  Guard against
	 * the unlikely case that it happens to be aligned.
	 */
	uintptr_t entry_addr = ns_buf;
	if (ALIGNED(entry_addr, l2_size)) {
		/* Shift by one granule to break 2 MB alignment */
		entry_addr += GRANULE_SIZE;
	}
	CHECK_FALSE(ALIGNED(entry_addr, l2_size));

	unsigned long *list = (unsigned long *)ns_buf;
	list[0] = encode_addr_desc_blk(entry_addr, 1UL,
				       RMI_OP_MEM_DELEGATED, l2_blk_sz);

	struct smc_result res = {};
	smc_op_mem_donate(handle, ns_buf, 1UL, &res);
	CHECK_EQUAL(RMI_ERROR_INPUT, res.x[0]);

	release_ctx(handle);
}

/* ----------------------------------------------------------------
 * TC_DONATE_10: Happy path — single valid L3 entry → SUCCESS.
 *
 *  The donation reaches the noop test callback which returns
 *  RMI_SUCCESS.
 * ----------------------------------------------------------------
 */
TEST(sro_donate_tests, donate_happy_path_single_entry)
{
	unsigned long xfer = GRANULE_SIZE;
	unsigned long handle = create_donate_ctx(xfer, false);
	uintptr_t ns_buf = reserve_granules(1U);

	uintptr_t donor = reserve_granules(1U);
	CHECK_TRUE(delegate_range(donor, donor + GRANULE_SIZE));

	unsigned long *list = (unsigned long *)ns_buf;
	list[0] = encode_addr_desc(donor, 1UL, RMI_OP_MEM_DELEGATED);

	struct smc_result res = {};
	smc_op_mem_donate(handle, ns_buf, 1UL, &res);
	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
	CHECK_EQUAL(1UL, res.x[1]);

	release_ctx(handle);
}

/* ----------------------------------------------------------------
 * TC_DONATE_11: Happy path — contiguous, single entry → SUCCESS.
 *
 *  is_contig=true with exactly one entry should pass.
 * ----------------------------------------------------------------
 */
TEST(sro_donate_tests, donate_happy_path_contig_single)
{
	unsigned long xfer = GRANULE_SIZE;
	unsigned long handle = create_donate_ctx(xfer, true);
	uintptr_t ns_buf = reserve_granules(1U);

	uintptr_t donor = reserve_granules(1U);
	CHECK_TRUE(delegate_range(donor, donor + GRANULE_SIZE));

	unsigned long *list = (unsigned long *)ns_buf;
	list[0] = encode_addr_desc(donor, 1UL, RMI_OP_MEM_DELEGATED);

	struct smc_result res = {};
	smc_op_mem_donate(handle, ns_buf, 1UL, &res);
	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);

	release_ctx(handle);
}

/* ----------------------------------------------------------------
 * TC_DONATE_11b: Contiguous donation with one valid entry and
 *                zero-count padding entries → SUCCESS.
 *
 *  Zero-count entries are skipped during validation and do not
 *  count toward the single-entry limit for contiguous mode.
 * ----------------------------------------------------------------
 */
TEST(sro_donate_tests, donate_contig_valid_plus_zero_cnt)
{
	unsigned long xfer = GRANULE_SIZE;
	unsigned long handle = create_donate_ctx(xfer, true);
	uintptr_t ns_buf = reserve_granules(1U);

	uintptr_t donor = reserve_granules(1U);
	CHECK_TRUE(delegate_range(donor, donor + GRANULE_SIZE));

	unsigned long *list = (unsigned long *)ns_buf;
	/* Zero-count entry (skipped) */
	list[0] = encode_addr_desc(ns_buf, 0UL, RMI_OP_MEM_DELEGATED);
	/* Valid single entry */
	list[1] = encode_addr_desc(donor, 1UL, RMI_OP_MEM_DELEGATED);
	/* Another zero-count entry (skipped) */
	list[2] = encode_addr_desc(ns_buf, 0UL, RMI_OP_MEM_DELEGATED);

	struct smc_result res = {};
	smc_op_mem_donate(handle, ns_buf, 3UL, &res);
	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);

	release_ctx(handle);
}

/* ----------------------------------------------------------------
 * TC_DONATE_11c: Contiguous donation where two valid entries exist
 *                among zero-count padding → ERROR_INPUT.
 *
 *  Even when separated by zero-count entries, having more than
 *  one valid descriptor is rejected in contiguous mode.
 * ----------------------------------------------------------------
 */
TEST(sro_donate_tests, donate_contig_two_valid_with_zeros)
{
	unsigned long xfer = 2UL * GRANULE_SIZE;
	unsigned long handle = create_donate_ctx(xfer, true);
	uintptr_t ns_buf = reserve_granules(1U);

	unsigned long *list = (unsigned long *)ns_buf;
	list[0] = encode_addr_desc(ns_buf, 1UL, RMI_OP_MEM_DELEGATED);
	list[1] = encode_addr_desc(ns_buf, 0UL, RMI_OP_MEM_DELEGATED);
	list[2] = encode_addr_desc(ns_buf, 1UL, RMI_OP_MEM_DELEGATED);

	struct smc_result res = {};
	smc_op_mem_donate(handle, ns_buf, 3UL, &res);
	CHECK_EQUAL(RMI_ERROR_INPUT, res.x[0]);

	release_ctx(handle);
}

/* ----------------------------------------------------------------
 * TC_DONATE_11d: Contiguous donation with multi-granule power-of-2
 *                block, properly aligned → SUCCESS.
 *
 *  Single entry: 2 × L3 (4K) = 8 KB, power of 2, addr aligned
 *  to 8 KB.
 * ----------------------------------------------------------------
 */
TEST(sro_donate_tests, donate_contig_multi_granule_aligned)
{
	unsigned long cnt = 2UL;
	unsigned long total_size = cnt * GRANULE_SIZE; /* 8 KB */
	unsigned long xfer = total_size;
	unsigned long handle = create_donate_ctx(xfer, true);
	uintptr_t ns_buf = reserve_granules(1U);

	/*
	 * Find a donor address that is aligned to total_size (8 KB).
	 * Reserve enough granules and pick an aligned base.
	 */
	uintptr_t pool = reserve_granules(4U);
	uintptr_t donor = round_up(pool, total_size);
	CHECK_TRUE(ALIGNED(donor, total_size));
	CHECK_TRUE(delegate_range(donor, donor + total_size));

	unsigned long *list = (unsigned long *)ns_buf;
	list[0] = encode_addr_desc(donor, cnt, RMI_OP_MEM_DELEGATED);

	struct smc_result res = {};
	smc_op_mem_donate(handle, ns_buf, 1UL, &res);
	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);

	release_ctx(handle);
}

/* ----------------------------------------------------------------
 * TC_DONATE_11e: Contiguous donation with non-power-of-2 total
 *                size → ERROR_INPUT.
 *
 *  3 × GRANULE_SIZE = 12 KB is not a power of 2.
 * ----------------------------------------------------------------
 */
TEST(sro_donate_tests, donate_contig_non_power_of_two)
{
	unsigned long cnt = 3UL;
	unsigned long total_size = cnt * GRANULE_SIZE; /* 12 KB */
	unsigned long xfer = total_size;
	unsigned long handle = create_donate_ctx(xfer, true);
	uintptr_t ns_buf = reserve_granules(1U);

	/*
	 * Even with a naturally aligned address, the non-power-of-2
	 * total size causes validation to fail.
	 */
	uintptr_t donor = reserve_granules(4U);
	donor = round_up(donor, total_size);

	unsigned long *list = (unsigned long *)ns_buf;
	list[0] = encode_addr_desc(donor, cnt, RMI_OP_MEM_DELEGATED);

	struct smc_result res = {};
	smc_op_mem_donate(handle, ns_buf, 1UL, &res);
	CHECK_EQUAL(RMI_ERROR_INPUT, res.x[0]);

	release_ctx(handle);
}

/* ----------------------------------------------------------------
 * TC_DONATE_11f: Contiguous donation — total is power-of-2 but
 *                addr not aligned to total size → ERROR_INPUT.
 *
 *  2 × 4K = 8 KB (power of 2). Address is 4 KB-aligned (valid
 *  for non-contig L3) but not 8 KB-aligned.
 * ----------------------------------------------------------------
 */
TEST(sro_donate_tests, donate_contig_addr_not_aligned_to_total)
{
	unsigned long cnt = 2UL;
	unsigned long total_size = cnt * GRANULE_SIZE; /* 8 KB */
	unsigned long xfer = total_size;
	unsigned long handle = create_donate_ctx(xfer, true);
	uintptr_t ns_buf = reserve_granules(1U);

	/*
	 * Find a donor address that IS 4 KB-aligned (block-aligned)
	 * but NOT 8 KB-aligned (total-size-aligned).
	 */
	uintptr_t pool = reserve_granules(4U);
	uintptr_t aligned = round_up(pool, total_size);
	uintptr_t donor = aligned + GRANULE_SIZE; /* 4K-aligned, not 8K */
	CHECK_TRUE(ALIGNED(donor, GRANULE_SIZE));
	CHECK_FALSE(ALIGNED(donor, total_size));

	unsigned long *list = (unsigned long *)ns_buf;
	list[0] = encode_addr_desc(donor, cnt, RMI_OP_MEM_DELEGATED);

	struct smc_result res = {};
	smc_op_mem_donate(handle, ns_buf, 1UL, &res);
	CHECK_EQUAL(RMI_ERROR_INPUT, res.x[0]);

	release_ctx(handle);
}

/* ----------------------------------------------------------------
 * TC_DONATE_11g: Descriptor with wrong memory state → ERROR_INPUT.
 *
 *  Context expects DELEGATE, but descriptor says UNDELEGATE.
 * ----------------------------------------------------------------
 */
TEST(sro_donate_tests, donate_wrong_state)
{
	unsigned long xfer = GRANULE_SIZE;
	unsigned long handle = create_donate_ctx(xfer, false);
	uintptr_t ns_buf = reserve_granules(1U);

	unsigned long *list = (unsigned long *)ns_buf;
	list[0] = encode_addr_desc(ns_buf, 1UL, RMI_OP_MEM_UNDELEGATED);

	struct smc_result res = {};
	smc_op_mem_donate(handle, ns_buf, 1UL, &res);
	CHECK_EQUAL(RMI_ERROR_INPUT, res.x[0]);

	release_ctx(handle);
}

/* ----------------------------------------------------------------
 * TC_DONATE_11h: Descriptor block count exceeds maximum → ERROR_INPUT.
 *
 *  For 4K granule, CNT is a 10-bit field (max 1023). The validation
 *  rejects descriptors where CNT > get_max_block_cnt().
 *  We encode the maximum representable value (1023) + 1 = 1024
 *  which wraps to 0 in the 10-bit field and would be a zero-count
 *  entry (skipped). Instead use the max count in a descriptor with
 *  a transfer_req that is too small to accept it.
 * ----------------------------------------------------------------
 */
TEST(sro_donate_tests, donate_total_exceeds_transfer_req_large_cnt)
{
	/*
	 * Allow only 1 granule of transfer, but request a descriptor
	 * with the maximum possible block count (1023 × 4K = ~4 MB).
	 */
	unsigned long max_cnt = (1UL << RMI_ADDR_RDESC_4K_CNT_WIDTH) - 1UL;
	unsigned long xfer = GRANULE_SIZE; /* much less than max_cnt pages */
	unsigned long handle = create_donate_ctx(xfer, false);
	uintptr_t ns_buf = reserve_granules(1U);

	unsigned long *list = (unsigned long *)ns_buf;
	list[0] = encode_addr_desc(ns_buf, max_cnt, RMI_OP_MEM_DELEGATED);

	struct smc_result res = {};
	smc_op_mem_donate(handle, ns_buf, 1UL, &res);
	CHECK_EQUAL(RMI_ERROR_INPUT, res.x[0]);

	release_ctx(handle);
}

/* ----------------------------------------------------------------
 * TC_DONATE_12: list_count is clamped to ADDR_LIST_MAX_RANGES.
 *
 *  Pass a huge list_count. The framework silently clamps it
 *  before reading from the NS buffer.  Verify the donation
 *  still succeeds (with the noop callback) and consumed count
 *  does not exceed ADDR_LIST_MAX_RANGES.
 * ----------------------------------------------------------------
 */
TEST(sro_donate_tests, donate_list_count_clamped)
{
	/*
	 * Allow a large transfer_req so the total-mem check passes
	 * even after clamping to ADDR_LIST_MAX_RANGES entries.
	 */
	unsigned long xfer = ADDR_LIST_MAX_RANGES * GRANULE_SIZE;
	unsigned long handle = create_donate_ctx(xfer, false);
	uintptr_t ns_buf = reserve_granules(1U);

	/* Fill the entire NS page with valid descriptors */
	unsigned long *list = (unsigned long *)ns_buf;
	for (unsigned long i = 0; i < ADDR_LIST_MAX_RANGES; i++) {
		uintptr_t fake_addr = ns_buf + i * GRANULE_SIZE;
		list[i] = encode_addr_desc(fake_addr, 1UL,
					   RMI_OP_MEM_DELEGATED);
	}

	struct smc_result res = {};
	/* Request far more than ADDR_LIST_MAX_RANGES */
	smc_op_mem_donate(handle, ns_buf,
			  ADDR_LIST_MAX_RANGES + 100UL, &res);

	/* Should succeed, and consumed must not exceed the maximum */
	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
	CHECK_TRUE(res.x[1] <= ADDR_LIST_MAX_RANGES);

	release_ctx(handle);
}

/* ----------------------------------------------------------------
 * TC_DONATE_13: list starts mid-granule, count clamped to avoid
 *               crossing the granule boundary.
 *
 *  Place the list at an 8-byte-aligned offset inside an NS
 *  granule.  Verify that the framework caps list_count so the
 *  operation doesn't cross the granule boundary.
 * ----------------------------------------------------------------
 */
TEST(sro_donate_tests, donate_mid_granule_boundary_clamp)
{
	unsigned long xfer = ADDR_LIST_MAX_RANGES * GRANULE_SIZE;
	unsigned long handle = create_donate_ctx(xfer, false);
	uintptr_t ns_buf = reserve_granules(1U);

	/*
	 * Start the list 8 bytes (one entry) into the granule.
	 * The maximum number of 8-byte entries that fit without
	 * crossing the granule boundary is ADDR_LIST_MAX_RANGES − 1.
	 */
	uintptr_t list_addr = ns_buf + sizeof(unsigned long);
	unsigned long *list = (unsigned long *)list_addr;
	for (unsigned long i = 0; i < ADDR_LIST_MAX_RANGES - 1UL; i++) {
		uintptr_t fake_addr = ns_buf + i * GRANULE_SIZE;
		list[i] = encode_addr_desc(fake_addr, 1UL,
					   RMI_OP_MEM_DELEGATED);
	}

	struct smc_result res = {};
	smc_op_mem_donate(handle, list_addr, ADDR_LIST_MAX_RANGES, &res);

	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
	/* Maximum entries that fit: ADDR_LIST_MAX_RANGES − 1 */
	CHECK_TRUE(res.x[1] <= (ADDR_LIST_MAX_RANGES - 1UL));

	release_ctx(handle);
}

/* ================================================================
 * smc_op_continue() tests
 * ================================================================
 */

/* ----------------------------------------------------------------
 * TC_CONTINUE_01: Invalid handle → ERROR_INPUT.
 * ----------------------------------------------------------------
 */
TEST(sro_donate_tests, continue_invalid_handle)
{
	struct smc_result res = {};

	smc_op_continue(0xDEADBEEFUL, 0UL, &res);
	CHECK_EQUAL(RMI_ERROR_INPUT, res.x[0]);
}

/* ----------------------------------------------------------------
 * TC_CONTINUE_02: Happy path — handler returns SUCCESS,
 *                 context is released.
 * ----------------------------------------------------------------
 */
TEST(sro_donate_tests, continue_happy_path_success)
{
	sro_handle_cb prev = sro_install_test_handler(SMC_RMI_REC_CREATE,
						      success_cb);
	unsigned long handle = create_continue_ctx(false);

	struct smc_result res = {};
	smc_op_continue(handle, 0UL, &res);
	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);

	/* Context was released — a second find must fail */
	CHECK_FALSE(sro_ctx_find(handle));

	sro_install_test_handler(SMC_RMI_REC_CREATE, prev);
}

/* ----------------------------------------------------------------
 * TC_CONTINUE_03: Handler returns INCOMPLETE with MEM_REQ_DONATE.
 *                 Context remains sealed (not released).
 * ----------------------------------------------------------------
 */
TEST(sro_donate_tests, continue_incomplete_donate_req)
{
	sro_handle_cb prev = sro_install_test_handler(SMC_RMI_REC_CREATE,
						      incomplete_donate_req_cb);
	unsigned long handle = create_continue_ctx(false);

	struct smc_result res = {};
	smc_op_continue(handle, 0UL, &res);

	unsigned long status = unpack_return_code(res.x[0]).status;
	CHECK_EQUAL(RMI_INCOMPLETE, status);

	unsigned long mem_req = EXTRACT(RMI_OP_MEM_REQ, res.x[0]);
	CHECK_EQUAL(RMI_OP_MEM_REQ_DONATE, mem_req);

	/* Context still alive — release it */
	release_ctx(handle);

	sro_install_test_handler(SMC_RMI_REC_CREATE, prev);
}

/* ----------------------------------------------------------------
 * TC_CONTINUE_04: Handler returns INCOMPLETE with MEM_REQ_RECLAIM.
 *                 Context remains sealed; pend_entries are set.
 * ----------------------------------------------------------------
 */
TEST(sro_donate_tests, continue_incomplete_reclaim_req)
{
	g_reclaim_count = 3UL;
	g_reclaim_base = granule_addr(10U);

	sro_handle_cb prev = sro_install_test_handler(SMC_RMI_REC_CREATE,
						      reclaim_entries_cb);
	unsigned long handle = create_continue_ctx(false);

	struct smc_result res = {};
	smc_op_continue(handle, 0UL, &res);

	unsigned long status = unpack_return_code(res.x[0]).status;
	CHECK_EQUAL(RMI_INCOMPLETE, status);

	unsigned long mem_req = EXTRACT(RMI_OP_MEM_REQ, res.x[0]);
	CHECK_EQUAL(RMI_OP_MEM_REQ_RECLAIM, mem_req);

	release_ctx(handle);

	sro_install_test_handler(SMC_RMI_REC_CREATE, prev);
}

/* ----------------------------------------------------------------
 * TC_CONTINUE_05: Wrong FID — send OP_CONTINUE when
 *                 MEM_DONATE is expected.  The handler returns
 *                 RMI_ERROR_INPUT and the context is sealed
 *                 (not released) so the host can retry with
 *                 the correct command.
 * ----------------------------------------------------------------
 */
TEST(sro_donate_tests, continue_wrong_fid_replay)
{
	sro_handle_cb prev = sro_install_test_handler(SMC_RMI_REC_CREATE,
						      incomplete_donate_req_cb);
	unsigned long handle = create_continue_ctx(false);

	/* First call gets INCOMPLETE | MEM_REQ_DONATE */
	struct smc_result res = {};
	smc_op_continue(handle, 0UL, &res);
	CHECK_EQUAL(RMI_INCOMPLETE, unpack_return_code(res.x[0]).status);

	/*
	 * Now the SRO expects MEM_DONATE, but we call OP_CONTINUE
	 * again — wrong FID.  Returns RMI_ERROR_INPUT, context
	 * remains sealed for retry.
	 */
	struct smc_result res2 = {};
	smc_op_continue(handle, 0UL, &res2);

	CHECK_EQUAL(RMI_ERROR_INPUT, res2.x[0]);

	/* Context still sealed — host should retry with correct FID */
	release_ctx(handle);

	sro_install_test_handler(SMC_RMI_REC_CREATE, prev);
}

/* ================================================================
 * smc_op_cancel() tests
 * ================================================================
 */

/* ----------------------------------------------------------------
 * TC_CANCEL_01: Invalid handle → ERROR_INPUT.
 * ----------------------------------------------------------------
 */
TEST(sro_donate_tests, cancel_invalid_handle)
{
	struct smc_result res = {};

	smc_op_cancel(0xDEADBEEFUL, &res);
	CHECK_EQUAL(RMI_ERROR_INPUT, res.x[0]);
}

/* ----------------------------------------------------------------
 * TC_CANCEL_02: can_cancel == false → ERROR_INPUT, context
 *               stays sealed (not released).
 * ----------------------------------------------------------------
 */
TEST(sro_donate_tests, cancel_not_cancellable)
{
	sro_handle_cb prev = sro_install_test_handler(SMC_RMI_REC_CREATE,
						      success_cb);
	/* can_cancel = false */
	unsigned long handle = create_continue_ctx(false);

	struct smc_result res = {};
	smc_op_cancel(handle, &res);
	CHECK_EQUAL(RMI_ERROR_INPUT, res.x[0]);

	/* Context must still exist (sealed, not released) */
	release_ctx(handle);

	sro_install_test_handler(SMC_RMI_REC_CREATE, prev);
}

/* ----------------------------------------------------------------
 * TC_CANCEL_03: can_cancel == true, handler returns SUCCESS →
 *               context is released.
 * ----------------------------------------------------------------
 */
TEST(sro_donate_tests, cancel_happy_path)
{
	sro_handle_cb prev = sro_install_test_handler(SMC_RMI_REC_CREATE,
						      success_cb);
	/* can_cancel = true */
	unsigned long handle = create_continue_ctx(true);

	struct smc_result res = {};
	smc_op_cancel(handle, &res);
	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);

	/* Context was released */
	CHECK_FALSE(sro_ctx_find(handle));

	sro_install_test_handler(SMC_RMI_REC_CREATE, prev);
}

/* ----------------------------------------------------------------
 * TC_CANCEL_04: Cancel bypasses expected-FID check.
 *
 *  Put the context into INCOMPLETE | MEM_REQ_DONATE state
 *  (expected_fid = MEM_DONATE).  Cancel should still succeed
 *  because rmi_op_dispatch does not enforce FID match for cancel.
 * ----------------------------------------------------------------
 */
TEST(sro_donate_tests, cancel_bypasses_expected_fid)
{
	sro_handle_cb prev = sro_install_test_handler(SMC_RMI_REC_CREATE,
						      incomplete_donate_req_cb);
	unsigned long handle = create_continue_ctx(false);

	/* Drive to INCOMPLETE|MEM_DONATE → expected_fid = MEM_DONATE */
	struct smc_result res = {};
	smc_op_continue(handle, 0UL, &res);
	CHECK_EQUAL(RMI_INCOMPLETE, unpack_return_code(res.x[0]).status);

	/*
	 * The INCOMPLETE|DONATE response set can_cancel via the
	 * CAN_CANCEL bit.  Now install the success handler so cancel
	 * returns SUCCESS.
	 */
	sro_install_test_handler(SMC_RMI_REC_CREATE, success_cb);

	struct smc_result cres = {};
	smc_op_cancel(handle, &cres);
	CHECK_EQUAL(RMI_SUCCESS, cres.x[0]);

	/* Context was released */
	CHECK_FALSE(sro_ctx_find(handle));

	sro_install_test_handler(SMC_RMI_REC_CREATE, prev);
}

/* ----------------------------------------------------------------
 * TC_CANCEL_05: Handler returns INCOMPLETE → context is sealed
 *               (not released).
 * ----------------------------------------------------------------
 */
TEST(sro_donate_tests, cancel_handler_returns_incomplete)
{
	sro_handle_cb prev = sro_install_test_handler(SMC_RMI_REC_CREATE,
						      incomplete_cb);
	unsigned long handle = create_continue_ctx(true);

	struct smc_result res = {};
	smc_op_cancel(handle, &res);
	CHECK_EQUAL(RMI_INCOMPLETE, unpack_return_code(res.x[0]).status);

	/* Context must still exist (sealed, not released) */
	release_ctx(handle);

	sro_install_test_handler(SMC_RMI_REC_CREATE, prev);
}

/* ================================================================
 * smc_op_mem_reclaim() tests
 * ================================================================
 */

/* ----------------------------------------------------------------
 * TC_RECLAIM_01: Invalid handle → ERROR_INPUT.
 * ----------------------------------------------------------------
 */
TEST(sro_donate_tests, reclaim_invalid_handle)
{
	uintptr_t ns_buf = reserve_granules(1U);
	struct smc_result res = {};

	smc_op_mem_reclaim(0xDEADBEEFUL, ns_buf, 1UL, &res);
	CHECK_EQUAL(RMI_ERROR_INPUT, res.x[0]);
}

/* ----------------------------------------------------------------
 * TC_RECLAIM_02: Unaligned list_addr → ERROR_INPUT.
 * ----------------------------------------------------------------
 */
TEST(sro_donate_tests, reclaim_unaligned_list_addr)
{
	sro_handle_cb prev = sro_install_test_handler(SMC_RMI_REC_CREATE,
						      success_cb);
	unsigned long handle = create_reclaim_ctx();

	uintptr_t ns_buf = reserve_granules(1U);
	uintptr_t bad_addr = ns_buf + 3UL; /* misaligned */

	struct smc_result res = {};
	smc_op_mem_reclaim(handle, bad_addr, 1UL, &res);
	CHECK_EQUAL(RMI_ERROR_INPUT, res.x[0]);

	release_ctx(handle);
	sro_install_test_handler(SMC_RMI_REC_CREATE, prev);
}

/* ----------------------------------------------------------------
 * TC_RECLAIM_03: Handler produces reclaim entries, host drains
 *                them in a single OP_MEM_RECLAIM call.
 *
 *  The reclaim_entries_cb fills list_buffer and sets pend_entries.
 *  A subsequent smc_op_mem_reclaim copies them to NS memory.
 * ----------------------------------------------------------------
 */
TEST(sro_donate_tests, reclaim_drain_single_batch)
{
	uintptr_t ns_buf = reserve_granules(2U);

	g_reclaim_count = 3UL;
	g_reclaim_base = granule_addr(10U);

	sro_handle_cb prev = sro_install_test_handler(SMC_RMI_REC_CREATE,
						      reclaim_entries_cb);
	unsigned long handle = create_reclaim_ctx();

	/*
	 * First call: handler populates pend_entries = 3 in list_buffer.
	 * smc_op_mem_reclaim dispatches to do_rmi_mem_op which calls the
	 * handler.  Then it notices pend_entries != 0 and copies to NS.
	 */
	struct smc_result res = {};
	smc_op_mem_reclaim(handle, ns_buf, 10UL, &res);

	/* All 3 entries drained in one shot */
	CHECK_EQUAL(3UL, res.x[1]);

	release_ctx(handle);
	sro_install_test_handler(SMC_RMI_REC_CREATE, prev);
}

/* ----------------------------------------------------------------
 * TC_RECLAIM_04: Reclaim with more pend_entries than list_count →
 *                returns INCOMPLETE | MEM_REQ_RECLAIM, memmoves
 *                remaining entries, then second call drains rest.
 * ----------------------------------------------------------------
 */
TEST(sro_donate_tests, reclaim_multi_batch_memmove)
{
	uintptr_t ns_buf = reserve_granules(2U);

	g_reclaim_count = 5UL;
	g_reclaim_base = granule_addr(20U);

	sro_handle_cb prev = sro_install_test_handler(SMC_RMI_REC_CREATE,
						      reclaim_entries_cb);
	unsigned long handle = create_reclaim_ctx();

	/* First call: host requests only 2 entries from 5 pending */
	struct smc_result res = {};
	smc_op_mem_reclaim(handle, ns_buf, 2UL, &res);

	unsigned long status = unpack_return_code(res.x[0]).status;
	CHECK_EQUAL(RMI_INCOMPLETE, status);
	CHECK_EQUAL(2UL, res.x[1]);

	unsigned long mem_req = EXTRACT(RMI_OP_MEM_REQ, res.x[0]);
	CHECK_EQUAL(RMI_OP_MEM_REQ_RECLAIM, mem_req);

	/* Second call: drain the remaining 3 entries */
	struct smc_result res2 = {};
	smc_op_mem_reclaim(handle, ns_buf, 10UL, &res2);
	CHECK_EQUAL(3UL, res2.x[1]);

	release_ctx(handle);
	sro_install_test_handler(SMC_RMI_REC_CREATE, prev);
}

/* ----------------------------------------------------------------
 * TC_RECLAIM_05: Reclaim copy to non-NS granule → ERROR_INPUT.
 *
 *  Pending entries exist but the list_addr points to a delegated
 *  (non-NS) granule, so copy_list_to_ns fails.
 * ----------------------------------------------------------------
 */
TEST(sro_donate_tests, reclaim_copy_to_non_ns_granule)
{
	uintptr_t del_buf = reserve_granules(1U);
	CHECK_TRUE(delegate_range(del_buf, del_buf + GRANULE_SIZE));

	g_reclaim_count = 2UL;
	g_reclaim_base = granule_addr(30U);

	sro_handle_cb prev = sro_install_test_handler(SMC_RMI_REC_CREATE,
						      reclaim_entries_cb);
	unsigned long handle = create_reclaim_ctx();

	/*
	 * First call with a valid NS buffer to trigger the handler
	 * and populate pend_entries.  Request only 1 of 2 so there
	 * are still pending entries.
	 */
	uintptr_t ns_buf = reserve_granules(1U);
	struct smc_result res = {};
	smc_op_mem_reclaim(handle, ns_buf, 1UL, &res);
	CHECK_EQUAL(RMI_INCOMPLETE, unpack_return_code(res.x[0]).status);
	CHECK_EQUAL(1UL, res.x[1]);

	/* Second call: target buffer is delegated → copy fails */
	struct smc_result res2 = {};
	smc_op_mem_reclaim(handle, del_buf, 1UL, &res2);
	CHECK_EQUAL(RMI_ERROR_INPUT, res2.x[0]);
	CHECK_EQUAL(0UL, res2.x[1]);

	release_ctx(handle);
	sro_install_test_handler(SMC_RMI_REC_CREATE, prev);
}

/* ----------------------------------------------------------------
 * TC_RECLAIM_06: list_count clamped to ADDR_LIST_MAX_RANGES.
 *
 *  Pass a huge list_count to smc_op_mem_reclaim; verify it
 *  is silently capped and does not cause OOB access.
 * ----------------------------------------------------------------
 */
TEST(sro_donate_tests, reclaim_list_count_clamped)
{
	uintptr_t ns_buf = reserve_granules(1U);

	g_reclaim_count = 4UL;
	g_reclaim_base = granule_addr(40U);

	sro_handle_cb prev = sro_install_test_handler(SMC_RMI_REC_CREATE,
						      reclaim_entries_cb);
	unsigned long handle = create_reclaim_ctx();

	struct smc_result res = {};
	smc_op_mem_reclaim(handle, ns_buf, ADDR_LIST_MAX_RANGES + 100UL,
			   &res);

	/* Should drain all 4 entries (list_count capped ≥ 4) */
	CHECK_EQUAL(4UL, res.x[1]);

	release_ctx(handle);
	sro_install_test_handler(SMC_RMI_REC_CREATE, prev);
}

/* ----------------------------------------------------------------
 * TC_RECLAIM_07: Reclaim when context expects
 *               MEM_DONATE returns RMI_ERROR_INPUT.
 * ----------------------------------------------------------------
 */
TEST(sro_donate_tests, reclaim_zero_list_count_wrong_fid)
{
	sro_handle_cb prev = sro_install_test_handler(SMC_RMI_REC_CREATE,
						      incomplete_donate_req_cb);
	unsigned long handle = create_continue_ctx(false);

	/* CONTINUE → INCOMPLETE | MEM_REQ_DONATE */
	struct smc_result res = {};
	smc_op_continue(handle, 0UL, &res);
	CHECK_EQUAL(RMI_INCOMPLETE, unpack_return_code(res.x[0]).status);
	CHECK_EQUAL(RMI_OP_MEM_REQ_DONATE,
		    EXTRACT(RMI_OP_MEM_REQ, res.x[0]));

	/* Now send MEM_RECLAIM (wrong FID) */
	uintptr_t ns_buf = reserve_granules(1U);
	struct smc_result rres = {};
	smc_op_mem_reclaim(handle, ns_buf, 0UL, &rres);

	/* Wrong FID → RMI_ERROR_INPUT */
	CHECK_EQUAL(RMI_ERROR_INPUT, rres.x[0]);

	release_ctx(handle);
	sro_install_test_handler(SMC_RMI_REC_CREATE, prev);
}

/* ================================================================
 * Full SRO flow integration tests
 * ================================================================
 */


/*
 * Per-test call counters for flow integration callbacks.
 * Static so they are accessible from named callback functions below.
 */
static int g_flow_donate_cnt;
static int g_flow_reclaim_cnt;
static int g_flow_cancel_cnt;
static int g_flow_l2_cnt;

/* Callback for flow_donate_continue_success */
static void flow_donate_phase_cb(unsigned long fid, struct smc_result *res)
{
	(void)fid;
	g_flow_donate_cnt++;
	if (g_flow_donate_cnt == 1) {
		/* First continue → request donation */
		res->x[0] = RMI_INCOMPLETE |
			    INPLACE(RMI_OP_MEM_REQ, RMI_OP_MEM_REQ_DONATE) |
			    INPLACE(RMI_OP_CAN_CANCEL_BIT, RMI_OP_CAN_CANCEL);
		res->x[1] = 0UL;
		res->x[2] = INPLACE(RMI_OP_DONATE_BLK_SIZE, RMI_PAGE_L3) |
			    INPLACE(RMI_OP_DONATE_BLK_COUNT, 1UL);
	} else if (g_flow_donate_cnt == 2) {
		/* Donate received → accept */
		res->x[0] = RMI_SUCCESS;
		res->x[1] = my_sro_ctx()->addr_list.count;
	} else {
		/* Final continue → done */
		res->x[0] = RMI_SUCCESS;
	}
}

/* Callback for flow_reclaim_continue_success */
static void flow_reclaim_phase_cb(unsigned long fid, struct smc_result *res)
{
	(void)fid;
	g_flow_reclaim_cnt++;
	if (g_flow_reclaim_cnt == 1) {
		/*
		 * First continue → request reclaim.
		 * Do NOT populate entries yet; the real handler
		 * only returns the request here.
		 */
		res->x[0] = RMI_INCOMPLETE |
			    INPLACE(RMI_OP_MEM_REQ, RMI_OP_MEM_REQ_RECLAIM) |
			    INPLACE(RMI_OP_CAN_CANCEL_BIT, RMI_OP_CAN_CANCEL);
		res->x[1] = 0UL;
	} else if (g_flow_reclaim_cnt == 2) {
		/*
		 * MEM_RECLAIM dispatch → populate entries.
		 * Use non-contiguous addresses to prevent
		 * merging into a single descriptor.
		 * All 4 entries fit in one batch so return
		 * MEM_REQ_NONE (like the real handler).
		 */
		struct sro_context *sro = my_sro_ctx();

		addr_list_add_block(&sro->addr_list,
			granule_addr(50U), 3U, RMI_OP_MEM_DELEGATED);
		addr_list_add_block(&sro->addr_list,
			granule_addr(60U), 3U, RMI_OP_MEM_DELEGATED);
		addr_list_add_block(&sro->addr_list,
			granule_addr(70U), 3U, RMI_OP_MEM_DELEGATED);
		addr_list_add_block(&sro->addr_list,
			granule_addr(80U), 3U, RMI_OP_MEM_DELEGATED);
		res->x[0] = RMI_INCOMPLETE |
			    INPLACE(RMI_OP_MEM_REQ, RMI_OP_MEM_REQ_NONE) |
			    INPLACE(RMI_OP_CAN_CANCEL_BIT, RMI_OP_CAN_CANCEL);
		res->x[1] = 4UL;
	} else {
		/* CONTINUE after drain → done */
		res->x[0] = RMI_SUCCESS;
	}
}

/* Callback for flow_cancel_mid_donate */
static void flow_cancel_phase_cb(unsigned long fid, struct smc_result *res)
{
	(void)fid;
	g_flow_cancel_cnt++;
	if (g_flow_cancel_cnt == 1) {
		/* Continue → request donation */
		res->x[0] = RMI_INCOMPLETE |
			    INPLACE(RMI_OP_MEM_REQ, RMI_OP_MEM_REQ_DONATE) |
			    INPLACE(RMI_OP_CAN_CANCEL_BIT, RMI_OP_CAN_CANCEL);
		res->x[1] = 0UL;
		res->x[2] = INPLACE(RMI_OP_DONATE_BLK_SIZE, RMI_PAGE_L3) |
			    INPLACE(RMI_OP_DONATE_BLK_COUNT, 1UL);
	} else {
		/* Cancel handler → done */
		res->x[0] = RMI_SUCCESS;
	}
}

/* Callback for flow_l2_block_donate_and_reclaim */
static void flow_l2_phase_cb(unsigned long fid, struct smc_result *res)
{
	(void)fid;
	g_flow_l2_cnt++;
	if (g_flow_l2_cnt == 1) {
		/*
		 * First continue → request donation:
		 * 1 × L2 block, non-contiguous, delegate state.
		 */
		res->x[0] = RMI_INCOMPLETE |
			    INPLACE(RMI_OP_MEM_REQ, RMI_OP_MEM_REQ_DONATE) |
			    INPLACE(RMI_OP_CAN_CANCEL_BIT, RMI_OP_CAN_CANCEL);
		res->x[1] = 0UL;
		res->x[2] = INPLACE(RMI_OP_DONATE_BLK_SIZE, RMI_BLOCK_L2) |
			    INPLACE(RMI_OP_DONATE_BLK_COUNT, 1UL) |
			    INPLACE(RMI_OP_DONATE_MEM_CONTIG, RMI_OP_MEM_NON_CONTIG);
	} else if (g_flow_l2_cnt == 2) {
		/*
		 * Donate accepted → request reclaim.
		 * Do NOT populate entries; the real handler
		 * returns MEM_REQ_RECLAIM here without entries.
		 */
		res->x[0] = RMI_INCOMPLETE |
			    INPLACE(RMI_OP_MEM_REQ, RMI_OP_MEM_REQ_RECLAIM) |
			    INPLACE(RMI_OP_CAN_CANCEL_BIT, RMI_OP_CAN_CANCEL);
		res->x[1] = my_sro_ctx()->addr_list.count;
	} else if (g_flow_l2_cnt == 3) {
		/*
		 * MEM_RECLAIM dispatch → populate a single
		 * reclaim entry.  All entries fit so return
		 * MEM_REQ_NONE (like the real handler).
		 */
		struct sro_context *sro = my_sro_ctx();

		addr_list_add_block(&sro->addr_list,
			granule_addr(100U), 3U, RMI_OP_MEM_DELEGATED);
		res->x[0] = RMI_INCOMPLETE |
			    INPLACE(RMI_OP_MEM_REQ, RMI_OP_MEM_REQ_NONE) |
			    INPLACE(RMI_OP_CAN_CANCEL_BIT, RMI_OP_CAN_CANCEL);
		res->x[1] = 1UL;
	} else {
		/* CONTINUE after drain → done */
		res->x[0] = RMI_SUCCESS;
	}
}

/* ----------------------------------------------------------------
 * TC_FLOW_01: Full donate flow — CONTINUE → INCOMPLETE|DONATE →
 *             MEM_DONATE → CONTINUE → SUCCESS.
 *
 *  Models the programming model from the spec:
 *    result = RMI_OP_CONTINUE(handle)
 *    if result.mem == DONATE: result = donate_mem(...)
 *    result = RMI_OP_CONTINUE(handle)
 *    → SUCCESS → done
 * ----------------------------------------------------------------
 */
TEST(sro_donate_tests, flow_donate_continue_success)
{
	g_flow_donate_cnt = 0;

	sro_handle_cb prev = sro_install_test_handler(SMC_RMI_REC_CREATE,
						      flow_donate_phase_cb);
	unsigned long handle = create_continue_ctx(false);

	/* Phase 1: CONTINUE → INCOMPLETE | MEM_REQ_DONATE */
	struct smc_result res = {};
	smc_op_continue(handle, 0UL, &res);
	CHECK_EQUAL(RMI_INCOMPLETE, unpack_return_code(res.x[0]).status);
	CHECK_EQUAL(RMI_OP_MEM_REQ_DONATE,
		    EXTRACT(RMI_OP_MEM_REQ, res.x[0]));

	/* Phase 2: MEM_DONATE */
	uintptr_t ns_buf = reserve_granules(1U);
	uintptr_t donor = reserve_granules(1U);
	CHECK_TRUE(delegate_range(donor, donor + GRANULE_SIZE));

	unsigned long *list = (unsigned long *)ns_buf;
	list[0] = encode_addr_desc(donor, 1UL, RMI_OP_MEM_DELEGATED);

	struct smc_result dres = {};
	smc_op_mem_donate(handle, ns_buf, 1UL, &dres);
	CHECK_EQUAL(RMI_SUCCESS, dres.x[0]);

	/* Phase 3: CONTINUE → SUCCESS, context released */
	struct smc_result fres = {};
	smc_op_continue(handle, 0UL, &fres);
	CHECK_EQUAL(RMI_SUCCESS, fres.x[0]);

	/* Context released */
	CHECK_FALSE(sro_ctx_find(handle));

	sro_install_test_handler(SMC_RMI_REC_CREATE, prev);
}

/* ----------------------------------------------------------------
 * TC_FLOW_02: Full reclaim flow — CONTINUE → INCOMPLETE|RECLAIM →
 *             MEM_RECLAIM (multi-batch) → CONTINUE → SUCCESS.
 *
 *  After reclaim entries are drained, expected_fid reverts to
 *  CONTINUE so the host finishes with OP_CONTINUE → SUCCESS.
 * ----------------------------------------------------------------
 */
TEST(sro_donate_tests, flow_reclaim_continue_success)
{
	g_flow_reclaim_cnt = 0;

	sro_handle_cb prev = sro_install_test_handler(SMC_RMI_REC_CREATE,
						      flow_reclaim_phase_cb);
	unsigned long handle = create_continue_ctx(false);

	/* Phase 1: CONTINUE → INCOMPLETE | MEM_REQ_RECLAIM */
	struct smc_result res = {};
	smc_op_continue(handle, 0UL, &res);
	CHECK_EQUAL(RMI_INCOMPLETE, unpack_return_code(res.x[0]).status);
	CHECK_EQUAL(RMI_OP_MEM_REQ_RECLAIM,
		    EXTRACT(RMI_OP_MEM_REQ, res.x[0]));

	/* Phase 2: MEM_RECLAIM batch 1 (2 of 4 entries) */
	uintptr_t ns_buf = reserve_granules(1U);
	struct smc_result rres = {};
	smc_op_mem_reclaim(handle, ns_buf, 2UL, &rres);
	CHECK_EQUAL(RMI_INCOMPLETE, unpack_return_code(rres.x[0]).status);
	CHECK_EQUAL(RMI_OP_MEM_REQ_RECLAIM,
		    EXTRACT(RMI_OP_MEM_REQ, rres.x[0]));
	CHECK_EQUAL(2UL, rres.x[1]);

	/* Phase 2 continued: MEM_RECLAIM batch 2 (remaining 2 entries) */
	struct smc_result rres2 = {};
	smc_op_mem_reclaim(handle, ns_buf, 10UL, &rres2);
	CHECK_EQUAL(RMI_INCOMPLETE, unpack_return_code(rres2.x[0]).status);
	CHECK_EQUAL(RMI_OP_MEM_REQ_NONE,
		    EXTRACT(RMI_OP_MEM_REQ, rres2.x[0]));
	CHECK_EQUAL(2UL, rres2.x[1]);

	/* Phase 3: All entries drained → CONTINUE → SUCCESS */
	struct smc_result fres = {};
	smc_op_continue(handle, 0UL, &fres);
	CHECK_EQUAL(RMI_SUCCESS, fres.x[0]);

	CHECK_FALSE(sro_ctx_find(handle));

	sro_install_test_handler(SMC_RMI_REC_CREATE, prev);
}

/* ----------------------------------------------------------------
 * TC_FLOW_03: Cancel mid-flow — CONTINUE → INCOMPLETE|DONATE →
 *             OP_CANCEL → SUCCESS.
 *
 *  Models the cancel path from the spec programming model.
 * ----------------------------------------------------------------
 */
TEST(sro_donate_tests, flow_cancel_mid_donate)
{
	g_flow_cancel_cnt = 0;

	sro_handle_cb prev = sro_install_test_handler(SMC_RMI_REC_CREATE,
						      flow_cancel_phase_cb);
	/* can_cancel = true */
	unsigned long handle = create_continue_ctx(true);

	/* Phase 1: CONTINUE → INCOMPLETE | MEM_REQ_DONATE */
	struct smc_result res = {};
	smc_op_continue(handle, 0UL, &res);
	CHECK_EQUAL(RMI_INCOMPLETE, unpack_return_code(res.x[0]).status);

	/* Host decides to cancel instead of donating */
	struct smc_result cres = {};
	smc_op_cancel(handle, &cres);
	CHECK_EQUAL(RMI_SUCCESS, cres.x[0]);

	/* Context released */
	CHECK_FALSE(sro_ctx_find(handle));

	sro_install_test_handler(SMC_RMI_REC_CREATE, prev);
}

/* ================================================================
 * L2-block / max-block-count donation and reclaim tests
 * ================================================================
 */

/* ----------------------------------------------------------------
 * TC_FLOW_04: Donate 512 L3 granules as a single L2 block
 *             descriptor, followed by reclaim.
 *
 *  The SRO callback requests 1 × L2 block (2 MB = 512 × L3).
 *  The host satisfies this with a single L2 descriptor (cnt=1,
 *  blk_sz=RMI_BLOCK_L2).  After donation the callback returns
 *  INCOMPLETE | MEM_REQ_RECLAIM with 1 reclaim entry, which the
 *  host drains via MEM_RECLAIM, then CONTINUE → SUCCESS.
 * ----------------------------------------------------------------
 */
TEST(sro_donate_tests, flow_l2_block_donate_and_reclaim)
{
	g_flow_l2_cnt = 0;

	/*
	 * L2 block size = XLAT_BLOCK_SIZE(2) = 2 MB.
	 * In the 4K-granule descriptor format, SZ=1 → L2.
	 */
	const unsigned long l2_blk_sz_enc = RMI_BLOCK_L2;
	const unsigned long l2_block_size =
		XLAT_BLOCK_SIZE((int)(XLAT_TABLE_LEVEL_MAX -
				      (int)l2_blk_sz_enc));

	sro_handle_cb prev = sro_install_test_handler(SMC_RMI_REC_CREATE,
						      flow_l2_phase_cb);
	unsigned long handle = create_continue_ctx(false);

	/* Phase 1: CONTINUE → INCOMPLETE | MEM_REQ_DONATE */
	struct smc_result res = {};
	smc_op_continue(handle, 0UL, &res);
	CHECK_EQUAL(RMI_INCOMPLETE, unpack_return_code(res.x[0]).status);
	CHECK_EQUAL(RMI_OP_MEM_REQ_DONATE,
		    EXTRACT(RMI_OP_MEM_REQ, res.x[0]));

	/* Verify the requested block params in res.x[2] */
	CHECK_EQUAL(RMI_BLOCK_L2,
		    EXTRACT(RMI_OP_DONATE_BLK_SIZE, res.x[2]));
	CHECK_EQUAL(1UL,
		    EXTRACT(RMI_OP_DONATE_BLK_COUNT, res.x[2]));

	/*
	 * Phase 2: MEM_DONATE — supply a single L2 descriptor.
	 * Need a 2 MB-aligned range of 512 granules.  Reserve extra
	 * granules to guarantee alignment.
	 */
	uintptr_t ns_buf = reserve_granules(1U);
	unsigned int l2_granules = (unsigned int)(l2_block_size / GRANULE_SIZE);
	uintptr_t pool = reserve_granules(2U * l2_granules);
	uintptr_t donor = round_up(pool, l2_block_size);
	CHECK_TRUE(ALIGNED(donor, l2_block_size));
	CHECK_TRUE(delegate_range(donor, donor + l2_block_size));

	unsigned long *list = (unsigned long *)ns_buf;
	list[0] = encode_addr_desc_blk(donor, 1UL,
				       RMI_OP_MEM_DELEGATED, l2_blk_sz_enc);

	struct smc_result dres = {};
	smc_op_mem_donate(handle, ns_buf, 1UL, &dres);
	CHECK_EQUAL(RMI_INCOMPLETE, unpack_return_code(dres.x[0]).status);
	CHECK_EQUAL(RMI_OP_MEM_REQ_RECLAIM,
		    EXTRACT(RMI_OP_MEM_REQ, dres.x[0]));

	/* Phase 3: MEM_RECLAIM — drain the single reclaim entry */
	struct smc_result rres = {};
	smc_op_mem_reclaim(handle, ns_buf, 10UL, &rres);
	CHECK_EQUAL(1UL, rres.x[1]);

	/* Phase 4: All entries drained → CONTINUE → SUCCESS */
	struct smc_result fres = {};
	smc_op_continue(handle, 0UL, &fres);
	CHECK_EQUAL(RMI_SUCCESS, fres.x[0]);

	CHECK_FALSE(sro_ctx_find(handle));

	sro_install_test_handler(SMC_RMI_REC_CREATE, prev);
}

/* ----------------------------------------------------------------
 * TC_DONATE_MAX_BLK: Donate a single descriptor with the maximum
 *                    block count (1023 × L3 = 1023 × 4K) → SUCCESS.
 *
 *  Verifies that the addr_list validator accepts descriptors at
 *  the maximum allowed count boundary.
 * ----------------------------------------------------------------
 */
TEST(sro_donate_tests, donate_max_block_count)
{
	unsigned long max_cnt =
		(1UL << RMI_ADDR_RDESC_4K_CNT_WIDTH) - 1UL; /* 1023 */
	unsigned long total_size = max_cnt * GRANULE_SIZE;
	unsigned long handle = create_donate_ctx(total_size, false);
	uintptr_t ns_buf = reserve_granules(1U);

	unsigned long *list = (unsigned long *)ns_buf;
	list[0] = encode_addr_desc(ns_buf, max_cnt, RMI_OP_MEM_DELEGATED);

	struct smc_result res = {};
	smc_op_mem_donate(handle, ns_buf, 1UL, &res);
	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);

	release_ctx(handle);
}

/* ----------------------------------------------------------------
 * TC_DONATE_MAX_BLK_PLUS_ONE: Donate a descriptor whose block
 *                             count exceeds the 10-bit field
 *                             maximum → handled gracefully.
 *
 *  Encode CNT = max_cnt + 1 = 1024.  The 10-bit CNT field
 *  (RMI_ADDR_RDESC_4K_CNT_WIDTH = 10) truncates 1024 → 0.
 *  A zero-count entry is silently skipped during validation,
 *  so the donate succeeds with total_mem = 0 (no memory
 *  actually transferred).
 * ----------------------------------------------------------------
 */
TEST(sro_donate_tests, donate_max_block_count_plus_one_wraps)
{
	unsigned long max_cnt =
		(1UL << RMI_ADDR_RDESC_4K_CNT_WIDTH) - 1UL; /* 1023 */
	unsigned long total_size = GRANULE_SIZE; /* small enough */
	unsigned long handle = create_donate_ctx(total_size, false);
	uintptr_t ns_buf = reserve_granules(1U);

	unsigned long *list = (unsigned long *)ns_buf;
	/*
	 * max_cnt + 1 = 1024, which overflows the 10-bit CNT field to 0.
	 * INPLACE does not mask, so we must mask the count ourselves
	 * to avoid corrupting adjacent descriptor fields.
	 */
	unsigned long cnt_mask = (1UL << RMI_ADDR_RDESC_4K_CNT_WIDTH) - 1UL;

	list[0] = encode_addr_desc(ns_buf, (max_cnt + 1UL) & cnt_mask,
				   RMI_OP_MEM_DELEGATED);

	struct smc_result res = {};
	smc_op_mem_donate(handle, ns_buf, 1UL, &res);
	/*
	 * The entry has CNT=0 after truncation, so it is skipped.
	 * total_mem = 0 ≤ transfer_req, validation passes.
	 */
	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);

	release_ctx(handle);
}
