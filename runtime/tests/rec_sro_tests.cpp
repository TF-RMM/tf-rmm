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
#include <rec.h>
#include <smc-handler.h>
#include <smc-rmi.h>
#include <smc.h>
#include <sro_context.h>
#include <status.h>
#include <stdlib.h>
#include <string.h>
#include <test_helpers.h>
#include <utils_def.h>
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

struct test_realm {
	uintptr_t rd;
	uintptr_t rec;
	uintptr_t rec_params;
	uintptr_t addr_list;  /* NS granule for address descriptor list */
};

/*
 * Set up a minimal test context. We do NOT call smc_realm_create because
 * it triggers attestation hashing that requires the EL0 app context
 * (unavailable in CppUTest). smc_rec_create only reserves an SRO context
 * and stores addresses — it does not validate them until the CONTINUE
 * phase — so arbitrary addresses suffice for testing the donation flow.
 */
static bool create_test_context(struct test_realm *r)
{
	r->rd = reserve_granules(1);
	r->rec = reserve_granules(1);
	r->rec_params = reserve_granules(1);
	r->addr_list = reserve_granules(1);

	/* smc_rec_create requires the rec granule to be DELEGATED */
	if (!delegate_range(r->rec, r->rec + GRANULE_SIZE)) {
		return false;
	}

	return true;
}

/*
 * Initiate RMI_REC_CREATE which returns INCOMPLETE requesting aux donation.
 * Returns the SRO handle and donate_req on success.
 */
static bool initiate_rec_create(struct test_realm *r,
				unsigned long *handle,
				unsigned long *donate_req)
{
	struct smc_result res = {};

	smc_rec_create(r->rd, r->rec, r->rec_params, &res);

	return_code_t rc = unpack_return_code(res.x[0]);
	if (rc.status != RMI_INCOMPLETE) {
		return false;
	}

	unsigned long mem_req = EXTRACT(RMI_OP_MEM_REQ, res.x[0]);
	if (mem_req != RMI_OP_MEM_REQ_DONATE) {
		return false;
	}

	*handle = res.x[1];
	*donate_req = res.x[2];
	return true;
}

/* ================================================================
 * Test Group
 * ================================================================
 */
TEST_GROUP(rec_sro_tests) {
	TEST_SETUP()
	{
		test_helpers_init();
		test_helpers_rmm_start(false);
		host_util_set_cpuid(0U);
		test_helpers_expect_assert_fail(false);

		/*
		 * Do NOT reset g_next_idx between tests.
		 * Granule states persist across tests (delegate is
		 * permanent), so each test must use fresh granules.
		 * The first test initialises the index on first use.
		 */
	}
	TEST_TEARDOWN()
	{
	}
};

/*
 * TC1: Happy path - donate exactly MAX_REC_AUX_GRANULES with CNT=1.
 *      The donation phase should complete and request OP_CONTINUE.
 *      We do not invoke OP_CONTINUE because the continuation path
 *      calls into attestation code that requires EL0 app context.
 */
TEST(rec_sro_tests, rec_create_sro_happy_path)
{
	struct test_realm realm;

	CHECK_TRUE(create_test_context(&realm));

	unsigned long handle = 0, donate_req = 0;
	CHECK_TRUE(initiate_rec_create(&realm, &handle, &donate_req));

	/* Verify L3 page size and read the count RMM actually requests */
	CHECK_EQUAL(RMI_PAGE_L3,
		    (unsigned long)EXTRACT(RMI_OP_DONATE_BLK_SIZE, donate_req));
	unsigned long requested_count = EXTRACT(RMI_OP_DONATE_BLK_COUNT, donate_req);
	CHECK_TRUE(requested_count > 0UL);

	/* Allocate and delegate the number of aux granules RMM asked for */
	uintptr_t aux_base = reserve_granules((unsigned int)requested_count);
	CHECK_TRUE(delegate_range(aux_base,
				  aux_base + requested_count * GRANULE_SIZE));

	/* Donate all aux granules in one batch */
	unsigned long *addr_list = (unsigned long *)realm.addr_list;
	for (unsigned long i = 0; i < requested_count; i++) {
		addr_list[i] = encode_addr_desc(
			aux_base + (i * GRANULE_SIZE),
			1UL, RMI_OP_MEM_DELEGATED);
	}

	struct smc_result res = {};
	smc_op_mem_donate(handle, realm.addr_list, requested_count, &res);

	return_code_t rc = unpack_return_code(res.x[0]);
	CHECK_EQUAL(RMI_INCOMPLETE, rc.status);

	/* All consumed */
	CHECK_EQUAL(requested_count, res.x[1]);

	/* Should now request OP_CONTINUE (MEM_REQ_NONE) */
	unsigned long mem_req = EXTRACT(RMI_OP_MEM_REQ, res.x[0]);
	CHECK_EQUAL(RMI_OP_MEM_REQ_NONE, mem_req);
}

/*
 * TC2: Submit more descriptors than MAX_REC_AUX_GRANULES
 *      with CNT=0. Zero-count entries are silently skipped by RMM,
 *      so no granules are donated. RMM returns INCOMPLETE requesting
 *      another DONATE round with the full count still pending.
 */
TEST(rec_sro_tests, rec_create_sro_zero_count_oob)
{
	struct test_realm realm;

	CHECK_TRUE(create_test_context(&realm));

	unsigned long handle = 0, donate_req = 0;
	CHECK_TRUE(initiate_rec_create(&realm, &handle, &donate_req));

	unsigned long requested_count = EXTRACT(RMI_OP_DONATE_BLK_COUNT, donate_req);
	/* Prepare more zero-count descriptors than RMM requested */
	unsigned long oob_count = requested_count + 3UL;
	uintptr_t extra_base = reserve_granules((unsigned int)oob_count);
	CHECK_TRUE(delegate_range(extra_base,
				  extra_base + oob_count * GRANULE_SIZE));

	unsigned long *addr_list = (unsigned long *)realm.addr_list;
	for (unsigned long i = 0; i < oob_count; i++) {
		/* CNT=0: addr_list_validate skips these entries */
		addr_list[i] = encode_addr_desc(
			extra_base + (i * GRANULE_SIZE),
			0UL, RMI_OP_MEM_DELEGATED);
	}

	struct smc_result res = {};
	smc_op_mem_donate(handle, realm.addr_list, oob_count, &res);

	/*
	 * All entries are zero-count so no granules are donated.
	 * RMM returns INCOMPLETE requesting more memory (full count
	 * still pending), and consumed count is 0.
	 */
	return_code_t rc = unpack_return_code(res.x[0]);
	CHECK_EQUAL(RMI_INCOMPLETE, rc.status);
	unsigned long mem_req = EXTRACT(RMI_OP_MEM_REQ, res.x[0]);
	CHECK_EQUAL(RMI_OP_MEM_REQ_DONATE, mem_req);
	CHECK_EQUAL(0UL, res.x[1]); /* nothing consumed */
	unsigned long pending = EXTRACT(RMI_OP_DONATE_BLK_COUNT, res.x[2]);
	CHECK_EQUAL(requested_count, pending);
}

/*
 * TC3: Submit a mix of valid (CNT=1) and zero-count (CNT=0) entries.
 *      Zero-count entries are silently skipped, so only the valid
 *      entries contribute granules. With the last entry zero-count
 *      the donation comes up one short, and RMM requests 1 more via
 *      DONATE.
 */
TEST(rec_sro_tests, rec_create_sro_mixed_zero_and_valid_count)
{
	struct test_realm realm;

	CHECK_TRUE(create_test_context(&realm));

	unsigned long handle = 0, donate_req = 0;
	CHECK_TRUE(initiate_rec_create(&realm, &handle, &donate_req));

	/* Build a list: some valid, one zero-count */
	unsigned long list_count = EXTRACT(RMI_OP_DONATE_BLK_COUNT, donate_req);
	CHECK_TRUE(list_count >= 2UL);
	uintptr_t aux_base = reserve_granules((unsigned int)list_count);
	CHECK_TRUE(delegate_range(aux_base,
				  aux_base + list_count * GRANULE_SIZE));

	unsigned long *addr_list = (unsigned long *)realm.addr_list;
	for (unsigned long i = 0; i < list_count; i++) {
		/* Make the last entry have CNT=0 */
		unsigned long cnt = (i == list_count - 1) ? 0UL : 1UL;
		addr_list[i] = encode_addr_desc(
			aux_base + (i * GRANULE_SIZE),
			cnt, RMI_OP_MEM_DELEGATED);
	}

	struct smc_result res = {};
	smc_op_mem_donate(handle, realm.addr_list, list_count, &res);

	/*
	 * (list_count - 1) granules donated; the zero-count last entry is
	 * skipped. One granule still needed -> INCOMPLETE + DONATE.
	 */
	return_code_t rc = unpack_return_code(res.x[0]);
	CHECK_EQUAL(RMI_INCOMPLETE, rc.status);
	unsigned long mem_req = EXTRACT(RMI_OP_MEM_REQ, res.x[0]);
	CHECK_EQUAL(RMI_OP_MEM_REQ_DONATE, mem_req);
	CHECK_EQUAL(list_count - 1UL, res.x[1]); /* consumed */
	unsigned long pending = EXTRACT(RMI_OP_DONATE_BLK_COUNT, res.x[2]);
	CHECK_EQUAL(1UL, pending);
}

/*
 * TC4: Donate more total memory than requested (transfer_req exceeded).
 *      Each entry has CNT=2, so each descriptor covers 2 * GRANULE_SIZE.
 *      Submitting as many entries as RMM requested doubles the total
 *      memory transferred, exceeding transfer_req.
 */
TEST(rec_sro_tests, rec_create_sro_transfer_exceeds_request)
{
	struct test_realm realm;

	CHECK_TRUE(create_test_context(&realm));

	unsigned long handle = 0, donate_req = 0;
	CHECK_TRUE(initiate_rec_create(&realm, &handle, &donate_req));

	unsigned long list_count = EXTRACT(RMI_OP_DONATE_BLK_COUNT, donate_req);
	uintptr_t aux_base = reserve_granules((unsigned int)list_count);
	CHECK_TRUE(delegate_range(aux_base,
				  aux_base + list_count * GRANULE_SIZE));

	unsigned long *addr_list = (unsigned long *)realm.addr_list;
	for (unsigned long i = 0; i < list_count; i++) {
		/* CNT=2 makes each entry contribute 2 * GRANULE_SIZE */
		addr_list[i] = encode_addr_desc(
			aux_base + (i * GRANULE_SIZE),
			2UL, RMI_OP_MEM_DELEGATED);
	}

	struct smc_result res = {};
	smc_op_mem_donate(handle, realm.addr_list, list_count, &res);

	return_code_t rc = unpack_return_code(res.x[0]);
	CHECK_EQUAL(RMI_ERROR_INPUT, rc.status);
}

/*
 * TC5: First donated granule is not in delegated but the range describes it
 *      as delegated. RMM should detect this mismatch and trigger reclaim
 *      and return error.
 */
TEST(rec_sro_tests, rec_create_sro_first_granule_not_delegated)
{
	struct test_realm realm;

	CHECK_TRUE(create_test_context(&realm));

	unsigned long handle = 0, donate_req = 0;
	CHECK_TRUE(initiate_rec_create(&realm, &handle, &donate_req));

	unsigned long requested_count = EXTRACT(RMI_OP_DONATE_BLK_COUNT, donate_req);
	/* Reserve granules but do NOT delegate them */
	uintptr_t aux_base = reserve_granules((unsigned int)requested_count);

	unsigned long *addr_list = (unsigned long *)realm.addr_list;
	for (unsigned long i = 0; i < requested_count; i++) {
		addr_list[i] = encode_addr_desc(
			aux_base + (i * GRANULE_SIZE),
			1UL, RMI_OP_MEM_DELEGATED);
	}

	struct smc_result res = {};
	smc_op_mem_donate(handle, realm.addr_list, requested_count, &res);

	/*
	 * The first granule is NS (not delegated), so rec_create_request_aux_mem
	 * should call rec_start_memory_reclaim -> return INCOMPLETE with RECLAIM.
	 */
	return_code_t rc = unpack_return_code(res.x[0]);
	CHECK_EQUAL(RMI_INCOMPLETE, rc.status);
	unsigned long mem_req = EXTRACT(RMI_OP_MEM_REQ, res.x[0]);
	CHECK_EQUAL(RMI_OP_MEM_REQ_RECLAIM, mem_req);
}

/*
 * TC5b: A middle (non-first) entry in the donation list is not in delegated
 *       state. RMM partially accepts entries 0..k-1, stops at entry k, and
 *       requests more granules via DONATE. The subsequent batch then starts
 *       with a non-delegated granule, causing rec_create_request_aux_mem to
 *       call rec_start_memory_reclaim -> INCOMPLETE + RECLAIM.
 */
TEST(rec_sro_tests, rec_create_sro_middle_granule_not_delegated)
{
	struct test_realm realm;

	CHECK_TRUE(create_test_context(&realm));

	unsigned long handle = 0, donate_req = 0;
	CHECK_TRUE(initiate_rec_create(&realm, &handle, &donate_req));

	unsigned long requested_count = EXTRACT(RMI_OP_DONATE_BLK_COUNT, donate_req);
	/* Need at least 2 entries to have a non-first bad entry */
	CHECK_TRUE(requested_count >= 2UL);

	/*
	 * Allocate requested_count granules. Delegate entry 0 but leave
	 * entry 1 (the "middle" entry) in NS state. Entries 2+ are also
	 * delegated so that they can be used in follow-up donations if
	 * requested_count > 2.
	 */
	uintptr_t aux_base = reserve_granules((unsigned int)requested_count);
	CHECK_TRUE(delegate_range(aux_base, aux_base + GRANULE_SIZE));
	/* skip index 1 (leave NS) */
	if (requested_count > 2UL) {
		CHECK_TRUE(delegate_range(aux_base + 2UL * GRANULE_SIZE,
					  aux_base + requested_count * GRANULE_SIZE));
	}

	unsigned long *addr_list = (unsigned long *)realm.addr_list;
	for (unsigned long i = 0; i < requested_count; i++) {
		addr_list[i] = encode_addr_desc(
			aux_base + (i * GRANULE_SIZE),
			1UL, RMI_OP_MEM_DELEGATED);
	}

	struct smc_result res = {};
	smc_op_mem_donate(handle, realm.addr_list, requested_count, &res);

	/*
	 * Entry 0 is donated; the loop stops at entry 1 (NS). RMM stores
	 * total_transferred=1 and requests the remaining entries via DONATE.
	 */
	return_code_t rc = unpack_return_code(res.x[0]);
	CHECK_EQUAL(RMI_INCOMPLETE, rc.status);
	CHECK_EQUAL(1UL, res.x[1]); /* only entry 0 was consumed */
	unsigned long mem_req = EXTRACT(RMI_OP_MEM_REQ, res.x[0]);
	CHECK_EQUAL(RMI_OP_MEM_REQ_DONATE, mem_req);

	unsigned long remaining = EXTRACT(RMI_OP_DONATE_BLK_COUNT, res.x[2]);
	CHECK_EQUAL(requested_count - 1UL, remaining);

	/*
	 * Send a single non-delegated granule as the next batch. This hits
	 * the i==0 failure path in rec_create_request_aux_mem, which calls
	 * rec_start_memory_reclaim -> INCOMPLETE + RECLAIM.
	 */
	uintptr_t bad_granule = reserve_granules(1);
	/* Do NOT delegate bad_granule - it stays in NS state */
	addr_list[0] = encode_addr_desc(bad_granule, 1UL, RMI_OP_MEM_DELEGATED);

	smc_op_mem_donate(handle, realm.addr_list, 1, &res);

	rc = unpack_return_code(res.x[0]);
	CHECK_EQUAL(RMI_INCOMPLETE, rc.status);
	mem_req = EXTRACT(RMI_OP_MEM_REQ, res.x[0]);
	CHECK_EQUAL(RMI_OP_MEM_REQ_RECLAIM, mem_req);
}

/*
 * TC6: Invalid (bogus) handle passed to OP_MEM_DONATE.
 *      Should return RMI_ERROR_INPUT.
 */
TEST(rec_sro_tests, rec_create_sro_invalid_handle)
{
	struct test_realm realm;

	CHECK_TRUE(create_test_context(&realm));

	unsigned long handle = 0, donate_req = 0;
	CHECK_TRUE(initiate_rec_create(&realm, &handle, &donate_req));

	/* Use a bogus handle */
	unsigned long bad_handle = 0xDEADBEEFUL;
	unsigned long *addr_list = (unsigned long *)realm.addr_list;

	uintptr_t aux_base = reserve_granules(1);
	CHECK_TRUE(delegate_range(aux_base, aux_base + GRANULE_SIZE));
	addr_list[0] = encode_addr_desc(aux_base, 1UL, RMI_OP_MEM_DELEGATED);

	struct smc_result res = {};
	smc_op_mem_donate(bad_handle, realm.addr_list, 1, &res);

	return_code_t rc = unpack_return_code(res.x[0]);
	CHECK_EQUAL(RMI_ERROR_INPUT, rc.status);
}

/*
 * TC7: Send OP_CONTINUE when OP_MEM_DONATE is expected (wrong FID sequence).
 *      The SRO dispatch should return RMI_ERROR_INPUT.
 */
TEST(rec_sro_tests, rec_create_sro_wrong_fid_sequence)
{
	struct test_realm realm;

	CHECK_TRUE(create_test_context(&realm));

	unsigned long handle = 0, donate_req = 0;
	CHECK_TRUE(initiate_rec_create(&realm, &handle, &donate_req));

	/*
	 * After REC_CREATE, the expected FID is OP_MEM_DONATE.
	 * Send OP_CONTINUE instead.
	 */
	struct smc_result res = {};
	smc_op_continue(handle, 0UL, &res);

	CHECK_EQUAL(RMI_ERROR_INPUT, res.x[0]);
	CHECK_EQUAL(0UL, res.x[1]);
}

/*
 * TC8: Incremental donation - donate one granule at a time, each time the
 *      SRO flow should request remaining and eventually transition to
 *      CONTINUE.
 */
TEST(rec_sro_tests, rec_create_sro_incremental_donation)
{
	struct test_realm realm;

	CHECK_TRUE(create_test_context(&realm));

	unsigned long handle = 0, donate_req = 0;
	CHECK_TRUE(initiate_rec_create(&realm, &handle, &donate_req));

	unsigned long requested_count = EXTRACT(RMI_OP_DONATE_BLK_COUNT, donate_req);
	uintptr_t aux_base = reserve_granules((unsigned int)requested_count);
	CHECK_TRUE(delegate_range(aux_base,
				  aux_base + requested_count * GRANULE_SIZE));

	unsigned long *addr_list = (unsigned long *)realm.addr_list;
	struct smc_result res = {};
	unsigned long donated_so_far = 0;

	for (unsigned long batch = 0; batch < requested_count; batch++) {
		addr_list[0] = encode_addr_desc(
			aux_base + (batch * GRANULE_SIZE),
			1UL, RMI_OP_MEM_DELEGATED);

		smc_op_mem_donate(handle, realm.addr_list, 1, &res);

		return_code_t rc = unpack_return_code(res.x[0]);
		CHECK_EQUAL(RMI_INCOMPLETE, rc.status);

		/* Should have consumed 1 entry */
		CHECK_EQUAL(1UL, res.x[1]);

		donated_so_far++;
		donate_req = res.x[2];

		unsigned long mem_req = EXTRACT(RMI_OP_MEM_REQ, res.x[0]);

		if (donated_so_far < requested_count) {
			/* Still need more - should request DONATE */
			CHECK_EQUAL(RMI_OP_MEM_REQ_DONATE, mem_req);

			/* Remaining count should match */
			unsigned long remaining = EXTRACT(RMI_OP_DONATE_BLK_COUNT,
							  donate_req);
			CHECK_EQUAL(requested_count - donated_so_far,
				    remaining);
		} else {
			/* All donated - should request NONE (continue) */
			CHECK_EQUAL(RMI_OP_MEM_REQ_NONE, mem_req);
		}
	}
}

/*
 * TC9: Unaligned list address passed to OP_MEM_DONATE.
 *      The list_addr must be 8-byte aligned. Passing an odd address
 *      should return RMI_ERROR_INPUT.
 */
TEST(rec_sro_tests, rec_create_sro_unaligned_list_addr)
{
	struct test_realm realm;

	CHECK_TRUE(create_test_context(&realm));

	unsigned long handle = 0, donate_req = 0;
	CHECK_TRUE(initiate_rec_create(&realm, &handle, &donate_req));

	/* Use an unaligned address for the list */
	uintptr_t unaligned_addr = realm.addr_list + 3;

	struct smc_result res = {};
	smc_op_mem_donate(handle, unaligned_addr, 1, &res);

	return_code_t rc = unpack_return_code(res.x[0]);
	CHECK_EQUAL(RMI_ERROR_INPUT, rc.status);
}

/*
 * TC10: Donate with list_count=0.
 *       Returns INCOMPLETE with the previous donate request so the
 *       host can retry.
 */
TEST(rec_sro_tests, rec_create_sro_zero_list_count)
{
	struct test_realm realm;

	CHECK_TRUE(create_test_context(&realm));

	unsigned long handle = 0, donate_req = 0;
	CHECK_TRUE(initiate_rec_create(&realm, &handle, &donate_req));

	struct smc_result res = {};
	smc_op_mem_donate(handle, realm.addr_list, 0, &res);

	return_code_t rc = unpack_return_code(res.x[0]);
	CHECK_EQUAL(RMI_INCOMPLETE, rc.status);
	CHECK_EQUAL(RMI_OP_MEM_REQ_DONATE,
		    EXTRACT(RMI_OP_MEM_REQ, res.x[0]));
	CHECK_EQUAL(0UL, res.x[1]);
	CHECK_EQUAL(donate_req, res.x[2]);
}

/* ================================================================
 * Helper: trigger reclaim by donating a single non-delegated granule
 * after successfully donating 'good_count' delegated granules.
 *
 * On return the SRO context is in the reclaim phase. The handle
 * remains valid for subsequent smc_op_mem_reclaim() calls.
 *
 * Returns the number of granules that were actually accepted (and
 * thus need to be reclaimed).
 * ================================================================
 */
static unsigned long trigger_reclaim(struct test_realm *r,
				     unsigned long *handle)
{
	unsigned long donate_req = 0;
	struct smc_result res = {};
	return_code_t rc;
	unsigned long mem_req;

	CHECK_TRUE(initiate_rec_create(r, handle, &donate_req));

	unsigned long requested = EXTRACT(RMI_OP_DONATE_BLK_COUNT, donate_req);
	CHECK_TRUE(requested >= 2UL);

	/*
	 * Donate (requested - 1) valid delegated granules so that
	 * the SRO context has some aux_granules_pa[] entries to reclaim.
	 */
	unsigned long good_count = requested - 1UL;
	uintptr_t aux_base = reserve_granules((unsigned int)good_count);
	CHECK_TRUE(delegate_range(aux_base,
				  aux_base + good_count * GRANULE_SIZE));

	unsigned long *addr_list = (unsigned long *)r->addr_list;
	for (unsigned long i = 0; i < good_count; i++) {
		addr_list[i] = encode_addr_desc(
			aux_base + (i * GRANULE_SIZE),
			1UL, RMI_OP_MEM_DELEGATED);
	}

	smc_op_mem_donate(*handle, r->addr_list, good_count, &res);
	rc = unpack_return_code(res.x[0]);
	CHECK_EQUAL(RMI_INCOMPLETE, rc.status);
	CHECK_EQUAL(good_count, res.x[1]);

	mem_req = EXTRACT(RMI_OP_MEM_REQ, res.x[0]);
	CHECK_EQUAL(RMI_OP_MEM_REQ_DONATE, mem_req);

	/*
	 * Now send a non-delegated granule as the next batch.
	 * This triggers the i==0 failure path -> rec_start_memory_reclaim.
	 */
	uintptr_t bad = reserve_granules(1);
	addr_list[0] = encode_addr_desc(bad, 1UL, RMI_OP_MEM_DELEGATED);

	smc_op_mem_donate(*handle, r->addr_list, 1, &res);
	rc = unpack_return_code(res.x[0]);
	CHECK_EQUAL(RMI_INCOMPLETE, rc.status);

	mem_req = EXTRACT(RMI_OP_MEM_REQ, res.x[0]);
	CHECK_EQUAL(RMI_OP_MEM_REQ_RECLAIM, mem_req);

	return good_count;
}

/*
 * TC11: Full reclaim in a single batch after donation failure.
 *       Donate (requested-1) granules, trigger reclaim, then issue
 *       smc_op_mem_reclaim with a buffer large enough to hold all
 *       entries. After reclaim completes, OP_CONTINUE finishes the
 *       SRO flow.
 */
TEST(rec_sro_tests, rec_create_sro_reclaim_single_batch)
{
	struct test_realm realm;
	CHECK_TRUE(create_test_context(&realm));

	unsigned long handle = 0;
	unsigned long reclaimed = trigger_reclaim(&realm, &handle);
	CHECK_TRUE(reclaimed > 0UL);

	/* Reclaim all entries in one smc_op_mem_reclaim call */
	struct smc_result res = {};
	smc_op_mem_reclaim(handle, realm.addr_list, reclaimed, &res);

	return_code_t rc = unpack_return_code(res.x[0]);
	CHECK_EQUAL(RMI_INCOMPLETE, rc.status);
	/* res.x[1] is the number of descriptors written */
	CHECK_TRUE(res.x[1] >= 1UL);

	unsigned long mem_req = EXTRACT(RMI_OP_MEM_REQ, res.x[0]);
	CHECK_EQUAL(RMI_OP_MEM_REQ_NONE, mem_req);
}

/* ================================================================
 * RMI_REC_DESTROY SRO tests
 *
 * smc_rec_destroy() transitions a REC granule back to DELEGATED and
 * reclaims every auxiliary granule via the SRO OP_MEM_RECLAIM
 * protocol before freeing the SRO context with OP_CONTINUE.
 *
 * Setup helper: build a minimal but valid fake REC granule together
 * with its RD and auxiliary granules so that smc_rec_destroy can
 * traverse the full reclaim state machine.
 * ================================================================
 */

/*
 * Populate a fake REC granule at @rec_pa.
 *
 * Preconditions:
 *  - @rec_pa is already in DELEGATED state.
 *  - @g_rd   is already in RD state with refcount == 1.
 *  - @aux_pa[0..num_aux-1] are already in REC_AUX state.
 *
 * Postcondition: the granule at @rec_pa is in GRANULE_STATE_REC with
 * refcount 0.  The struct rec content reflects the provided parameters.
 */
static void populate_fake_rec(uintptr_t rec_pa,
			      struct granule *g_rd,
			      uintptr_t *aux_pa,
			      unsigned int num_aux)
{
	struct granule *g_rec = find_granule(rec_pa);
	struct rec *rec;

	/* Write the rec fields before changing the granule state so we avoid
	 * touching memory that is in REC state without holding the lock.
	 */
	rec = (struct rec *)rec_pa;
	(void)memset(rec, 0, sizeof(*rec));
	rec->num_rec_aux = num_aux;
	for (unsigned int i = 0U; i < num_aux; i++) {
		rec->g_aux[i] = find_granule(aux_pa[i]);
	}
	rec->realm_info.g_rd = g_rd;
	/* rec->attest_app_data is zeroed; app_delete_instance returns early
	 * when app_id == 0 and get_app_process_data() finds no entry.
	 */
	/* Transition DELEGATED -> REC */
	granule_lock(g_rec, GRANULE_STATE_DELEGATED);
	__granule_set_state(g_rec, GRANULE_STATE_REC);
	granule_unlock(g_rec);
}

/*
 * Allocate and fully configure a fake REC for use in destroy tests.
 *
 * Reserves fresh granules from the global pool, delegates them, sets up
 * the RD granule with refcount 1, and places each auxiliary granule in
 * REC_AUX state.
 *
 * Returns the PA of the REC granule.  On any setup failure the function
 * issues a CppUTest CHECK_TRUE failure and returns ~0UL.
 */
static uintptr_t alloc_fake_rec(unsigned int num_aux,
				uintptr_t aux_pa_out[])
{
	uintptr_t rd_pa  = reserve_granules(1U);
	uintptr_t rec_pa = reserve_granules(1U);

	/* Delegate REC and RD granules */
	CHECK_TRUE(delegate_range(rd_pa,  rd_pa  + GRANULE_SIZE));
	CHECK_TRUE(delegate_range(rec_pa, rec_pa + GRANULE_SIZE));

	/* Set up RD granule: DELEGATED -> RD with refcount 1 */
	struct granule *g_rd = find_granule(rd_pa);
	granule_lock(g_rd, GRANULE_STATE_DELEGATED);
	__granule_set_state(g_rd, GRANULE_STATE_RD);
	granule_refcount_inc(g_rd, 1U);
	granule_unlock(g_rd);

	/* Delegate and set each auxiliary granule to REC_AUX */
	for (unsigned int i = 0U; i < num_aux; i++) {
		aux_pa_out[i] = reserve_granules(1U);
		CHECK_TRUE(delegate_range(aux_pa_out[i],
					  aux_pa_out[i] + GRANULE_SIZE));

		struct granule *g_aux = find_granule(aux_pa_out[i]);
		granule_lock(g_aux, GRANULE_STATE_DELEGATED);
		__granule_set_state(g_aux, GRANULE_STATE_REC_AUX);
		granule_unlock(g_aux);
	}

	populate_fake_rec(rec_pa, g_rd, aux_pa_out, num_aux);

	return rec_pa;
}

/*
 * Drive the full reclaim phase for an already-started REC_DESTROY.
 *
 * Calls OP_MEM_RECLAIM with @batch_size entries per call until all
 * @total granule PAs have been returned to the NS output buffer.
 * After each batch, the descriptors written to @ns_buf are decoded
 * and every granule PA is verified against @expected_pa[0..total-1].
 * On success returns the handle ready for the subsequent OP_CONTINUE.
 */
static void drain_reclaim(unsigned long handle,
			  uintptr_t ns_buf,
			  unsigned long total,
			  unsigned long batch_size,
			  const uintptr_t *expected_pa)
{
	unsigned long remaining = total;
	unsigned long verified = 0UL;
	struct smc_result res = {};

	CHECK_TRUE(ALIGNED(ns_buf, GRANULE_SIZE));
	CHECK_TRUE(batch_size > 0UL);

	while (remaining > 0UL) {
		unsigned long batch = MIN(batch_size, remaining);
		smc_op_mem_reclaim(handle, ns_buf, batch, &res);

		return_code_t rc = unpack_return_code(res.x[0]);
		CHECK_EQUAL(RMI_INCOMPLETE, rc.status);

		unsigned long mem_req =
			EXTRACT(RMI_OP_MEM_REQ, res.x[0]);

		if (remaining > batch) {
			CHECK_EQUAL(RMI_OP_MEM_REQ_RECLAIM, mem_req);
		} else {
			CHECK_EQUAL(RMI_OP_MEM_REQ_NONE, mem_req);
		}

		/* Verify the descriptors written to ns_buf */
		unsigned long num_descs = res.x[1];
		unsigned long *descs = (unsigned long *)ns_buf;

		for (unsigned long d = 0UL; d < num_descs; d++) {
			unsigned long desc = descs[d];
			unsigned long base_addr =
				RMI_ADDR_RDESC_4K_GET_ADDR(desc);
			unsigned long cnt =
				EXTRACT(RMI_ADDR_RDESC_4K_CNT, desc);
			unsigned long sz =
				EXTRACT(RMI_ADDR_RDESC_4K_SZ, desc);
			unsigned long blk_size = XLAT_BLOCK_SIZE(
				(int)XLAT_TABLE_LEVEL_MAX - (int)sz);

			for (unsigned long g = 0UL; g < cnt; g++) {
				unsigned long pa = base_addr + g * blk_size;
				bool found = false;

				for (unsigned long e = 0UL; e < total; e++) {
					if ((unsigned long)expected_pa[e] == pa) {
						found = true;
						break;
					}
				}
				CHECK_TRUE(found);
				verified++;
			}
		}

		remaining -= batch;
	}

	CHECK_EQUAL(total, verified);
}

/* ----------------------------------------------------------------
 * TC_DESTROY_01: Unaligned REC address → RMI_ERROR_INPUT (no SRO).
 * ----------------------------------------------------------------
 */
TEST(rec_sro_tests, rec_destroy_invalid_address)
{
	uintptr_t unaligned = granule_addr(g_next_idx) + 1U;
	struct smc_result res = {};
	smc_rec_destroy(unaligned, &res);
	CHECK_EQUAL(RMI_ERROR_INPUT, res.x[0]);
}

/* ----------------------------------------------------------------
 * TC_DESTROY_02: Granule is in DELEGATED state, not REC.
 *                find_lock_unused_granule() fails → RMI_ERROR_INPUT.
 * ----------------------------------------------------------------
 */
TEST(rec_sro_tests, rec_destroy_granule_not_in_rec_state)
{
	uintptr_t delegated_pa = reserve_granules(1U);
	CHECK_TRUE(delegate_range(delegated_pa, delegated_pa + GRANULE_SIZE));

	struct smc_result res = {};
	smc_rec_destroy(delegated_pa, &res);
	CHECK_EQUAL(RMI_ERROR_INPUT, res.x[0]);
}

/* ----------------------------------------------------------------
 * TC_DESTROY_03: REC is currently running (refcount != 0).
 *                find_lock_unused_granule() returns -EBUSY →
 *                RMI_ERROR_REC.
 * ----------------------------------------------------------------
 */
TEST(rec_sro_tests, rec_destroy_busy_rec)
{
	uintptr_t rec_pa = reserve_granules(1U);
	CHECK_TRUE(delegate_range(rec_pa, rec_pa + GRANULE_SIZE));

	/* Force the granule to REC state, then bump the refcount to 1 */
	struct granule *g_rec = find_granule(rec_pa);
	granule_lock(g_rec, GRANULE_STATE_DELEGATED);
	__granule_set_state(g_rec, GRANULE_STATE_REC);
	granule_refcount_inc(g_rec, 1U);
	granule_unlock(g_rec);

	struct smc_result res = {};
	smc_rec_destroy(rec_pa, &res);
	CHECK_EQUAL(RMI_ERROR_REC, res.x[0]);

	/* Clean up: remove the artificial refcount so the granule can be
	 * garbage-collected if the pool is reused later in the suite.
	 */
	granule_lock(g_rec, GRANULE_STATE_REC);
	atomic_granule_put(g_rec);
	__granule_set_state(g_rec, GRANULE_STATE_DELEGATED);
	granule_unlock(g_rec);
}

/* ----------------------------------------------------------------
 * TC_DESTROY_04: Happy path — destroy a REC that has
 *                MAX_REC_AUX_GRANULES aux granules.
 *
 *  smc_rec_destroy  → INCOMPLETE + RECLAIM + handle
 *  OP_MEM_RECLAIM   → INCOMPLETE + NONE   (all in one batch)
 *  OP_CONTINUE      → RMI_SUCCESS
 *
 *  After the sequence:
 *   • the REC granule is in DELEGATED state.
 *   • every auxiliary granule is in DELEGATED state.
 * ----------------------------------------------------------------
 */
TEST(rec_sro_tests, rec_destroy_single_batch_reclaim)
{
	uintptr_t aux_pa[MAX_REC_AUX_GRANULES];
	uintptr_t rec_pa = alloc_fake_rec(MAX_REC_AUX_GRANULES, aux_pa);
	uintptr_t ns_buf = reserve_granules(1U);

	struct smc_result res = {};
	smc_rec_destroy(rec_pa, &res);

	return_code_t rc = unpack_return_code(res.x[0]);
	CHECK_EQUAL(RMI_INCOMPLETE, rc.status);
	CHECK_EQUAL(RMI_OP_MEM_REQ_RECLAIM,
		    (unsigned long)EXTRACT(RMI_OP_MEM_REQ, res.x[0]));

	/* REC granule is in PARTIAL state during the SRO flow */
	CHECK_EQUAL(GRANULE_STATE_PARTIAL,
		    (unsigned long)granule_unlocked_state(find_granule(rec_pa)));

	unsigned long handle = res.x[1];
	/* handle is the pool index; 0 is a valid first-slot handle */

	/* Reclaim all aux granules in one call */
	smc_op_mem_reclaim(handle, ns_buf, MAX_REC_AUX_GRANULES, &res);
	rc = unpack_return_code(res.x[0]);
	CHECK_EQUAL(RMI_INCOMPLETE, rc.status);
	CHECK_EQUAL(RMI_OP_MEM_REQ_NONE,
		    (unsigned long)EXTRACT(RMI_OP_MEM_REQ, res.x[0]));

	/* Finish */
	smc_op_continue(handle, 0UL, &res);
	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);

	/* REC granule must now be DELEGATED after the full flow */
	CHECK_EQUAL(GRANULE_STATE_DELEGATED,
		    (unsigned long)granule_unlocked_state(find_granule(rec_pa)));

	/* All auxiliary granules must now be DELEGATED */
	for (unsigned int i = 0U; i < MAX_REC_AUX_GRANULES; i++) {
		CHECK_EQUAL(GRANULE_STATE_DELEGATED,
			    (unsigned long)granule_unlocked_state(
						find_granule(aux_pa[i])));
	}
}

/* ----------------------------------------------------------------
 * TC_DESTROY_05: Multi-batch reclaim — reclaim one aux granule per
 *                OP_MEM_RECLAIM call.
 *
 *  smc_rec_destroy  → INCOMPLETE + RECLAIM + handle
 *  OP_MEM_RECLAIM×N → interleaved RECLAIM / NONE responses
 *  OP_CONTINUE      → RMI_SUCCESS
 * ----------------------------------------------------------------
 */
TEST(rec_sro_tests, rec_destroy_multi_batch_reclaim)
{
	uintptr_t aux_pa[MAX_REC_AUX_GRANULES];
	uintptr_t rec_pa = alloc_fake_rec(MAX_REC_AUX_GRANULES, aux_pa);
	uintptr_t ns_buf = reserve_granules(1U);

	struct smc_result res = {};
	smc_rec_destroy(rec_pa, &res);

	return_code_t rc = unpack_return_code(res.x[0]);
	CHECK_EQUAL(RMI_INCOMPLETE, rc.status);
	unsigned long handle = res.x[1];

	/* Drain one entry at a time */
	drain_reclaim(handle, ns_buf,
		      (unsigned long)MAX_REC_AUX_GRANULES, 1UL,
		      aux_pa);

	/* After all reclaimed, OP_CONTINUE finalises the destroy */
	smc_op_continue(handle, 0UL, &res);
	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
}

/* ----------------------------------------------------------------
 * TC_DESTROY_06: Bogus handle passed to OP_MEM_RECLAIM while a
 *                genuine reclaim is in progress on a different handle.
 *                sro_ctx_find() fails → RMI_ERROR_INPUT.
 *                The genuine handle is unaffected.
 * ----------------------------------------------------------------
 */
TEST(rec_sro_tests, rec_destroy_reclaim_invalid_handle)
{
	uintptr_t aux_pa[MAX_REC_AUX_GRANULES];
	uintptr_t rec_pa = alloc_fake_rec(MAX_REC_AUX_GRANULES, aux_pa);
	uintptr_t ns_buf = reserve_granules(1U);

	struct smc_result res = {};
	smc_rec_destroy(rec_pa, &res);
	unsigned long real_handle = res.x[1];

	/* Attempt reclaim with a bogus handle */
	smc_op_mem_reclaim(0xDEADBEEFUL, ns_buf, 1UL, &res);
	CHECK_EQUAL(RMI_ERROR_INPUT, res.x[0]);

	/* The real context is still usable */
	drain_reclaim(real_handle, ns_buf,
		      (unsigned long)MAX_REC_AUX_GRANULES,
		      (unsigned long)MAX_REC_AUX_GRANULES,
		      aux_pa);
	smc_op_continue(real_handle, 0UL, &res);
	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
}

/* ----------------------------------------------------------------
 * TC_DESTROY_07: Unaligned NS output buffer in OP_MEM_RECLAIM.
 *
 *  Alignment check fires before any granule transition →
 *  RMI_ERROR_INPUT; no entries are written and the SRO context
 *  remains in reclaim state so a valid retry succeeds.
 * ----------------------------------------------------------------
 */
TEST(rec_sro_tests, rec_destroy_reclaim_unaligned_output)
{
	uintptr_t aux_pa[MAX_REC_AUX_GRANULES];
	uintptr_t rec_pa = alloc_fake_rec(MAX_REC_AUX_GRANULES, aux_pa);
	uintptr_t ns_buf = reserve_granules(1U);

	struct smc_result res = {};
	smc_rec_destroy(rec_pa, &res);
	unsigned long handle = res.x[1];

	/* Misalign by 3 bytes */
	smc_op_mem_reclaim(handle, ns_buf + 3UL,
			   (unsigned long)MAX_REC_AUX_GRANULES, &res);
	CHECK_EQUAL(RMI_ERROR_INPUT, res.x[0]);

	/* Retry with the properly aligned buffer */
	drain_reclaim(handle, ns_buf,
		      (unsigned long)MAX_REC_AUX_GRANULES,
		      (unsigned long)MAX_REC_AUX_GRANULES,
		      aux_pa);
	smc_op_continue(handle, 0UL, &res);
	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
}

/* ----------------------------------------------------------------
 * TC_DESTROY_08: NS output buffer is in DELEGATED state (not NS).
 *
 *  copy_list_to_ns() checks the granule state of the output page.
 *  When it is not NS the call returns RMI_ERROR_INPUT with zero
 *  entries written.  The SRO context survives so a valid retry
 *  succeeds.
 * ----------------------------------------------------------------
 */
TEST(rec_sro_tests, rec_destroy_reclaim_non_ns_output_buffer)
{
	uintptr_t aux_pa[MAX_REC_AUX_GRANULES];
	uintptr_t rec_pa = alloc_fake_rec(MAX_REC_AUX_GRANULES, aux_pa);

	/* A delegated granule is NOT in NS state */
	uintptr_t bad_buf = reserve_granules(1U);
	CHECK_TRUE(delegate_range(bad_buf, bad_buf + GRANULE_SIZE));

	uintptr_t ns_buf = reserve_granules(1U); /* stays in NS state */

	struct smc_result res = {};
	smc_rec_destroy(rec_pa, &res);
	unsigned long handle = res.x[1];

	smc_op_mem_reclaim(handle, bad_buf,
			   (unsigned long)MAX_REC_AUX_GRANULES, &res);
	return_code_t rc = unpack_return_code(res.x[0]);
	CHECK_EQUAL(RMI_ERROR_INPUT, rc.status);
	CHECK_EQUAL(0UL, res.x[1]);

	/* Retry with valid NS buffer — should succeed */
	drain_reclaim(handle, ns_buf,
		      (unsigned long)MAX_REC_AUX_GRANULES,
		      (unsigned long)MAX_REC_AUX_GRANULES,
		      aux_pa);
	smc_op_continue(handle, 0UL, &res);
	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
}

/* ----------------------------------------------------------------
 * TC_DESTROY_09: Wrong FID — host issues OP_CONTINUE when
 *                OP_MEM_RECLAIM is expected.
 * ----------------------------------------------------------------
 */
TEST(rec_sro_tests, rec_destroy_wrong_fid_continue_before_reclaim)
{
	uintptr_t aux_pa[MAX_REC_AUX_GRANULES];
	uintptr_t rec_pa = alloc_fake_rec(MAX_REC_AUX_GRANULES, aux_pa);
	uintptr_t ns_buf = reserve_granules(1U);

	struct smc_result res = {};
	smc_rec_destroy(rec_pa, &res);
	unsigned long handle = res.x[1];

	/*
	 * Issue OP_CONTINUE while OP_MEM_RECLAIM is expected.
	 * Returns RMI_ERROR_INPUT.
	 */
	smc_op_continue(handle, 0UL, &res);
	CHECK_EQUAL(RMI_ERROR_INPUT, res.x[0]);

	/*
	 * The context is still alive — proceed with the correct
	 * reclaim sequence.
	 */
	smc_op_mem_reclaim(handle, ns_buf,
			   (unsigned long)MAX_REC_AUX_GRANULES, &res);
	CHECK_EQUAL(RMI_INCOMPLETE, unpack_return_code(res.x[0]).status);
}

/* ----------------------------------------------------------------
 * TC_DESTROY_10: OP_CANCEL is rejected because REC_DESTROY is
 *                non-cancellable (can_cancel == false).
 *
 *  smc_op_cancel() returns RMI_ERROR_INPUT; the SRO context remains
 *  sealed so the reclaim sequence can still be completed.
 * ----------------------------------------------------------------
 */
TEST(rec_sro_tests, rec_destroy_cancel_not_allowed)
{
	uintptr_t aux_pa[MAX_REC_AUX_GRANULES];
	uintptr_t rec_pa = alloc_fake_rec(MAX_REC_AUX_GRANULES, aux_pa);
	uintptr_t ns_buf = reserve_granules(1U);

	struct smc_result res = {};
	smc_rec_destroy(rec_pa, &res);
	unsigned long handle = res.x[1];

	/* Attempt to cancel — must be refused */
	smc_op_cancel(handle, &res);
	CHECK_EQUAL(RMI_ERROR_INPUT, res.x[0]);

	/* Context still alive; complete the reclaim normally */
	drain_reclaim(handle, ns_buf,
		      (unsigned long)MAX_REC_AUX_GRANULES,
		      (unsigned long)MAX_REC_AUX_GRANULES,
		      aux_pa);
	smc_op_continue(handle, 0UL, &res);
	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
}

/* ----------------------------------------------------------------
 * TC_DESTROY_11: Partial reclaim with an oversized batch.
 *
 *  The output buffer is a single 4 KB granule.  ADDR_LIST_MAX_RANGES
 *  caps the number of entries per call; when the caller requests more
 *  than available the framework clamps list_count automatically and
 *  returns INCOMPLETE + RECLAIM until the tail is exhausted.
 *
 *  This test uses MAX_REC_AUX_GRANULES auxiliary granules and passes
 *  ADDR_LIST_MAX_RANGES + 1 as the count, verifying the clamping path.
 * ----------------------------------------------------------------
 */
TEST(rec_sro_tests, rec_destroy_reclaim_oversized_batch_clamped)
{
	uintptr_t aux_pa[MAX_REC_AUX_GRANULES];
	uintptr_t rec_pa = alloc_fake_rec(MAX_REC_AUX_GRANULES, aux_pa);
	uintptr_t ns_buf = reserve_granules(1U);

	struct smc_result res = {};
	smc_rec_destroy(rec_pa, &res);
	unsigned long handle = res.x[1];

	/*
	 * Request more than ADDR_LIST_MAX_RANGES in a single call.
	 * The framework silently clamps list_count to ADDR_LIST_MAX_RANGES.
	 * With MAX_REC_AUX_GRANULES (16) << ADDR_LIST_MAX_RANGES (512),
	 * all granules are reclaimed in one call and mem_req transitions
	 * to NONE immediately.
	 */
	smc_op_mem_reclaim(handle, ns_buf,
			   ADDR_LIST_MAX_RANGES + 1UL, &res);
	return_code_t rc = unpack_return_code(res.x[0]);
	CHECK_EQUAL(RMI_INCOMPLETE, rc.status);
	CHECK_TRUE(res.x[1] >= 1UL); /* clamped path returned ≥1 descriptor */
	CHECK_EQUAL(RMI_OP_MEM_REQ_NONE,
		    (unsigned long)EXTRACT(RMI_OP_MEM_REQ, res.x[0]));

	smc_op_continue(handle, 0UL, &res);
	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
}

/* ----------------------------------------------------------------
 * TC_DESTROY_12: Exercises the "still pending entries" path in
 *                smc_op_mem_reclaim that performs a memmove of
 *                remaining entries.
 *
 *  This path requires addr_list->count > list_count so that a single
 *  copy call does not drain the whole list.  Consecutive aux granules
 *  compact into one descriptor, so this test uses two non-consecutive
 *  aux granules (separated by a gap) to produce two descriptors.
 *
 *  Steps:
 *   1. Build a fake REC with 2 non-consecutive aux granules.
 *   2. REC_DESTROY → INCOMPLETE (RECLAIM).
 *   3. OP_MEM_RECLAIM with a delegated (non-NS) output buffer and
 *      list_count = 2.  Callback fills both descriptors but the NS
 *      copy fails → addr_list->count stays at 2.
 *   4. Retry with valid NS buffer, list_count = 1.  Copies descriptor
 *      [0], memmoves descriptor [1] to front → addr_list->count = 1
 *      → "still pending" branch → RECLAIM.
 *   5. One more call drains descriptor [1] → MEM_REQ_NONE.
 *   6. OP_CONTINUE → RMI_SUCCESS.
 * ----------------------------------------------------------------
 */
TEST(rec_sro_tests, rec_destroy_reclaim_pending_entries_memmove)
{
	/*
	 * Allocate 2 non-consecutive aux granules by inserting a 1-granule
	 * gap between them.  The gap PA is never delegated, so the two aux
	 * PAs differ by 2 * GRANULE_SIZE and cannot be merged into one
	 * descriptor by addr_list_add_block.
	 */
	uintptr_t aux_pa[2];

	uintptr_t rd_pa  = reserve_granules(1U);
	uintptr_t rec_pa = reserve_granules(1U);
	CHECK_TRUE(delegate_range(rd_pa,  rd_pa  + GRANULE_SIZE));
	CHECK_TRUE(delegate_range(rec_pa, rec_pa + GRANULE_SIZE));

	struct granule *g_rd = find_granule(rd_pa);
	granule_lock(g_rd, GRANULE_STATE_DELEGATED);
	__granule_set_state(g_rd, GRANULE_STATE_RD);
	granule_refcount_inc(g_rd, 1U);
	granule_unlock(g_rd);

	aux_pa[0] = reserve_granules(1U);
	reserve_granules(1U);              /* gap: creates non-consecutive PA */
	aux_pa[1] = reserve_granules(1U);

	for (unsigned int i = 0U; i < 2U; i++) {
		CHECK_TRUE(delegate_range(aux_pa[i], aux_pa[i] + GRANULE_SIZE));
		struct granule *g_aux = find_granule(aux_pa[i]);
		granule_lock(g_aux, GRANULE_STATE_DELEGATED);
		__granule_set_state(g_aux, GRANULE_STATE_REC_AUX);
		granule_unlock(g_aux);
	}

	populate_fake_rec(rec_pa, g_rd, aux_pa, 2U);

	/* A delegated granule serves as the invalid (non-NS) output buf */
	uintptr_t bad_buf = reserve_granules(1U);
	CHECK_TRUE(delegate_range(bad_buf, bad_buf + GRANULE_SIZE));

	uintptr_t ns_buf = reserve_granules(1U); /* stays in NS state */

	struct smc_result res = {};
	smc_rec_destroy(rec_pa, &res);

	return_code_t rc = unpack_return_code(res.x[0]);
	CHECK_EQUAL(RMI_INCOMPLETE, rc.status);
	unsigned long handle = res.x[1];

	/*
	 * Step 3: drive the callback with list_count = 2 so both descriptors
	 * are populated, then fail the NS copy with the delegated buffer.
	 * addr_list->count remains 2.
	 */
	smc_op_mem_reclaim(handle, bad_buf, 2UL, &res);
	rc = unpack_return_code(res.x[0]);
	CHECK_EQUAL(RMI_ERROR_INPUT, rc.status);
	CHECK_EQUAL(0UL, res.x[1]);

	/*
	 * Step 4: retry with valid NS buffer, list_count = 1.
	 * addr_list->count = 2 → copies 1 descriptor → memmove shifts [1]
	 * to [0] → addr_list->count = 1 → "still pending" → RECLAIM.
	 */
	smc_op_mem_reclaim(handle, ns_buf, 1UL, &res);
	rc = unpack_return_code(res.x[0]);
	CHECK_EQUAL(RMI_INCOMPLETE, rc.status);
	CHECK_EQUAL(1UL, res.x[1]);
	CHECK_EQUAL(RMI_OP_MEM_REQ_RECLAIM,
		    (unsigned long)EXTRACT(RMI_OP_MEM_REQ, res.x[0]));

	/*
	 * Step 5: drain the final descriptor → MEM_REQ_NONE.
	 */
	smc_op_mem_reclaim(handle, ns_buf, 1UL, &res);
	rc = unpack_return_code(res.x[0]);
	CHECK_EQUAL(RMI_INCOMPLETE, rc.status);
	CHECK_EQUAL(1UL, res.x[1]);
	CHECK_EQUAL(RMI_OP_MEM_REQ_NONE,
		    (unsigned long)EXTRACT(RMI_OP_MEM_REQ, res.x[0]));

	/* Step 6: finish the destroy */
	smc_op_continue(handle, 0UL, &res);
	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
}
