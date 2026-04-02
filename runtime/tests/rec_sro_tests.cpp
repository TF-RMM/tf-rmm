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
			1UL, RMI_OP_MEM_DELEGATE);
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
			0UL, RMI_OP_MEM_DELEGATE);
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
			cnt, RMI_OP_MEM_DELEGATE);
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
			2UL, RMI_OP_MEM_DELEGATE);
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
			1UL, RMI_OP_MEM_DELEGATE);
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
			1UL, RMI_OP_MEM_DELEGATE);
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
	addr_list[0] = encode_addr_desc(bad_granule, 1UL, RMI_OP_MEM_DELEGATE);

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
	addr_list[0] = encode_addr_desc(aux_base, 1UL, RMI_OP_MEM_DELEGATE);

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
			1UL, RMI_OP_MEM_DELEGATE);

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
			1UL, RMI_OP_MEM_DELEGATE);
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
	addr_list[0] = encode_addr_desc(bad, 1UL, RMI_OP_MEM_DELEGATE);

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
