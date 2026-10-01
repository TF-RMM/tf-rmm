/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <CppUTest/CommandLineTestRunner.h>
#include <CppUTest/TestHarness.h>

extern "C" {
#include <buffer.h>
#include <granule.h>
#include <host_utils.h>
#include <realm.h>
#include <rec.h>
}

#include <rmi_test_helpers.h>

extern "C" {
#include <smc-handler.h>
#include <smc-rmi.h>
#include <sro_context.h>
#include <status.h>
#include <string.h>
#include <test_helpers.h>
}

static unsigned long encode_addr_desc(uintptr_t base, unsigned long count,
				      unsigned long state)
{
	return INPLACE(RMI_ADDR_RDESC_4K_SZ, RMI_PAGE_L3) |
	       INPLACE(RMI_ADDR_RDESC_4K_CNT, count) |
	       INPLACE(RMI_ADDR_RDESC_4K_ADDR, base >> GRANULE_SHIFT) |
	       INPLACE(RMI_ADDR_RDESC_4K_ST, state);
}

static bool delegate_range(uintptr_t start, uintptr_t end)
{
	struct smc_result res = {};
	uintptr_t current = start;

	while (current < end) {
		smc_granule_range_delegate(current, end, &res);
		if (res.x[0] != RMI_SUCCESS) {
			return false;
		}

		current = res.x[1];
		if (current == 0UL) {
			break;
		}
	}

	return true;
}

/* Start creation of a prepared Realm and check the initial donation request. */
static void start_realm_create(struct rmi_test_realm *realm)
{
	struct smc_result res = {};
	return_code_t rc;

	smc_realm_create(realm->rd, realm->params, &res);
	rc = unpack_return_code(res.x[0]);
	CHECK_EQUAL(RMI_INCOMPLETE, rc.status);
	CHECK_EQUAL(RMI_OP_MEM_REQ_DONATE,
		    (unsigned long)EXTRACT(RMI_OP_MEM_REQ, res.x[0]));
	CHECK_EQUAL(RMI_PAGE_L3,
		    (unsigned long)EXTRACT(RMI_OP_DONATE_BLK_SIZE, res.x[2]));
	CHECK_EQUAL(RMI_OP_MEM_NON_CONTIG,
		    (unsigned long)EXTRACT(RMI_OP_DONATE_MEM_CONTIG, res.x[2]));
	CHECK_EQUAL(RMI_OP_MEM_DELEGATED,
		    (unsigned long)EXTRACT(RMI_OP_DONATE_MEM_STATE, res.x[2]));

	realm->handle = res.x[1];
	realm->num_aux = (unsigned int)EXTRACT(RMI_OP_DONATE_BLK_COUNT,
						 res.x[2]);
	CHECK_EQUAL(MAX_RD_AUX_GRANULES, realm->num_aux);
	CHECK_EQUAL(GRANULE_STATE_PARTIAL,
		    (unsigned long)granule_unlocked_state(tr_find_fine_granule(realm->rd)));
	CHECK_EQUAL(GRANULE_STATE_DELEGATED,
		    (unsigned long)granule_unlocked_state(tr_find_fine_granule(realm->rtt)));
}

/* Build a donation list, optionally separating AUX pages to prevent coalescing. */
static void allocate_realm_aux(struct rmi_test_realm *realm, bool separated)
{
	unsigned long *addr_list = (unsigned long *)realm->addr_list;

	for (unsigned int i = 0U; i < realm->num_aux; i++) {
		realm->aux[i] = test_helpers_allocate_granules(1U);
		CHECK_TRUE(delegate_range(realm->aux[i],
					  realm->aux[i] + GRANULE_SIZE));
		addr_list[i] = encode_addr_desc(realm->aux[i], 1UL,
					       RMI_OP_MEM_DELEGATED);

		if (separated && ((i + 1U) < realm->num_aux)) {
			(void)test_helpers_allocate_granules(1U);
		}
	}
}

/* Donate the prepared AUX list and check the state before OP_CONTINUE. */
static void donate_realm_aux(struct rmi_test_realm *realm)
{
	struct smc_result res = {};
	return_code_t rc;

	smc_op_mem_donate(realm->handle, realm->addr_list,
			  realm->num_aux, &res);
	rc = unpack_return_code(res.x[0]);
	CHECK_EQUAL(RMI_INCOMPLETE, rc.status);
	CHECK_EQUAL(RMI_OP_MEM_REQ_NONE,
		    (unsigned long)EXTRACT(RMI_OP_MEM_REQ, res.x[0]));
	CHECK_EQUAL(realm->num_aux, res.x[1]);

	for (unsigned int i = 0U; i < realm->num_aux; i++) {
		CHECK_EQUAL(GRANULE_STATE_RD_AUX,
			    (unsigned long)granule_unlocked_state(
						tr_find_fine_granule(realm->aux[i])));
	}
}

/* Release the SRO after a donation-only test; the next test resets its granules. */
static void release_realm_create_context(struct rmi_test_realm *realm)
{
	CHECK_TRUE(sro_ctx_find(realm->handle));
	sro_ctx_release();
}

/* Create a valid Realm through RMI before testing its destroy protocol. */
static void init_destroy_realm(struct rmi_test_realm *realm, bool separated_aux)
{
	rmi_test_realm_prepare(realm);
	rmi_test_realm_create(realm, separated_aux);
}

/* Terminate a Realm with no RECs or child RTTs; return its destroy SRO handle. */
static unsigned long start_realm_destroy(struct rmi_test_realm *realm)
{
	struct smc_result res = {};
	return_code_t rc;

	smc_realm_terminate(realm->rd, &res);
	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);

	smc_realm_destroy(realm->rd, &res);
	rc = unpack_return_code(res.x[0]);
	CHECK_EQUAL(RMI_INCOMPLETE, rc.status);
	CHECK_EQUAL(RMI_OP_MEM_REQ_RECLAIM,
		    (unsigned long)EXTRACT(RMI_OP_MEM_REQ, res.x[0]));
	CHECK_EQUAL(GRANULE_STATE_PARTIAL,
		    (unsigned long)granule_unlocked_state(tr_find_fine_granule(realm->rd)));

	return res.x[1];
}

/* Check that destruction returned the RD, root RTT and AUX pages to DELEGATED. */
static void check_realm_destroyed(const struct rmi_test_realm *realm)
{
	CHECK_EQUAL(GRANULE_STATE_DELEGATED,
		    (unsigned long)granule_unlocked_state(tr_find_fine_granule(realm->rd)));
	CHECK_EQUAL(GRANULE_STATE_DELEGATED,
		    (unsigned long)granule_unlocked_state(tr_find_fine_granule(realm->rtt)));

	for (unsigned int i = 0U; i < realm->num_aux; i++) {
		CHECK_EQUAL(GRANULE_STATE_DELEGATED,
			    (unsigned long)granule_unlocked_state(
						tr_find_fine_granule(realm->aux[i])));
	}
}

TEST_GROUP(realm_sro_tests) {
	TEST_SETUP()
	{
		test_helpers_init();
		test_helpers_rmm_start(false);
		host_util_set_cpuid(0U);
		test_helpers_expect_assert_fail(false);
	}

	TEST_TEARDOWN()
	{
	}
};

/*
 * TC1: Start Realm creation and donate all requested RD auxiliary granules.
 *
 * REALM_CREATE must return INCOMPLETE with a donation request. After the
 * donation, the SRO operation must be ready for OP_CONTINUE, with the RD in
 * PARTIAL state, the auxiliary granules in RD_AUX state, and the root RTT
 * still in DELEGATED state.
 */
TEST(realm_sro_tests, realm_create_donate_requests_continue)
{
	struct rmi_test_realm realm;

	rmi_test_realm_prepare(&realm);
	start_realm_create(&realm);
	allocate_realm_aux(&realm, false);
	donate_realm_aux(&realm);

	/*
	 * This test stops at the donation boundary. The lifecycle test below
	 * exercises creation through completion with the real apps.
	 */
	release_realm_create_context(&realm);
}

/*
 * TC2: Fail Realm creation after accepting one RD auxiliary granule.
 *
 * A subsequent donation containing a non-delegated granule must start
 * reclamation. Reclaiming the accepted granule and continuing the operation
 * must return RMI_ERROR_INPUT and restore the RD, RTT, and auxiliary granule
 * to DELEGATED state.
 */
TEST(realm_sro_tests, realm_create_donation_failure_rolls_back)
{
	struct rmi_test_realm realm;
	struct smc_result res = {};
	return_code_t rc;
	unsigned long *addr_list;
	uintptr_t bad_aux;

	rmi_test_realm_prepare(&realm);
	start_realm_create(&realm);
	allocate_realm_aux(&realm, false);

	addr_list = (unsigned long *)realm.addr_list;
	smc_op_mem_donate(realm.handle, realm.addr_list, 1UL, &res);
	rc = unpack_return_code(res.x[0]);
	CHECK_EQUAL(RMI_INCOMPLETE, rc.status);
	CHECK_EQUAL(RMI_OP_MEM_REQ_DONATE,
		    (unsigned long)EXTRACT(RMI_OP_MEM_REQ, res.x[0]));

	bad_aux = test_helpers_allocate_granules(1U);
	addr_list[0] = encode_addr_desc(bad_aux, 1UL, RMI_OP_MEM_DELEGATED);
	smc_op_mem_donate(realm.handle, realm.addr_list, 1UL, &res);
	rc = unpack_return_code(res.x[0]);
	CHECK_EQUAL(RMI_INCOMPLETE, rc.status);
	CHECK_EQUAL(RMI_OP_MEM_REQ_RECLAIM,
		    (unsigned long)EXTRACT(RMI_OP_MEM_REQ, res.x[0]));

	smc_op_mem_reclaim(realm.handle, realm.addr_list, 1UL, &res);
	rc = unpack_return_code(res.x[0]);
	CHECK_EQUAL(RMI_INCOMPLETE, rc.status);
	CHECK_EQUAL(RMI_OP_MEM_REQ_NONE,
		    (unsigned long)EXTRACT(RMI_OP_MEM_REQ, res.x[0]));

	smc_op_continue(realm.handle, 0UL, &res);
	CHECK_EQUAL(RMI_ERROR_INPUT, res.x[0]);
	CHECK_EQUAL(GRANULE_STATE_DELEGATED,
		    (unsigned long)granule_unlocked_state(tr_find_fine_granule(realm.rd)));
	CHECK_EQUAL(GRANULE_STATE_DELEGATED,
		    (unsigned long)granule_unlocked_state(tr_find_fine_granule(realm.rtt)));
	CHECK_EQUAL(GRANULE_STATE_DELEGATED,
		    (unsigned long)granule_unlocked_state(tr_find_fine_granule(realm.aux[0])));
}

/*
 * TC3: Verify that Realm parameters are copied by the create continuation.
 *
 * Invalidate the Non-secure parameters after REALM_CREATE and donation.
 * OP_CONTINUE must observe the updated invalid parameters, reclaim all RD
 * auxiliary granules, return RMI_ERROR_INPUT, and leave the RD and auxiliary
 * granules in DELEGATED state without transitioning the root RTT.
 */
TEST(realm_sro_tests, realm_create_copies_params_during_continue)
{
	struct rmi_test_realm realm;
	struct rmi_realm_params *params;
	struct smc_result res = {};
	return_code_t rc;

	rmi_test_realm_prepare(&realm);
	start_realm_create(&realm);
	allocate_realm_aux(&realm, false);
	donate_realm_aux(&realm);

	/* Make the NS parameters invalid after the initial command. */
	params = (struct rmi_realm_params *)realm.params;
	params->num_bps = 0U;

	smc_op_continue(realm.handle, 0UL, &res);
	rc = unpack_return_code(res.x[0]);
	CHECK_EQUAL(RMI_INCOMPLETE, rc.status);
	CHECK_EQUAL(RMI_OP_MEM_REQ_RECLAIM,
		    (unsigned long)EXTRACT(RMI_OP_MEM_REQ, res.x[0]));
	CHECK_EQUAL(GRANULE_STATE_DELEGATED,
		    (unsigned long)granule_unlocked_state(tr_find_fine_granule(realm.rtt)));

	smc_op_mem_reclaim(realm.handle, realm.addr_list, realm.num_aux, &res);
	rc = unpack_return_code(res.x[0]);
	CHECK_EQUAL(RMI_INCOMPLETE, rc.status);
	CHECK_EQUAL(RMI_OP_MEM_REQ_NONE,
		    (unsigned long)EXTRACT(RMI_OP_MEM_REQ, res.x[0]));

	smc_op_continue(realm.handle, 0UL, &res);
	CHECK_EQUAL(RMI_ERROR_INPUT, res.x[0]);
	CHECK_EQUAL(GRANULE_STATE_DELEGATED,
		    (unsigned long)granule_unlocked_state(tr_find_fine_granule(realm.rd)));
	for (unsigned int i = 0U; i < realm.num_aux; i++) {
		CHECK_EQUAL(GRANULE_STATE_DELEGATED,
			    (unsigned long)granule_unlocked_state(
						tr_find_fine_granule(realm.aux[i])));
	}
}

/*
 * TC4: Destroy a Realm and reclaim all RD auxiliary granules in one batch.
 *
 * After reclamation, OP_CONTINUE must complete successfully and transition
 * the RD, root RTT, and every auxiliary granule to DELEGATED state.
 */
TEST(realm_sro_tests, realm_destroy_reclaims_aux_and_finishes)
{
	struct rmi_test_realm realm;
	struct smc_result res = {};
	return_code_t rc;
	unsigned long handle;

	init_destroy_realm(&realm, false);
	handle = start_realm_destroy(&realm);

	smc_op_mem_reclaim(handle, realm.addr_list, realm.num_aux, &res);
	rc = unpack_return_code(res.x[0]);
	CHECK_EQUAL(RMI_INCOMPLETE, rc.status);
	CHECK_EQUAL(RMI_OP_MEM_REQ_NONE,
		    (unsigned long)EXTRACT(RMI_OP_MEM_REQ, res.x[0]));

	smc_op_continue(handle, 0UL, &res);
	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
	check_realm_destroyed(&realm);
}

/*
 * TC5: Destroy a Realm whose RD auxiliary granules require multiple reclaim
 * batches.
 *
 * Each reclaim must consume one auxiliary granule and request another batch
 * until none remain. OP_CONTINUE must then complete successfully and restore
 * the RD, root RTT, and all auxiliary granules to DELEGATED state.
 */
TEST(realm_sro_tests, realm_destroy_reclaims_multiple_batches)
{
	struct rmi_test_realm realm;
	struct smc_result res = {};
	return_code_t rc;
	unsigned long handle;

	init_destroy_realm(&realm, true);
	handle = start_realm_destroy(&realm);

	for (unsigned int i = 0U; i < realm.num_aux; i++) {
		smc_op_mem_reclaim(handle, realm.addr_list, 1UL, &res);
		rc = unpack_return_code(res.x[0]);
		CHECK_EQUAL(RMI_INCOMPLETE, rc.status);
		CHECK_EQUAL(1UL, res.x[1]);
		CHECK_EQUAL(((i + 1U) == realm.num_aux) ?
				RMI_OP_MEM_REQ_NONE : RMI_OP_MEM_REQ_RECLAIM,
			    (unsigned long)EXTRACT(RMI_OP_MEM_REQ, res.x[0]));
	}

	smc_op_continue(handle, 0UL, &res);
	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
	check_realm_destroyed(&realm);
}
