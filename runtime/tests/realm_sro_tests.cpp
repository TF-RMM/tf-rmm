/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <CppUTest/CommandLineTestRunner.h>
#include <CppUTest/TestHarness.h>

extern "C" {
#include <arch_features.h>
#include <buffer.h>
#include <granule.h>
#include <host_utils.h>
#include <mec.h>
#include <realm.h>
#include <smc-handler.h>
#include <smc-rmi.h>
#include <sro_context.h>
#include <status.h>
#include <string.h>
#include <test_helpers.h>
#include <vmid.h>
}

struct test_realm {
	uintptr_t rd;
	uintptr_t params;
	uintptr_t rtt;
	uintptr_t addr_list;
	uintptr_t aux[MAX_RD_AUX_GRANULES];
	unsigned long handle;
	unsigned int num_aux;
};

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

static void init_realm_params(struct rmi_realm_params *params,
			      uintptr_t rtt)
{
	(void)memset(params, 0, sizeof(*params));
	params->s2sz = arch_feat_get_pa_width();
	params->rtt_base = rtt;
	params->rtt_num_start = 1U;
	params->num_bps = 1U;
	params->num_wps = 1U;
	params->algorithm = RMI_HASH_SHA_256;
}

static void init_test_realm(struct test_realm *realm)
{
	struct rmi_realm_params *params;

	(void)memset(realm, 0, sizeof(*realm));
	realm->rd = test_helpers_allocate_granules(1U);
	realm->params = test_helpers_allocate_granules(1U);
	realm->rtt = test_helpers_allocate_granules(1U);
	realm->addr_list = test_helpers_allocate_granules(1U);

	CHECK_TRUE(delegate_range(realm->rd, realm->rd + GRANULE_SIZE));
	CHECK_TRUE(delegate_range(realm->rtt, realm->rtt + GRANULE_SIZE));

	params = (struct rmi_realm_params *)realm->params;
	init_realm_params(params, realm->rtt);
}

static void start_realm_create(struct test_realm *realm)
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
		    (unsigned long)granule_unlocked_state(find_granule(realm->rd)));
	CHECK_EQUAL(GRANULE_STATE_DELEGATED,
		    (unsigned long)granule_unlocked_state(find_granule(realm->rtt)));
}

static void allocate_realm_aux(struct test_realm *realm, bool separated)
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

static void donate_realm_aux(struct test_realm *realm)
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
						find_granule(realm->aux[i])));
	}
}

static void release_realm_create_context(struct test_realm *realm)
{
	CHECK_TRUE(sro_ctx_find(realm->handle));
	sro_ctx_release();
}

static void transition_granule(uintptr_t addr, unsigned char from,
			       unsigned char to)
{
	struct granule *g = find_granule(addr);

	CHECK_TRUE(g != NULL);
	granule_lock(g, from);
	granule_unlock_transition(g, to);
}

static void init_destroy_realm(struct test_realm *realm, bool separated_aux)
{
	struct granule *g_aux[MAX_RD_AUX_GRANULES];
	struct sarray_hdr *map;
	struct rd_aux *rd_aux;
	struct rd *rd;
	unsigned int mecid;
	unsigned int vmid;

	(void)memset(realm, 0, sizeof(*realm));
	realm->rd = test_helpers_allocate_granules(1U);
	realm->rtt = test_helpers_allocate_granules(1U);
	realm->addr_list = test_helpers_allocate_granules(1U);
	realm->num_aux = MAX_RD_AUX_GRANULES;

	CHECK_TRUE(delegate_range(realm->rd, realm->rd + GRANULE_SIZE));
	CHECK_TRUE(delegate_range(realm->rtt, realm->rtt + GRANULE_SIZE));
	transition_granule(realm->rtt, GRANULE_STATE_DELEGATED,
			   GRANULE_STATE_RTT);

	for (unsigned int i = 0U; i < realm->num_aux; i++) {
		realm->aux[i] = test_helpers_allocate_granules(1U);
		CHECK_TRUE(delegate_range(realm->aux[i],
					  realm->aux[i] + GRANULE_SIZE));
		transition_granule(realm->aux[i], GRANULE_STATE_DELEGATED,
				   GRANULE_STATE_RD_AUX);
		g_aux[i] = find_granule(realm->aux[i]);

		if (separated_aux && ((i + 1U) < realm->num_aux)) {
			(void)test_helpers_allocate_granules(1U);
		}
	}

	rd_aux = (struct rd_aux *)
		buffer_rd_aux_granules_map_zeroed(g_aux, realm->num_aux);
	CHECK_TRUE(rd_aux != NULL);
	map = sarray_init_vdev_map(&rd_aux->vdev_map_hnd,
				   rd_aux->vdev_map_mem,
				   sizeof(rd_aux->vdev_map_mem));
	CHECK_TRUE(map != NULL);
	buffer_rd_aux_granules_unmap(rd_aux, realm->num_aux);

	CHECK_TRUE(vmid_alloc(&vmid));
	CHECK_TRUE(mecid_alloc(&mecid, true));

	rd = (struct rd *)realm->rd;
	(void)memset(rd, 0, sizeof(*rd));
	set_rd_state(rd, REALM_NEW);
	rd->num_rd_aux = realm->num_aux;
	rd->s2_ctx[0].g_rtt = find_granule(realm->rtt);
	rd->s2_ctx[0].num_root_rtts = 1U;
	rd->s2_ctx[0].vmid = (unsigned short)vmid;
	rd->s2_ctx[0].mecid = mecid;
	for (unsigned int i = 0U; i < realm->num_aux; i++) {
		rd->aux_granules[i] = g_aux[i];
	}

	transition_granule(realm->rd, GRANULE_STATE_DELEGATED,
			   GRANULE_STATE_RD);
}

static unsigned long start_realm_destroy(struct test_realm *realm)
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
		    (unsigned long)granule_unlocked_state(find_granule(realm->rd)));

	return res.x[1];
}

static void check_realm_destroyed(const struct test_realm *realm)
{
	CHECK_EQUAL(GRANULE_STATE_DELEGATED,
		    (unsigned long)granule_unlocked_state(find_granule(realm->rd)));
	CHECK_EQUAL(GRANULE_STATE_DELEGATED,
		    (unsigned long)granule_unlocked_state(find_granule(realm->rtt)));

	for (unsigned int i = 0U; i < realm->num_aux; i++) {
		CHECK_EQUAL(GRANULE_STATE_DELEGATED,
			    (unsigned long)granule_unlocked_state(
						find_granule(realm->aux[i])));
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
	struct test_realm realm;

	init_test_realm(&realm);
	start_realm_create(&realm);
	allocate_realm_aux(&realm, false);
	donate_realm_aux(&realm);

	/*
	 * The next continuation performs attestation hashing, which requires
	 * the EL0 app context unavailable in CppUTest.
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
	struct test_realm realm;
	struct smc_result res = {};
	return_code_t rc;
	unsigned long *addr_list;
	uintptr_t bad_aux;

	init_test_realm(&realm);
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
		    (unsigned long)granule_unlocked_state(find_granule(realm.rd)));
	CHECK_EQUAL(GRANULE_STATE_DELEGATED,
		    (unsigned long)granule_unlocked_state(find_granule(realm.rtt)));
	CHECK_EQUAL(GRANULE_STATE_DELEGATED,
		    (unsigned long)granule_unlocked_state(find_granule(realm.aux[0])));
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
	struct test_realm realm;
	struct rmi_realm_params *params;
	struct smc_result res = {};
	return_code_t rc;

	init_test_realm(&realm);
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
		    (unsigned long)granule_unlocked_state(find_granule(realm.rtt)));

	smc_op_mem_reclaim(realm.handle, realm.addr_list, realm.num_aux, &res);
	rc = unpack_return_code(res.x[0]);
	CHECK_EQUAL(RMI_INCOMPLETE, rc.status);
	CHECK_EQUAL(RMI_OP_MEM_REQ_NONE,
		    (unsigned long)EXTRACT(RMI_OP_MEM_REQ, res.x[0]));

	smc_op_continue(realm.handle, 0UL, &res);
	CHECK_EQUAL(RMI_ERROR_INPUT, res.x[0]);
	CHECK_EQUAL(GRANULE_STATE_DELEGATED,
		    (unsigned long)granule_unlocked_state(find_granule(realm.rd)));
	for (unsigned int i = 0U; i < realm.num_aux; i++) {
		CHECK_EQUAL(GRANULE_STATE_DELEGATED,
			    (unsigned long)granule_unlocked_state(
						find_granule(realm.aux[i])));
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
	struct test_realm realm;
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
	struct test_realm realm;
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
