/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef RMI_TEST_HELPERS_H
#define RMI_TEST_HELPERS_H

#include <CppUTest/TestHarness.h>

extern "C" {
#include <arch_features.h>
#include <smc-handler.h>
#include <smc-rmi.h>
#include <status.h>
#include <string.h>
#include <test_helpers.h>
}

/* Host-owned addresses and donation records; RMI initializes the RD and REC. */
struct rmi_test_realm {
	uintptr_t rd;
	uintptr_t params;
	uintptr_t rtt;
	uintptr_t addr_list;
	uintptr_t aux[MAX_RD_AUX_GRANULES];
	unsigned long handle;
	unsigned int num_aux;
	uintptr_t (*allocate)(unsigned int count);
};

struct rmi_test_rec {
	uintptr_t rec;
	uintptr_t params;
	uintptr_t aux[MAX_REC_AUX_GRANULES];
	unsigned int num_aux;
};

/* Delegate an aligned host range, checking RMI status and forward progress. */
static inline void rmi_test_delegate(uintptr_t base, unsigned int count)
{
	uintptr_t top = base + (uintptr_t)count * GRANULE_SIZE;

	while (base < top) {
		struct smc_result res = {};

		smc_granule_range_delegate(base, top, &res);
		CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
		CHECK_TRUE((res.x[1] > base) && (res.x[1] <= top));
		base = res.x[1];
	}
}

/*
 * Allocate host inputs for a single-plane Realm with one root RTT. Boot RMM
 * first and hold no granule locks. The allocator returns fresh NS granules;
 * callers may adjust the RMI parameters before rmi_test_realm_create().
 */
static inline void rmi_test_realm_prepare(struct rmi_test_realm *realm,
	uintptr_t (*allocate)(unsigned int) = test_helpers_allocate_granules)
{
	struct rmi_realm_params *params;

	(void)memset(realm, 0, sizeof(*realm));
	realm->allocate = allocate;
	realm->rd = allocate(1U);
	realm->params = allocate(1U);
	realm->rtt = allocate(1U);
	realm->addr_list = allocate(1U);
	rmi_test_delegate(realm->rd, 1U);
	rmi_test_delegate(realm->rtt, 1U);

	params = (struct rmi_realm_params *)realm->params;
	(void)memset(params, 0, sizeof(*params));
	params->s2sz = arch_feat_get_pa_width();
	params->rtt_base = realm->rtt;
	params->rtt_num_start = 1U;
	params->num_bps = 1U;
	params->num_wps = 1U;
	params->algorithm = RMI_HASH_SHA_256;
}

/*
 * Complete a successful Realm/REC creation SRO. Allocate and donate the
 * requested auxiliary pages, returning their count and addresses in @aux.
 * @list is an NS granule. Separated pages exercise multiple reclaim entries.
 * The caller holds no granule locks and has no pending interrupt.
 */
static inline unsigned int rmi_test_complete_create(struct smc_result res,
	uintptr_t list, uintptr_t aux[], unsigned int capacity, bool separated,
	uintptr_t (*allocate)(unsigned int))
{
	unsigned long handle = res.x[1];
	unsigned long *descs = (unsigned long *)list;
	unsigned int count;

	CHECK_EQUAL(RMI_INCOMPLETE, unpack_return_code(res.x[0]).status);
	CHECK_EQUAL(RMI_OP_MEM_REQ_DONATE,
		    (unsigned long)EXTRACT(RMI_OP_MEM_REQ, res.x[0]));
	CHECK_EQUAL(RMI_PAGE_L3,
		    (unsigned long)EXTRACT(RMI_OP_DONATE_BLK_SIZE, res.x[2]));
	count = (unsigned int)EXTRACT(RMI_OP_DONATE_BLK_COUNT, res.x[2]);
	CHECK_TRUE((count > 0U) && (count <= capacity));

	for (unsigned int i = 0U; i < count; i++) {
		aux[i] = allocate(1U);
		rmi_test_delegate(aux[i], 1U);
		descs[i] = INPLACE(RMI_ADDR_RDESC_4K_SZ, RMI_PAGE_L3) |
			   INPLACE(RMI_ADDR_RDESC_4K_CNT, 1UL) |
			   INPLACE(RMI_ADDR_RDESC_4K_ADDR, aux[i] >> GRANULE_SHIFT) |
			   INPLACE(RMI_ADDR_RDESC_4K_ST, RMI_OP_MEM_DELEGATED);
		if (separated && ((i + 1U) < count)) {
			(void)allocate(1U);
		}
	}

	res = {};
	smc_op_mem_donate(handle, list, count, &res);
	CHECK_EQUAL(RMI_INCOMPLETE, unpack_return_code(res.x[0]).status);
	CHECK_EQUAL(RMI_OP_MEM_REQ_NONE,
		    (unsigned long)EXTRACT(RMI_OP_MEM_REQ, res.x[0]));
	CHECK_EQUAL(count, res.x[1]);

	/* Direct handler calls need the fresh result registers supplied by dispatch. */
	res = {};
	smc_op_continue(handle, 0UL, &res);
	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
	return count;
}

/* Create a prepared Realm through RMI, with optional gaps between AUX pages. */
static inline void rmi_test_realm_create(struct rmi_test_realm *realm,
					bool separated = false)
{
	struct smc_result res = {};

	smc_realm_create(realm->rd, realm->params, &res);
	realm->num_aux = rmi_test_complete_create(res, realm->addr_list,
		realm->aux, MAX_RD_AUX_GRANULES, separated, realm->allocate);
}

/*
 * Create a runnable REC with MPIDR 0 through RMI in a NEW Realm with no RECs.
 * Save donated AUX addresses for reclaim assertions; hold no granule locks.
 */
static inline void rmi_test_rec_create(struct rmi_test_realm *realm,
				     struct rmi_test_rec *rec, bool separated = false)
{
	struct smc_result res = {};
	struct rmi_rec_params *params;

	(void)memset(rec, 0, sizeof(*rec));
	rec->rec = realm->allocate(1U);
	rec->params = realm->allocate(1U);
	rmi_test_delegate(rec->rec, 1U);
	params = (struct rmi_rec_params *)rec->params;
	(void)memset(params, 0, sizeof(*params));
	params->flags = REC_PARAMS_FLAG_RUNNABLE;
	smc_rec_create(realm->rd, rec->rec, rec->params, &res);
	rec->num_aux = rmi_test_complete_create(res, realm->addr_list,
		rec->aux, MAX_REC_AUX_GRANULES, separated, realm->allocate);
}

/* Reclaim all AUX pages of a destroy SRO through an NS list, then complete it. */
static inline void rmi_test_reclaim(unsigned long handle, uintptr_t list,
				    unsigned int capacity)
{
	struct smc_result res = {};

	smc_op_mem_reclaim(handle, list, capacity, &res);
	CHECK_EQUAL(RMI_INCOMPLETE, unpack_return_code(res.x[0]).status);
	CHECK_EQUAL(RMI_OP_MEM_REQ_NONE,
		    (unsigned long)EXTRACT(RMI_OP_MEM_REQ, res.x[0]));
	res = {};
	smc_op_continue(handle, 0UL, &res);
	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
}

/*
 * Destroy a Realm that has no RECs, data mappings or non-root RTTs, returning
 * its RD, RTT and AUX pages to DELEGATED. The caller holds no granule locks.
 */
static inline void rmi_test_realm_destroy(struct rmi_test_realm *realm)
{
	struct smc_result res = {};

	smc_realm_terminate(realm->rd, &res);
	CHECK_EQUAL(RMI_SUCCESS, res.x[0]);
	res = {};
	smc_realm_destroy(realm->rd, &res);
	CHECK_EQUAL(RMI_INCOMPLETE, unpack_return_code(res.x[0]).status);
	rmi_test_reclaim(res.x[1], realm->addr_list, realm->num_aux);
}

#endif /* RMI_TEST_HELPERS_H */
