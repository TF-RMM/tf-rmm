/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <CppUTest/CommandLineTestRunner.h>
#include <CppUTest/TestHarness.h>

extern "C" {
#include <dev.h>
}

#include "rtt_data_test_helpers.h"

/*
 * RMI_PDEV_ABORT during a stream operation, and the RMI_PDEV_STREAM_COMPLETE
 * that follows it.
 *
 * DEN0137 2.0-bet3 B4.5.18.3: when the aborted operation is a stream
 * operation that cannot be reverted, pdev.op becomes
 * PDEV_OP_STREAM_COMPLETE and pdev.state becomes PDEV_ERROR
 * (stream_cannot_revert_op, stream_cannot_revert_state); comm_state
 * becomes DEV_COMM_IDLE. B4.5.25: RMI_PDEV_STREAM_COMPLETE accepts a PDEV
 * in PDEV_ERROR (pdev_1_state, pdev_1_comm_state) and then disconnects and
 * releases the stream (connect_err_abrt_*, disconnect_error*).
 *
 * The tests install two PDEV objects and their stream granule directly,
 * with the stream in the middle of a disconnect or connect, the way
 * vdev_ownership_tests.cpp installs device objects. The PDEVs have no app
 * auxiliary granules, so the abort does not reach the device assignment
 * app.
 */

#define ABORT_TEST_RTT_START_IDX	119800U
#define ABORT_TEST_NS_LIST_START_IDX	128000U

#define ABORT_TEST_STREAM_TYPE		((unsigned char)RMI_PDEV_STREAM_NCOH)

struct abort_test_objects {
	uintptr_t pd1;
	uintptr_t pd2;
	uintptr_t stream_aux;
	unsigned long handle;
};

TEST_GROUP(pdev_abort_stream_tests) {
	TEST_SETUP()
	{
		static bool counters_initialized;

		if (!counters_initialized) {
			reset_data_granule_allocation();
			g_rtt_next_idx = ABORT_TEST_RTT_START_IDX;
			g_ns_list_next_idx = ABORT_TEST_NS_LIST_START_IDX;
			counters_initialized = true;
		}
		test_helpers_init();
		test_helpers_rmm_start(false);
		host_util_set_cpuid(0U);
		test_helpers_expect_assert_fail(false);
	}

	TEST_TEARDOWN()
	{
	}
};

/* Turn a delegated granule into a READY PDEV taking part in one stream. */
static void install_pdev(uintptr_t pdev_pa, uintptr_t stream_aux_pa,
			 unsigned long op, unsigned int comm_state)
{
	struct granule *g_pdev = tr_find_fine_granule(pdev_pa);
	struct pdev *pd;

	granule_lock(g_pdev, GRANULE_STATE_DELEGATED);
	pd = (struct pdev *)buffer_granule_map_zeroed(g_pdev, SLOT_PDEV);
	CHECK_TRUE(pd != NULL);
	pd->g_pdev = g_pdev;
	pd->rmi_state = RMI_PDEV_STATE_READY;
	pd->dev_comm_state = comm_state;
	pd->op.curr = op;
	pd->op.op_stream_type = ABORT_TEST_STREAM_TYPE;
	pd->g_stream_aux = tr_find_fine_granule(stream_aux_pa);
	pd->associated_stream_count = 1UL;
	buffer_unmap(pd);
	granule_unlock_transition(g_pdev, GRANULE_STATE_PDEV);
}

/* Turn a delegated granule into the stream granule of @pd1 and @pd2. */
static void install_stream(uintptr_t stream_aux_pa, uintptr_t pd1,
			   uintptr_t pd2, unsigned long state)
{
	struct granule *g_aux = tr_find_fine_granule(stream_aux_pa);
	struct pdev_stream *streams;

	granule_lock(g_aux, GRANULE_STATE_DELEGATED);
	streams = (struct pdev_stream *)buffer_granule_map_zeroed(
						g_aux, SLOT_PDEV_STREAM);
	CHECK_TRUE(streams != NULL);
	streams[ABORT_TEST_STREAM_TYPE].pd1_addr = pd1;
	streams[ABORT_TEST_STREAM_TYPE].pd2_addr = pd2;
	streams[ABORT_TEST_STREAM_TYPE].state = state;
	streams[ABORT_TEST_STREAM_TYPE].op_state = STREAM_OP_STATE_START;
	streams[ABORT_TEST_STREAM_TYPE].taken = true;
	buffer_unmap(streams);
	granule_unlock_transition(g_aux, GRANULE_STATE_PDEV_AUX);
}

/*
 * Build a stream in @stream_state between two PDEVs. pd1 is in @pd1_op with
 * communication @pd1_comm; pd2 is in @pd2_op with communication @pd2_comm.
 */
static void build_objects(struct abort_test_objects *o,
			  unsigned long stream_state,
			  unsigned long pd1_op, unsigned int pd1_comm,
			  unsigned long pd2_op, unsigned int pd2_comm)
{
	uintptr_t base = reserve_delegated_granules(3U);

	o->pd1 = base;
	o->pd2 = base + GRANULE_SIZE;
	o->stream_aux = base + (2UL * GRANULE_SIZE);
	/* The stream handle is the first PDEV address plus the stream type. */
	o->handle = o->pd1 + ABORT_TEST_STREAM_TYPE;

	install_stream(o->stream_aux, o->pd1, o->pd2, stream_state);
	install_pdev(o->pd1, o->stream_aux, pd1_op, pd1_comm);
	install_pdev(o->pd2, o->stream_aux, pd2_op, pd2_comm);
}

static void read_pdev(uintptr_t pdev_pa, struct pdev *out)
{
	struct granule *g_pdev = tr_find_fine_granule(pdev_pa);
	struct pdev *pd;

	granule_lock(g_pdev, GRANULE_STATE_PDEV);
	pd = (struct pdev *)buffer_granule_map(g_pdev, SLOT_PDEV);
	CHECK_TRUE(pd != NULL);
	(void)memcpy(out, pd, sizeof(*out));
	buffer_unmap(pd);
	granule_unlock(g_pdev);
}

static void read_stream(uintptr_t stream_aux_pa, struct pdev_stream *out)
{
	struct granule *g_aux = tr_find_fine_granule(stream_aux_pa);
	struct pdev_stream *streams;

	granule_lock(g_aux, GRANULE_STATE_PDEV_AUX);
	streams = (struct pdev_stream *)buffer_granule_map(g_aux,
							   SLOT_PDEV_STREAM);
	CHECK_TRUE(streams != NULL);
	(void)memcpy(out, &streams[ABORT_TEST_STREAM_TYPE], sizeof(*out));
	buffer_unmap(streams);
	granule_unlock(g_aux);
}

TEST(pdev_abort_stream_tests, abort_of_stream_operation_leaves_it_to_stream_complete)
{
	struct abort_test_objects o;
	struct smc_result res = {};
	struct pdev pd;

	build_objects(&o, PDEV_STREAM_DISCONNECTING,
		      PDEV_OP_DISCONNECT, DEV_COMM_PENDING,
		      PDEV_OP_DISCONNECT, DEV_COMM_PENDING);

	smc_pdev_abort(o.pd1, &res);

	UNSIGNED_LONGS_EQUAL(RMI_SUCCESS, res.x[0]);
	read_pdev(o.pd1, &pd);
	UNSIGNED_LONGS_EQUAL(DEV_COMM_IDLE, pd.dev_comm_state);
	UNSIGNED_LONGS_EQUAL(PDEV_OP_STREAM_COMPLETE, pd.op.curr);
	UNSIGNED_LONGS_EQUAL(RMI_PDEV_STATE_ERROR, pd.rmi_state);
}

/* Nothing to abort: the command fails and the PDEV is untouched. */
TEST(pdev_abort_stream_tests, abort_with_idle_communication_is_rejected)
{
	struct abort_test_objects o;
	struct smc_result res = {};
	struct pdev pd;

	build_objects(&o, PDEV_STREAM_DISCONNECTING,
		      PDEV_OP_DISCONNECT, DEV_COMM_IDLE,
		      PDEV_OP_DISCONNECT, DEV_COMM_PENDING);

	smc_pdev_abort(o.pd1, &res);

	UNSIGNED_LONGS_EQUAL(RMI_ERROR_DEVICE, res.x[0]);
	read_pdev(o.pd1, &pd);
	UNSIGNED_LONGS_EQUAL(PDEV_OP_DISCONNECT, pd.op.curr);
	UNSIGNED_LONGS_EQUAL(RMI_PDEV_STATE_READY, pd.rmi_state);
}

TEST(pdev_abort_stream_tests, stream_complete_after_abort_disconnects_the_stream)
{
	struct abort_test_objects o;
	struct smc_result res = {};
	struct pdev_stream stream;
	struct pdev pd;

	build_objects(&o, PDEV_STREAM_DISCONNECTING,
		      PDEV_OP_DISCONNECT, DEV_COMM_PENDING,
		      PDEV_OP_DISCONNECT, DEV_COMM_PENDING);
	smc_pdev_abort(o.pd1, &res);
	UNSIGNED_LONGS_EQUAL(RMI_SUCCESS, res.x[0]);
	smc_pdev_abort(o.pd2, &res);
	UNSIGNED_LONGS_EQUAL(RMI_SUCCESS, res.x[0]);

	smc_pdev_stream_complete(o.pd1, o.pd2, o.handle, &res);

	UNSIGNED_LONGS_EQUAL(RMI_SUCCESS, res.x[0]);
	read_stream(o.stream_aux, &stream);
	UNSIGNED_LONGS_EQUAL(PDEV_STREAM_DISCONNECTED, stream.state);
	CHECK_FALSE(stream.taken);
	read_pdev(o.pd1, &pd);
	UNSIGNED_LONGS_EQUAL(PDEV_OP_NONE, pd.op.curr);
	UNSIGNED_LONGS_EQUAL(0UL, pd.associated_stream_count);
	read_pdev(o.pd2, &pd);
	UNSIGNED_LONGS_EQUAL(PDEV_OP_NONE, pd.op.curr);
	UNSIGNED_LONGS_EQUAL(0UL, pd.associated_stream_count);
}

/* A connect aborted on one side is torn down by STREAM_COMPLETE. */
TEST(pdev_abort_stream_tests, stream_complete_after_aborted_connect_releases_the_stream)
{
	struct abort_test_objects o;
	struct smc_result res = {};
	struct pdev_stream stream;
	struct pdev pd;

	build_objects(&o, PDEV_STREAM_CONNECTING,
		      PDEV_OP_CONNECT, DEV_COMM_PENDING,
		      PDEV_OP_STREAM_COMPLETE, DEV_COMM_IDLE);
	smc_pdev_abort(o.pd1, &res);
	UNSIGNED_LONGS_EQUAL(RMI_SUCCESS, res.x[0]);

	smc_pdev_stream_complete(o.pd1, o.pd2, o.handle, &res);

	UNSIGNED_LONGS_EQUAL(RMI_SUCCESS, res.x[0]);
	read_stream(o.stream_aux, &stream);
	UNSIGNED_LONGS_EQUAL(PDEV_STREAM_DISCONNECTED, stream.state);
	CHECK_FALSE(stream.taken);
	read_pdev(o.pd1, &pd);
	UNSIGNED_LONGS_EQUAL(0UL, pd.associated_stream_count);
	read_pdev(o.pd2, &pd);
	UNSIGNED_LONGS_EQUAL(0UL, pd.associated_stream_count);
}

/* Without an abort a finished connect still ends in CONNECTED. */
TEST(pdev_abort_stream_tests, stream_complete_without_error_connects)
{
	struct abort_test_objects o;
	struct smc_result res = {};
	struct pdev_stream stream;
	struct pdev pd;

	build_objects(&o, PDEV_STREAM_CONNECTING,
		      PDEV_OP_STREAM_COMPLETE, DEV_COMM_IDLE,
		      PDEV_OP_STREAM_COMPLETE, DEV_COMM_IDLE);

	smc_pdev_stream_complete(o.pd1, o.pd2, o.handle, &res);

	UNSIGNED_LONGS_EQUAL(RMI_SUCCESS, res.x[0]);
	read_stream(o.stream_aux, &stream);
	UNSIGNED_LONGS_EQUAL(PDEV_STREAM_CONNECTED, stream.state);
	CHECK_TRUE(stream.taken);
	read_pdev(o.pd1, &pd);
	UNSIGNED_LONGS_EQUAL(PDEV_OP_NONE, pd.op.curr);
	UNSIGNED_LONGS_EQUAL(1UL, pd.associated_stream_count);
}
