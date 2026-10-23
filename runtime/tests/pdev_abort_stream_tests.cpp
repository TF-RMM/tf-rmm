/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <CppUTest/TestHarness.h>

extern "C" {
#include <buffer.h>
#include <dev.h>
#include <glob_data.h>
#include <host_da.h>
#include <host_rmi_wrappers.h>
#include <host_utils.h>
#include <string.h>
#include <test_helpers.h>
}

/*
 * Create PDEVs and streams through RMI, using the host DA driver and SPDM
 * responder for device communication. The fixture recreates the devices
 * and responder for every test.
 * Aborted stream operations must remain available to STREAM_COMPLETE so it
 * can release the stream and its PDEV associations.
 */

/* Finish STOP even when the PDEV remains in ERROR until its app exits. */
static void stop_and_destroy(struct host_pdev *pdev, bool ep)
{
	void *addr = host_pdev_ptr(pdev, ep);
	struct rmi_dev_comm_data *comm = host_pdev_comm_data(pdev);
	struct smc_result res = {};

	host_rmi_pdev_stop(addr, &res);
	UNSIGNED_LONGS_EQUAL(RMI_SUCCESS, res.x[0]);
	comm->enter.status = RMI_DEV_COMM_ENTER_STATUS_NONE;
	comm->enter.resp_len = 0U;
	for (unsigned int attempt = 0U; attempt < 16U; attempt++) {
		host_rmi_pdev_communicate(addr, comm, &res);
		UNSIGNED_LONGS_EQUAL(RMI_SUCCESS, res.x[0]);
		host_rmi_pdev_get_state(addr, &res);
		UNSIGNED_LONGS_EQUAL(RMI_SUCCESS, res.x[0]);
		if (res.x[1] == RMI_PDEV_STATE_STOPPED) {
			break;
		}
		/* Fail remaining exchanges, as in the existing abort/STOP tests. */
		comm->enter.status = RMI_DEV_COMM_ENTER_STATUS_ERROR;
		comm->enter.resp_len = 0U;
	}
	UNSIGNED_LONGS_EQUAL(RMI_PDEV_STATE_STOPPED, res.x[1]);
	CHECK_EQUAL(0, host_pdev_destroy(pdev, ep));
	host_pdev_cleanup(pdev, ep);
}

static unsigned long begin_connect(struct host_pdev *pdev)
{
	struct rmi_pdev_stream_params *params;
	struct smc_result res = {};
	unsigned long handle;

	params = (struct rmi_pdev_stream_params *)allocate_granule(1U);
	(void)memset(params, 0, sizeof(*params));
	params->stream_type = RMI_PDEV_STREAM_NCOH;
	params->pdev_1 = (unsigned long)host_pdev_ptr(pdev, true);
	params->pdev_2 = (unsigned long)host_pdev_ptr(pdev, false);
	host_rmi_pdev_stream_connect(params, &handle, &res);
	UNSIGNED_LONGS_EQUAL(RMI_SUCCESS, res.x[0]);
	return handle;
}

static void communicate(struct host_pdev *pdev, bool ep, bool wait_for_stream)
{
	CHECK_EQUAL(0, host_dev_communicate(NULL, pdev, ep, NULL,
					 RMI_PDEV_STATE_READY, wait_for_stream));
}

/* The root port and endpoint must each wait for the other before finishing. */
static void complete_communication(struct host_pdev *pdev)
{
	communicate(pdev, false, true);
	communicate(pdev, true, true);
	communicate(pdev, false, false);
	communicate(pdev, true, false);
}

static void complete_stream(struct host_pdev *pdev, unsigned long handle)
{
	struct smc_result res = {};

	host_rmi_pdev_stream_complete(host_pdev_ptr(pdev, true),
				      host_pdev_ptr(pdev, false), handle, &res);
	UNSIGNED_LONGS_EQUAL(RMI_SUCCESS, res.x[0]);
}

static void begin_disconnect(struct host_pdev *pdev, unsigned long handle)
{
	struct smc_result res = {};

	host_rmi_pdev_stream_disconnect(host_pdev_ptr(pdev, true),
					host_pdev_ptr(pdev, false), handle, &res);
	UNSIGNED_LONGS_EQUAL(RMI_SUCCESS, res.x[0]);
}

static void disconnect_stream(struct host_pdev *pdev, unsigned long handle)
{
	begin_disconnect(pdev, handle);
	complete_communication(pdev);
	complete_stream(pdev, handle);
}

TEST_GROUP(pdev_abort_stream_tests) {
	struct host_pdev *pdev;
	void *endpoint;
	void *root_port;
	unsigned long handle;
	int pdev_id;

	TEST_SETUP()
	{
		pdev_id = 0;
		test_helpers_init();
		host_util_pas_enable(true);
		test_helpers_allocate_reset();
		test_helpers_rmm_start(false);
		host_util_set_cpuid(0U);
		test_helpers_expect_assert_fail(false);
		if (glob_data_get_rmm_state() == RMM_STATE_INIT) {
			CHECK_TRUE(glob_data_transition_rmm_state(RMM_STATE_INIT,
								RMM_STATE_ACTIVE));
		}
		CHECK_EQUAL(RMM_STATE_ACTIVE, glob_data_get_rmm_state());
		test_helpers_spdm_responder_start();

		pdev_id = host_pdev_probe_and_setup();
		CHECK_TRUE(pdev_id > 0);
		pdev = host_pdev_current();
		endpoint = host_pdev_ptr(pdev, true);
		root_port = host_pdev_ptr(pdev, false);
		/* Leave the session established and start a fresh stream operation. */
		CHECK_EQUAL(0, host_pdev_stream_disconnect(pdev));
		handle = begin_connect(pdev);
	}

	TEST_TEARDOWN()
	{
		/* Successful tests release the stream before reclaiming its PDEVs. */
		if (pdev_id > 0) {
			stop_and_destroy(pdev, false);
			stop_and_destroy(pdev, true);
		}
		host_util_stop_spdm_responder();
		host_util_pas_enable(false);
	}
};

/* Inspect an ABI-created PDEV without changing its state. */
static void read_pdev(void *pdev_addr, struct pdev *out)
{
	struct granule *g_pdev = tr_find_fine_granule((uintptr_t)pdev_addr);
	struct pdev *pd;

	granule_lock(g_pdev, GRANULE_STATE_PDEV);
	pd = (struct pdev *)buffer_granule_map(g_pdev, SLOT_PDEV);
	CHECK_TRUE(pd != NULL);
	(void)memcpy(out, pd, sizeof(*out));
	buffer_unmap(pd);
	granule_unlock(g_pdev);
}

/* Inspect the stream owned by the endpoint, including after it is released. */
static void read_stream(void *endpoint, struct pdev_stream *out)
{
	struct pdev pd;
	struct pdev_stream *streams;

	read_pdev(endpoint, &pd);
	granule_lock(pd.g_stream_aux, GRANULE_STATE_PDEV_AUX);
	streams = (struct pdev_stream *)buffer_granule_map(pd.g_stream_aux,
							   SLOT_PDEV_STREAM);
	CHECK_TRUE(streams != NULL);
	(void)memcpy(out, &streams[RMI_PDEV_STREAM_NCOH], sizeof(*out));
	buffer_unmap(streams);
	granule_unlock(pd.g_stream_aux);
}

/*
 * Verify that aborting active stream communication preserves its completion step.
 *
 * Setup: Create the endpoint and root-port PDEVs through RMI, establish their
 * stream, and start a disconnect. Let the root port wait for the endpoint,
 * then yield the endpoint app on its first device request.
 * Action: Abort the endpoint, abort the waiting root port, and call
 * RMI_PDEV_STREAM_COMPLETE.
 * Expected: The endpoint abort succeeds and leaves the PDEV in ERROR with
 * IDLE communication and PDEV_OP_STREAM_COMPLETE. Stream completion succeeds,
 * and teardown can stop and destroy both PDEVs.
 */
TEST(pdev_abort_stream_tests, abort_of_stream_operation_leaves_it_to_stream_complete)
{
	struct smc_result res = {};
	struct rmi_dev_comm_data *comm = host_pdev_comm_data(pdev);
	struct pdev pd;

	complete_communication(pdev);
	complete_stream(pdev, handle);
	begin_disconnect(pdev, handle);
	communicate(pdev, false, true);
	/* Abort while the endpoint app is waiting for its first device response. */
	comm->enter.status = RMI_DEV_COMM_ENTER_STATUS_NONE;
	comm->enter.resp_len = 0U;
	host_rmi_pdev_communicate(endpoint, comm, &res);
	UNSIGNED_LONGS_EQUAL(RMI_SUCCESS, res.x[0]);
	CHECK_TRUE((comm->exit.flags & RMI_DEV_COMM_EXIT_FLAGS_REQ_SEND_BIT) != 0U);
	read_pdev(endpoint, &pd);
	UNSIGNED_LONGS_EQUAL(DEV_COMM_ACTIVE, pd.dev_comm_state);
	UNSIGNED_LONGS_EQUAL(PDEV_OP_DISCONNECT, pd.op.curr);

	host_rmi_pdev_abort(endpoint, &res);

	UNSIGNED_LONGS_EQUAL(RMI_SUCCESS, res.x[0]);
	read_pdev(endpoint, &pd);
	UNSIGNED_LONGS_EQUAL(DEV_COMM_IDLE, pd.dev_comm_state);
	UNSIGNED_LONGS_EQUAL(PDEV_OP_STREAM_COMPLETE, pd.op.curr);
	UNSIGNED_LONGS_EQUAL(RMI_PDEV_STATE_ERROR, pd.rmi_state);
	host_rmi_pdev_abort(root_port, &res);
	UNSIGNED_LONGS_EQUAL(RMI_SUCCESS, res.x[0]);
	complete_stream(pdev, handle);
}

/*
 * Verify that ABORT rejects idle communication without losing stream completion.
 *
 * Setup: Create both PDEVs and start a stream connect through RMI. Finish
 * communication on both sides, leaving stream completion pending.
 * Action: Call RMI_PDEV_ABORT on the endpoint, then complete the stream and
 * disconnect it normally.
 * Expected: ABORT returns RMI_ERROR_DEVICE. The endpoint remains READY with
 * IDLE communication and PDEV_OP_STREAM_COMPLETE. Stream completion and the
 * subsequent disconnect succeed.
 */
TEST(pdev_abort_stream_tests, abort_with_idle_communication_is_rejected)
{
	struct smc_result res = {};
	struct pdev pd;

	complete_communication(pdev);
	host_rmi_pdev_abort(endpoint, &res);

	UNSIGNED_LONGS_EQUAL(RMI_ERROR_DEVICE, res.x[0]);
	read_pdev(endpoint, &pd);
	UNSIGNED_LONGS_EQUAL(DEV_COMM_IDLE, pd.dev_comm_state);
	UNSIGNED_LONGS_EQUAL(PDEV_OP_STREAM_COMPLETE, pd.op.curr);
	UNSIGNED_LONGS_EQUAL(RMI_PDEV_STATE_READY, pd.rmi_state);
	complete_stream(pdev, handle);
	disconnect_stream(pdev, handle);
}

/*
 * Verify that completing an aborted disconnect releases the stream associations.
 *
 * Setup: Create both PDEVs and connect their stream through RMI. Start a
 * disconnect, leaving communication PENDING on both sides.
 * Action: Abort both PDEVs before either begins disconnect communication,
 * then call RMI_PDEV_STREAM_COMPLETE.
 * Expected: Both aborts and stream completion succeed. The stream becomes
 * DISCONNECTED and its slot is released. Both PDEVs have PDEV_OP_NONE and
 * zero associated streams, allowing teardown to stop and destroy them.
 */
TEST(pdev_abort_stream_tests, stream_complete_after_abort_disconnects_the_stream)
{
	struct smc_result res = {};
	struct pdev_stream stream;
	struct pdev pd;

	complete_communication(pdev);
	complete_stream(pdev, handle);
	begin_disconnect(pdev, handle);
	/* Abort both sides before either starts communication. */
	host_rmi_pdev_abort(endpoint, &res);
	UNSIGNED_LONGS_EQUAL(RMI_SUCCESS, res.x[0]);
	host_rmi_pdev_abort(root_port, &res);
	UNSIGNED_LONGS_EQUAL(RMI_SUCCESS, res.x[0]);

	complete_stream(pdev, handle);

	read_stream(endpoint, &stream);
	UNSIGNED_LONGS_EQUAL(PDEV_STREAM_DISCONNECTED, stream.state);
	CHECK_FALSE(stream.taken);
	read_pdev(endpoint, &pd);
	UNSIGNED_LONGS_EQUAL(PDEV_OP_NONE, pd.op.curr);
	UNSIGNED_LONGS_EQUAL(0UL, pd.associated_stream_count);
	read_pdev(root_port, &pd);
	UNSIGNED_LONGS_EQUAL(PDEV_OP_NONE, pd.op.curr);
	UNSIGNED_LONGS_EQUAL(0UL, pd.associated_stream_count);
}

/*
 * Verify that a connect aborted on one side releases the stream.
 *
 * Setup: Create both PDEVs and start a stream connect through RMI. Finish
 * root-port communication so it is IDLE with PDEV_OP_STREAM_COMPLETE, while
 * the endpoint still waits for stream synchronization.
 * Action: Abort the endpoint and call RMI_PDEV_STREAM_COMPLETE with the
 * normally completed root port.
 * Expected: The abort and stream completion succeed. The stream becomes
 * DISCONNECTED, its slot is released, and both PDEV association counts reach
 * zero. Teardown can stop and destroy both PDEVs.
 */
TEST(pdev_abort_stream_tests, stream_complete_after_aborted_connect_releases_the_stream)
{
	struct smc_result res = {};
	struct pdev_stream stream;
	struct pdev pd;

	communicate(pdev, false, true);
	communicate(pdev, true, true);
	/* Finish the root port while the endpoint still waits for stream sync. */
	communicate(pdev, false, false);
	read_pdev(root_port, &pd);
	UNSIGNED_LONGS_EQUAL(PDEV_OP_STREAM_COMPLETE, pd.op.curr);
	UNSIGNED_LONGS_EQUAL(DEV_COMM_IDLE, pd.dev_comm_state);
	host_rmi_pdev_abort(endpoint, &res);
	UNSIGNED_LONGS_EQUAL(RMI_SUCCESS, res.x[0]);

	complete_stream(pdev, handle);

	read_stream(endpoint, &stream);
	UNSIGNED_LONGS_EQUAL(PDEV_STREAM_DISCONNECTED, stream.state);
	CHECK_FALSE(stream.taken);
	read_pdev(endpoint, &pd);
	UNSIGNED_LONGS_EQUAL(0UL, pd.associated_stream_count);
	read_pdev(root_port, &pd);
	UNSIGNED_LONGS_EQUAL(0UL, pd.associated_stream_count);
}

/*
 * Verify that a successful connect keeps the stream and its association.
 *
 * Setup: Create both PDEVs and start a stream connect through RMI, then
 * finish communication on both sides without an abort or device error.
 * Action: Call RMI_PDEV_STREAM_COMPLETE and query RMI_PDEV_STREAM_INFO.
 * Expected: Completion succeeds and both the ABI query and internal stream
 * state report CONNECTED. The stream slot remains allocated, and the endpoint
 * has PDEV_OP_NONE with one associated stream. A normal disconnect releases
 * the stream before teardown stops and destroys the PDEVs.
 */
TEST(pdev_abort_stream_tests, stream_complete_without_error_connects)
{
	struct smc_result res = {};
	struct pdev_stream stream;
	struct pdev pd;

	complete_communication(pdev);
	complete_stream(pdev, handle);

	host_rmi_pdev_stream_info(endpoint, root_port, handle, &res);
	UNSIGNED_LONGS_EQUAL(RMI_SUCCESS, res.x[0]);
	UNSIGNED_LONGS_EQUAL(RMI_PDEV_STREAM_CONNECTED, res.x[1]);
	read_stream(endpoint, &stream);
	UNSIGNED_LONGS_EQUAL(PDEV_STREAM_CONNECTED, stream.state);
	CHECK_TRUE(stream.taken);
	read_pdev(endpoint, &pd);
	UNSIGNED_LONGS_EQUAL(PDEV_OP_NONE, pd.op.curr);
	UNSIGNED_LONGS_EQUAL(1UL, pd.associated_stream_count);
	disconnect_stream(pdev, handle);
}
