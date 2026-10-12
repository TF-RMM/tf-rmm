/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <CppUTest/TestHarness.h>

extern "C" {
#include <app.h>
#include <dev.h>
#include <pdev_comm.h>
#include <string.h>
}

/*
 * Exercise PDEV state transitions directly. Device-assignment app outcomes
 * are represented by the app status and app_unwound arguments supplied to
 * pdev_comm_complete(); these tests perform no SPDM or device communication.
 */
TEST_GROUP(pdev_comm_tests) {
	struct pdev pd;

	TEST_SETUP()
	{
		(void)memset(&pd, 0, sizeof(pd));
		pd.rmi_flags = INPLACE(RMI_PDEV_FLAGS_CATEGORY,
				       RMI_PDEV_ENDPOINT_ACCEL_OFF_CHIP);
		pdev_comm_init(&pd);
	}
};

/* Verify endpoint initialization and secure-session establishment. */
TEST(pdev_comm_tests, connection_and_session_completion)
{
	pdev_comm_complete(&pd, DEV_ASSIGN_STATUS_SUCCESS, true);
	CHECK_EQUAL(RMI_PDEV_STATE_NEEDS_KEY, pd.rmi_state);
	CHECK_EQUAL(DEV_COMM_IDLE, pd.dev_comm_state);

	pdev_comm_begin_key(&pd);
	CHECK_EQUAL(RMI_PDEV_STATE_HAS_KEY, pd.rmi_state);
	CHECK_EQUAL(DEV_COMM_PENDING, pd.dev_comm_state);

	pdev_comm_complete(&pd, DEV_ASSIGN_STATUS_COMM_BLOCKED_APP_YIELD, false);
	CHECK_EQUAL(DEV_COMM_ACTIVE, pd.dev_comm_state);
	CHECK_EQUAL(RMI_PDEV_STATE_HAS_KEY, pd.rmi_state);

	pdev_comm_complete(&pd, DEV_ASSIGN_STATUS_SUCCESS, true);
	CHECK_EQUAL(RMI_PDEV_STATE_READY, pd.rmi_state);
	CHECK_EQUAL(DEV_COMM_IDLE, pd.dev_comm_state);
	CHECK_EQUAL(PDEV_OP_NONE, pd.op.curr);
}

/* Verify that a root port reaches READY without key setup. */
TEST(pdev_comm_tests, root_port_connection_completes_ready)
{
	pd.rmi_flags = INPLACE(RMI_PDEV_FLAGS_CATEGORY, RMI_PDEV_ROOTPORT);
	pdev_comm_complete(&pd, DEV_ASSIGN_STATUS_SUCCESS, true);
	CHECK_EQUAL(RMI_PDEV_STATE_READY, pd.rmi_state);
	CHECK_EQUAL(DEV_COMM_IDLE, pd.dev_comm_state);
}

/* Verify that a failed initial exchange remains stoppable. */
TEST(pdev_comm_tests, failed_initial_connection_can_stop)
{
	pdev_comm_complete(&pd, DEV_ASSIGN_STATUS_ERROR, true);
	CHECK_EQUAL(RMI_PDEV_STATE_ERROR, pd.rmi_state);
	CHECK_EQUAL(DEV_COMM_IDLE, pd.dev_comm_state);
	CHECK_EQUAL(PDEV_OP_NONE, pd.op.curr);

	pdev_comm_begin(&pd, PDEV_OP_STOP);
	pdev_comm_complete(&pd, DEV_ASSIGN_STATUS_ERROR, true);
	CHECK_EQUAL(RMI_PDEV_STATE_STOPPED, pd.rmi_state);
	CHECK_EQUAL(DEV_COMM_ERROR, pd.dev_comm_state);
	CHECK_EQUAL(PDEV_OP_NONE, pd.op.curr);
}

/* Verify that interrupted session setup can be aborted and stopped. */
TEST(pdev_comm_tests, aborted_session_setup_can_stop)
{
	pdev_comm_complete(&pd, DEV_ASSIGN_STATUS_SUCCESS, true);
	pdev_comm_begin_key(&pd);
	pdev_comm_complete(&pd, DEV_ASSIGN_STATUS_COMM_BLOCKED_APP_YIELD, false);
	pdev_comm_abort(&pd);
	CHECK_EQUAL(RMI_PDEV_STATE_ERROR, pd.rmi_state);
	CHECK_EQUAL(DEV_COMM_IDLE, pd.dev_comm_state);

	pdev_comm_begin(&pd, PDEV_OP_STOP);
	pdev_comm_complete(&pd, DEV_ASSIGN_STATUS_SUCCESS, true);
	CHECK_EQUAL(RMI_PDEV_STATE_STOPPED, pd.rmi_state);
	CHECK_EQUAL(DEV_COMM_IDLE, pd.dev_comm_state);
}

/* Verify that STOP does not publish STOPPED while the app is yielded. */
TEST(pdev_comm_tests, failed_stop_waits_for_yielded_app)
{
	pdev_comm_complete(&pd, DEV_ASSIGN_STATUS_SUCCESS, true);
	pdev_comm_begin(&pd, PDEV_OP_STOP);
	pdev_comm_complete(&pd, DEV_ASSIGN_STATUS_COMM_BLOCKED_APP_YIELD, false);
	pdev_comm_complete(&pd, DEV_ASSIGN_STATUS_ERROR, false);
	CHECK_EQUAL(RMI_PDEV_STATE_NEEDS_KEY, pd.rmi_state);
	CHECK_EQUAL(DEV_COMM_ACTIVE, pd.dev_comm_state);
	CHECK_EQUAL(PDEV_OP_STOP, pd.op.curr);

	pdev_comm_complete(&pd, DEV_ASSIGN_STATUS_ERROR, true);
	CHECK_EQUAL(RMI_PDEV_STATE_STOPPED, pd.rmi_state);
	CHECK_EQUAL(DEV_COMM_ERROR, pd.dev_comm_state);
	CHECK_EQUAL(PDEV_OP_NONE, pd.op.curr);
}

/* Verify that stream communication and stream completion remain distinct. */
TEST(pdev_comm_tests, stream_completion_remains_explicit)
{
	pdev_comm_complete(&pd, DEV_ASSIGN_STATUS_SUCCESS, true);
	pdev_comm_begin_key(&pd);
	pdev_comm_complete(&pd, DEV_ASSIGN_STATUS_SUCCESS, true);
	pdev_comm_begin(&pd, PDEV_OP_CONNECT);
	pdev_comm_complete(&pd, DEV_ASSIGN_STATUS_SUCCESS, true);
	CHECK_EQUAL(PDEV_OP_STREAM_COMPLETE, pd.op.curr);
	CHECK_EQUAL(DEV_COMM_IDLE, pd.dev_comm_state);

	pdev_comm_stream_complete(&pd);
	CHECK_EQUAL(PDEV_OP_NONE, pd.op.curr);
}

/* Verify beta-3 stream-error completion and abort behavior. */
TEST(pdev_comm_tests, stream_failure_remains_completable)
{
	pdev_comm_complete(&pd, DEV_ASSIGN_STATUS_SUCCESS, true);
	pdev_comm_begin_key(&pd);
	pdev_comm_complete(&pd, DEV_ASSIGN_STATUS_SUCCESS, true);
	pdev_comm_begin(&pd, PDEV_OP_DISCONNECT);
	pdev_comm_complete(&pd, DEV_ASSIGN_STATUS_ERROR, true);
	CHECK_EQUAL(RMI_PDEV_STATE_ERROR, pd.rmi_state);
	CHECK_EQUAL(DEV_COMM_IDLE, pd.dev_comm_state);
	CHECK_EQUAL(PDEV_OP_STREAM_COMPLETE, pd.op.curr);

	pdev_comm_stream_complete(&pd);
	CHECK_EQUAL(PDEV_OP_NONE, pd.op.curr);
}

/* Verify that the current-base stream-abort transition is preserved. */
TEST(pdev_comm_tests, stream_abort_remains_completable)
{
	pdev_comm_complete(&pd, DEV_ASSIGN_STATUS_SUCCESS, true);
	pdev_comm_begin_key(&pd);
	pdev_comm_complete(&pd, DEV_ASSIGN_STATUS_SUCCESS, true);
	pdev_comm_begin(&pd, PDEV_OP_DISCONNECT);
	pdev_comm_complete(&pd, DEV_ASSIGN_STATUS_COMM_BLOCKED_APP_YIELD, false);
	pdev_comm_abort(&pd);
	CHECK_EQUAL(RMI_PDEV_STATE_ERROR, pd.rmi_state);
	CHECK_EQUAL(DEV_COMM_IDLE, pd.dev_comm_state);
	CHECK_EQUAL(PDEV_OP_STREAM_COMPLETE, pd.op.curr);

	pdev_comm_stream_complete(&pd);
	CHECK_EQUAL(PDEV_OP_NONE, pd.op.curr);
}

/*
 * A pending operation on another VDEV, or on the PDEV, must not unwind the
 * DA app yielded for the first VDEV. The app is deliberately not initialized:
 * calling its abort path here would be invalid and fail the test.
 */
TEST(pdev_comm_tests, abort_non_owner_preserves_yielded_app)
{
	struct granule first_vdev = {};
	struct granule second_vdev = {};
	struct granule pdev_granule = {};

	pd.g_pdev = &pdev_granule;
	pd.da_app_yield_owner = &first_vdev;
	pd.da_app_data.exit_flag = APP_EXIT_SVC_YIELD_FLAG;

	CHECK_EQUAL(DEV_ASSIGN_STATUS_SUCCESS,
		    dev_abort_app_if_owner(&pd, &second_vdev));
	CHECK_EQUAL(DEV_ASSIGN_STATUS_SUCCESS,
		    dev_abort_app_if_owner(&pd, &pdev_granule));
	POINTERS_EQUAL(&first_vdev, pd.da_app_yield_owner);
	CHECK_EQUAL(APP_EXIT_SVC_YIELD_FLAG, pd.da_app_data.exit_flag);
}
