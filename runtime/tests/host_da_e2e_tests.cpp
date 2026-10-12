/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <CppUTest/TestHarness.h>

extern "C" {
#include <glob_data.h>
#include <host_da.h>
#include <host_rmi_wrappers.h>
#include <host_utils.h>
}

#include <rmi_test_helpers.h>

/*
 * Run each DA case in its own process because the emulator has a fixed port
 * and the RMM test model retains some device and app state across resets.
 * The responder and DA app are real host child processes in these tests.
 *
 * An operation call queues work as PENDING. COMMUNICATE drives that work;
 * operations needing device exchanges start the DA app through this call.
 * A yield awaiting Host transport makes communication ACTIVE, and completion
 * makes it IDLE. The RMI device state changes only when the operation reaches
 * its state transition, so a pending or active LOCK can still be UNLOCKED.
 * Raw RMI wrappers let tests stop at these boundaries. host_dev_communicate()
 * handles the request/response transport until the requested stopping point.
 */
TEST_GROUP(host_da_e2e_tests) {
	TEST_SETUP()
	{
		test_helpers_init();
		host_util_pas_enable(true);
		test_helpers_allocate_reset();
		test_helpers_rmm_start(false);
		host_util_set_cpuid(0U);
		test_helpers_expect_assert_fail(false);
		/* The unit-test boot populates tracking but leaves the RMI gate in INIT. */
		CHECK_TRUE(glob_data_transition_rmm_state(RMM_STATE_INIT,
							RMM_STATE_ACTIVE));
		test_helpers_spdm_responder_start();
	}

	TEST_TEARDOWN()
	{
		host_util_stop_spdm_responder();
		host_util_pas_enable(false);
	}
};

/* Query the state of an existing PDEV through the Host RMI dispatcher. */
static unsigned long pdev_state(void *pdev)
{
	struct smc_result result = {};

	host_rmi_pdev_get_state(pdev, &result);
	CHECK_EQUAL(RMI_SUCCESS, result.x[0]);
	return result.x[1];
}

/* Query the state of an existing VDEV through the Host RMI dispatcher. */
static unsigned long vdev_state(void *vdev)
{
	struct smc_result result = {};

	host_rmi_vdev_get_state(vdev, &result);
	CHECK_EQUAL(RMI_SUCCESS, result.x[0]);
	return result.x[1];
}

/*
 * Fail yielded STOP exchanges until the endpoint is STOPPED. The first
 * exchange must send a fresh request after the earlier abort or failure.
 */
static void complete_failed_stop(void *pdev, struct rmi_dev_comm_data *comm)
{
	struct smc_result result = {};

	comm->enter.status = RMI_DEV_COMM_ENTER_STATUS_NONE;
	comm->enter.resp_len = 0U;
	for (unsigned int attempt = 0U; attempt < 16U; attempt++) {
		host_rmi_pdev_communicate(pdev, comm, &result);
		CHECK_EQUAL(RMI_SUCCESS, result.x[0]);
		if (attempt == 0U) {
			CHECK_TRUE((comm->exit.flags &
				RMI_DEV_COMM_EXIT_FLAGS_REQ_SEND_BIT) != 0U);
		}
		if (pdev_state(pdev) == RMI_PDEV_STATE_STOPPED) {
			return;
		}
		/* Feed a transport failure back into the app's next resume. */
		comm->enter.status = RMI_DEV_COMM_ENTER_STATUS_ERROR;
		comm->enter.resp_len = 0U;
	}

	FAIL_TEST("PDEV STOP did not complete after 16 exchanges");
}

/*
 * Drive endpoint initialization recovery, STOP and destroy through the RMI ABI.
 * Abort while the app is yielded if abort_while_yielded is true. Otherwise,
 * complete initialization with a device error and verify that ABORT rejects
 * the resulting idle communication channel without preventing STOP.
 */
static void initial_abort_stop(bool abort_while_yielded)
{
	struct host_pdev *pdev = host_pdev_current();
	struct rmi_dev_comm_data *comm;
	struct smc_result result = {};
	void *endpoint;

	/* Create queues initialization; do not complete the SPDM session yet. */
	CHECK_EQUAL(0, host_pdev_setup(pdev));
	CHECK_EQUAL(0, host_pdev_create(pdev, true));
	endpoint = host_pdev_ptr(pdev, true);
	comm = host_pdev_comm_data(pdev);

	/* Start GET_VERSION and stop when the app asks the Host to send it. */
	comm->enter.status = RMI_DEV_COMM_ENTER_STATUS_NONE;
	comm->enter.resp_len = 0U;
	host_rmi_pdev_communicate(endpoint, comm, &result);
	CHECK_EQUAL(RMI_SUCCESS, result.x[0]);
	CHECK_TRUE((comm->exit.flags &
		RMI_DEV_COMM_EXIT_FLAGS_REQ_SEND_BIT) != 0U);

	if (!abort_while_yielded) {
		/* Unwind initialization through its error path before attempting ABORT. */
		comm->enter.status = RMI_DEV_COMM_ENTER_STATUS_ERROR;
		comm->enter.resp_len = 0U;
		host_rmi_pdev_communicate(endpoint, comm, &result);
		CHECK_EQUAL(RMI_SUCCESS, result.x[0]);
		CHECK_EQUAL(RMI_PDEV_STATE_ERROR, pdev_state(endpoint));
	}

	/* ABORT can unwind yielded work, but rejects an already idle channel. */
	host_rmi_pdev_abort(endpoint, &result);
	CHECK_EQUAL(abort_while_yielded ? RMI_SUCCESS : RMI_ERROR_DEVICE,
		    result.x[0]);
	CHECK_EQUAL(RMI_PDEV_STATE_ERROR, pdev_state(endpoint));
	/* Recovery must start fresh STOP work after either initialization failure. */
	host_rmi_pdev_stop(endpoint, &result);
	CHECK_EQUAL(RMI_SUCCESS, result.x[0]);
	complete_failed_stop(endpoint, comm);
	/* STOPPED releases the endpoint for destruction and Host buffer cleanup. */
	CHECK_EQUAL(0, host_pdev_destroy(pdev, true));
	host_pdev_cleanup(pdev, true);
	host_pdev_cleanup(pdev, false);
}

/*
 * Verify that aborting the first yielded SPDM exchange allows STOP to finish.
 *
 * Setup: Boot the host RMM, start the responder, and create an endpoint PDEV
 * through the RMI/DA app path. Leave GET_VERSION yielded before any response.
 * Action: Abort the yielded communication, start STOP, return device errors
 * to its reset exchange, then destroy the PDEV.
 * Expected: Abort enters ERROR; STOP reaches STOPPED; destroy releases the
 * PDEV without a stale SPDM request assertion or a stranded app instance.
 */
TEST(host_da_e2e_tests, pdev_yielded_abort_stop)
{
	initial_abort_stop(true);
}

/*
 * Verify recovery after the first SPDM request fails and app work unwinds.
 *
 * Setup: Create an endpoint PDEV and yield its initial GET_VERSION exchange.
 * Action: Return a device error to initialization, attempt ABORT on its idle
 * channel, start STOP, fail the reset exchange, then destroy the PDEV.
 * Expected: Initialization enters ERROR; ABORT returns RMI_ERROR_DEVICE;
 * STOP reaches STOPPED and destroy completes without an active DA app or
 * stale request.
 */
TEST(host_da_e2e_tests, pdev_failed_abort_stop)
{
	initial_abort_stop(false);
}

/*
 * Verify that failed DevCommExit copyout still releases a stopped PDEV.
 *
 * Setup: Establish a real SPDM session and IDE stream for the endpoint and
 * root port, then disconnect the stream before STOP.
 * Action: Fail the second NS map of the communication page, after the DA app
 * has run but before DevCommExit can be copied to the Host.
 * Expected: PDEV_COMMUNICATE reports RMI_ERROR_INPUT; the endpoint is STOPPED;
 * the injected fault was consumed; both PDEV objects can be destroyed.
 */
TEST(host_da_e2e_tests, pdev_stop_copyout)
{
	struct host_pdev *pdev;
	struct rmi_dev_comm_data *comm;
	struct smc_result result = {};
	void *endpoint;
	bool map_failed;
	int pdev_id;

	pdev_id = host_pdev_probe_and_setup();
	CHECK_TRUE(pdev_id > 0);
	pdev = host_pdev_current();
	endpoint = host_pdev_ptr(pdev, true);
	comm = host_pdev_comm_data(pdev);
	/* Disconnect IDE before asking STOP to tear down the established session. */
	CHECK_EQUAL(0, host_pdev_stream_disconnect(pdev));
	/* Queue STOP; its app work runs only in the following COMMUNICATE call. */
	host_rmi_pdev_stop(endpoint, &result);
	CHECK_EQUAL(RMI_SUCCESS, result.x[0]);

	comm->enter.status = RMI_DEV_COMM_ENTER_STATUS_NONE;
	comm->enter.resp_len = 0U;
	/* Allow input copyin, then fault output copyout after STOP has completed. */
	host_da_test_fail_ns_map((unsigned long)comm, 2U);
	host_rmi_pdev_communicate(endpoint, comm, &result);
	map_failed = host_da_test_ns_map_faulted();
	/* Disarm the injection before querying state or reclaiming either PDEV. */
	host_da_test_fail_ns_map(0UL, 0U);
	CHECK_TRUE(map_failed);
	CHECK_EQUAL(RMI_ERROR_INPUT, result.x[0]);
	/* The copyout error must not roll back STOP or retain the app instance. */
	CHECK_EQUAL(RMI_PDEV_STATE_STOPPED, pdev_state(endpoint));
	CHECK_EQUAL(0, host_pdev_destroy(pdev, true));
	CHECK_EQUAL(0, host_pdev_reclaim(0));
	host_pdev_cleanup(pdev, true);
}

/*
 * Verify VDEV validation while LOCK has a pending communication request.
 *
 * Setup: Create a DA-enabled Realm, establish the endpoint SPDM session and
 * IDE stream, activate its PSMMU table, and bind a VDEV to the Realm.
 * Action: Reject ABORT on the idle VDEV, start LOCK, reject an unsolicited
 * RESPONSE, then complete the real TDISP/SPDM exchanges with the responder.
 * Expected: Invalid calls leave the VDEV usable; LOCK reaches LOCKED; unlock,
 * destroy, PDEV cleanup, and Realm destruction all succeed.
 */
TEST(host_da_e2e_tests, vdev_pending_input)
{
	struct rmi_test_realm realm;
	struct host_realm host_realm = {};
	struct rmi_realm_params *params;
	struct smc_result result = {};
	struct host_pdev *pdev;
	struct host_vdev *vdev;
	struct rmi_dev_comm_data *comm;
	void *endpoint;
	void *vdev_obj;
	int pdev_id;
	int vdev_id;

	/* Enable DA and reserve one VDEV slot before creating the Realm. */
	rmi_test_realm_prepare(&realm);
	params = (struct rmi_realm_params *)realm.params;
	params->flags0 = INPLACE(RMI_REALM_FLAGS0_DA, RMI_FEATURE_TRUE);
	params->max_num_vdevs = 1UL;
	rmi_test_realm_create(&realm);
	smc_realm_activate(realm.rd, &result);
	CHECK_EQUAL(RMI_SUCCESS, result.x[0]);
	host_realm.rd = (void *)realm.rd;

	/* Establish SPDM/IDE and a PSMMU stream table for the Realm device. */
	pdev_id = host_pdev_probe_and_setup();
	CHECK_TRUE(pdev_id > 0);
	CHECK_EQUAL(0, host_psmmu_setup(0U, (unsigned long)pdev_id));
	/* Unlike create_pending(), assign also completes INIT to IDLE/UNLOCKED. */
	vdev_id = host_vdev_assign(&host_realm, (unsigned long)pdev_id);
	CHECK_TRUE(vdev_id >= 0);
	pdev = host_pdev_current();
	vdev = host_vdev_current();
	endpoint = host_pdev_ptr(pdev, true);
	vdev_obj = host_vdev_ptr(vdev);
	comm = host_vdev_comm_data(vdev);

	/* With no operation in progress, ABORT must leave the VDEV usable. */
	host_rmi_vdev_abort(host_realm.rd, endpoint, vdev_obj, &result);
	CHECK_EQUAL(RMI_ERROR_DEVICE, result.x[0]);
	CHECK_EQUAL(RMI_VDEV_STATE_UNLOCKED, vdev_state(vdev_obj));
	/* LOCK only queues work; a RESPONSE before its first request is invalid. */
	host_rmi_vdev_lock(host_realm.rd, endpoint, vdev_obj, &result);
	CHECK_EQUAL(RMI_SUCCESS, result.x[0]);
	comm->enter.status = RMI_DEV_COMM_ENTER_STATUS_RESPONSE;
	comm->enter.resp_len = 1U;
	host_rmi_vdev_communicate(host_realm.rd, endpoint, vdev_obj, comm, &result);
	CHECK_EQUAL(RMI_ERROR_DEVICE, result.x[0]);
	CHECK_EQUAL(RMI_VDEV_STATE_UNLOCKED, vdev_state(vdev_obj));
	/* Retry from status NONE and transport real responses until LOCK completes. */
	CHECK_EQUAL(0, host_dev_communicate(&host_realm, pdev, true, vdev,
					RMI_VDEV_STATE_LOCKED, false));
	/* Reclaim unlocks the LOCKED VDEV before destroying it. */
	CHECK_EQUAL(0, host_vdev_reclaim(&host_realm, vdev_id));
	/* Reclaim root port ID 0 and the endpoint after dropping VDEV references. */
	CHECK_EQUAL(0, host_pdev_reclaim(0));
	CHECK_EQUAL(0, host_pdev_reclaim(pdev_id));
	rmi_test_realm_destroy(&realm);
}
