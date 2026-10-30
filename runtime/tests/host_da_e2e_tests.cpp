/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <CppUTest/TestHarness.h>

extern "C" {
#include <app.h>
#include <buffer.h>
#include <dev.h>
#include <granule.h>
#include <host_da.h>
#include <host_rmi_wrappers.h>
#include <host_utils.h>
#include <realm.h>
#include <rec.h>
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

struct vdev_operation_snapshot {
	unsigned long op;
	uint32_t comm_state;
};

/* Read the pending operation and communication state under the VDEV lock. */
static struct vdev_operation_snapshot vdev_operation_state(void *vdev_addr)
{
	struct granule *g_vdev = tr_addr_to_granule((uintptr_t)vdev_addr);
	struct vdev *vd;
	struct vdev_operation_snapshot snapshot;

	granule_lock(g_vdev, GRANULE_STATE_VDEV);
	vd = (struct vdev *)buffer_granule_map(g_vdev, SLOT_VDEV);
	CHECK_TRUE(vd != NULL);
	snapshot.op = vd->op;
	snapshot.comm_state = vd->comm_state;
	buffer_unmap(vd);
	granule_unlock(g_vdev);

	return snapshot;
}

/* Copy freshness from an existing VDEV under its granule lock. */
static struct vdev_freshness vdev_freshness(void *vdev_addr)
{
	struct granule *g_vdev = tr_addr_to_granule((uintptr_t)vdev_addr);
	struct vdev *vd;
	struct vdev_freshness freshness;

	granule_lock(g_vdev, GRANULE_STATE_VDEV);
	vd = (struct vdev *)buffer_granule_map(g_vdev, SLOT_VDEV);
	CHECK_TRUE(vd != NULL);
	freshness = vd->freshness;
	buffer_unmap(vd);
	granule_unlock(g_vdev);

	return freshness;
}

/* Read the Realm-wide lock counter from an existing RD under its lock. */
static uint64_t realm_vdev_lock_sequence(uintptr_t rd_addr)
{
	struct granule *g_rd = tr_addr_to_granule(rd_addr);
	struct rd *rd;
	uint64_t sequence;

	granule_lock(g_rd, GRANULE_STATE_RD);
	rd = (struct rd *)buffer_granule_map(g_rd, SLOT_RD);
	CHECK_TRUE(rd != NULL);
	sequence = rd->last_vdev_lock_seq;
	buffer_unmap(rd);
	granule_unlock(g_rd);

	return sequence;
}

/*
 * Save a completed VDEV operation's freshness and IPA range in an existing
 * REC under its lock, modeling a Realm's pending device mapping request.
 */
static void set_pending_vdev_mapping(uintptr_t rec_addr,
				     const struct vdev_freshness *freshness,
				     unsigned long ipa)
{
	struct granule *g_rec = tr_addr_to_granule(rec_addr);
	struct rec *rec;

	granule_lock(g_rec, GRANULE_STATE_REC);
	rec = (struct rec *)buffer_granule_map(g_rec, SLOT_REC);
	CHECK_TRUE(rec != NULL);
	rec->dev_mem.base = ipa;
	rec->dev_mem.addr = ipa;
	rec->dev_mem.top = ipa + GRANULE_SIZE;
	rec->vdev_id_1 = HOST_DA_VDEV_ID;
	rec->vdev_freshness_1 = *freshness;
	buffer_unmap(rec);
	granule_unlock(g_rec);
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
 * Verify the explicit INIT operation from VDEV_CREATE to VDEV_UNLOCKED.
 *
 * Setup: Create a DA-enabled Realm and PDEV, then create a VDEV without
 * driving its initial communication.
 * Action: Reject an unsolicited response, then communicate with status NONE.
 * Expected: CREATE leaves INIT pending in NEW; the rejected input preserves
 * that state; completion returns no device request and clears the operation.
 */
TEST(host_da_e2e_tests, vdev_init_operation)
{
	struct rmi_test_realm realm;
	struct host_realm host_realm = {};
	struct rmi_realm_params *params;
	struct smc_result result = {};
	struct host_pdev *pdev;
	struct host_vdev *vdev;
	struct rmi_dev_comm_data *comm;
	struct vdev_operation_snapshot snapshot;
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
	/* Leave CREATE at NEW/PENDING so INIT can be tested before completion. */
	vdev_id = host_vdev_create_pending(&host_realm, (unsigned long)pdev_id);
	CHECK_EQUAL(HOST_DA_VDEV_ID, vdev_id);
	pdev = host_pdev_current();
	vdev = host_vdev_current();
	endpoint = host_pdev_ptr(pdev, true);
	vdev_obj = host_vdev_ptr(vdev);
	comm = host_vdev_comm_data(vdev);

	CHECK_EQUAL(RMI_VDEV_STATE_NEW, vdev_state(vdev_obj));
	snapshot = vdev_operation_state(vdev_obj);
	CHECK_EQUAL(VDEV_OP_INIT, snapshot.op);
	CHECK_EQUAL(DEV_COMM_PENDING, snapshot.comm_state);

	/* No request has been sent yet, so a Host response must be rejected. */
	comm->enter.status = RMI_DEV_COMM_ENTER_STATUS_RESPONSE;
	comm->enter.resp_len = 1U;
	host_rmi_vdev_communicate(host_realm.rd, endpoint, vdev_obj, comm, &result);
	CHECK_EQUAL(RMI_ERROR_DEVICE, result.x[0]);
	CHECK_EQUAL(RMI_VDEV_STATE_NEW, vdev_state(vdev_obj));
	snapshot = vdev_operation_state(vdev_obj);
	CHECK_EQUAL(VDEV_OP_INIT, snapshot.op);
	CHECK_EQUAL(DEV_COMM_PENDING, snapshot.comm_state);

	/* INIT needs no device exchange; seed stale output to check it is cleared. */
	comm->enter.status = RMI_DEV_COMM_ENTER_STATUS_NONE;
	comm->enter.resp_len = 0U;
	comm->exit.flags = RMI_DEV_COMM_EXIT_FLAGS_REQ_SEND_BIT;
	comm->exit.req_len = 1UL;
	host_rmi_vdev_communicate(host_realm.rd, endpoint, vdev_obj, comm, &result);
	CHECK_EQUAL(RMI_SUCCESS, result.x[0]);
	UNSIGNED_LONGS_EQUAL(0UL, comm->exit.flags);
	UNSIGNED_LONGS_EQUAL(0UL, comm->exit.req_len);
	CHECK_EQUAL(RMI_VDEV_STATE_UNLOCKED, vdev_state(vdev_obj));
	snapshot = vdev_operation_state(vdev_obj);
	CHECK_EQUAL(VDEV_OP_NONE, snapshot.op);
	CHECK_EQUAL(DEV_COMM_IDLE, snapshot.comm_state);

	/* INIT is now IDLE/UNLOCKED and the VDEV can be destroyed directly. */
	CHECK_EQUAL(0, host_vdev_reclaim(&host_realm, vdev_id));
	/* Reclaim root port ID 0 and the endpoint after dropping VDEV references. */
	CHECK_EQUAL(0, host_pdev_reclaim(0));
	CHECK_EQUAL(0, host_pdev_reclaim(pdev_id));
	rmi_test_realm_destroy(&realm);
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

/*
 * VDEV_LOCK leaves an unlocked VDEV with pending communication. Destroying it
 * before the DA app runs must release the VDEV and its parent references.
 */
TEST(host_da_e2e_tests, vdev_destroy_pending_lock)
{
	struct rmi_test_realm realm;
	struct host_realm host_realm = {};
	struct rmi_realm_params *params;
	struct smc_result result = {};
	struct host_pdev *pdev;
	struct host_vdev *vdev;
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
	vdev_id = host_vdev_assign(&host_realm, (unsigned long)pdev_id);
	CHECK_TRUE(vdev_id >= 0);
	pdev = host_pdev_current();
	vdev = host_vdev_current();

	/* Queue LOCK without COMMUNICATE: the app has not acquired ownership yet. */
	host_rmi_vdev_lock(host_realm.rd, host_pdev_ptr(pdev, true),
			   host_vdev_ptr(vdev), &result);
	CHECK_EQUAL(RMI_SUCCESS, result.x[0]);
	CHECK_EQUAL(RMI_VDEV_STATE_UNLOCKED, vdev_state(host_vdev_ptr(vdev)));
	/* Still UNLOCKED, the VDEV can discard pending LOCK work during destroy. */
	CHECK_EQUAL(0, host_vdev_reclaim(&host_realm, vdev_id));
	/* Reclaim root port ID 0 and the endpoint after dropping VDEV references. */
	CHECK_EQUAL(0, host_pdev_reclaim(0));
	CHECK_EQUAL(0, host_pdev_reclaim(pdev_id));
	rmi_test_realm_destroy(&realm);
}

/*
 * GET_MEASUREMENTS admission depends on VDEV communication, independently of
 * PDEV communication, and must preserve pending and active LOCK operations.
 * DESTROY must preserve the yielded app's VDEV owner so ABORT can unwind it. This
 * isolated case ends after verifying that the app has exited and its
 * ownership has been released.
 */
TEST(host_da_e2e_tests, vdev_destroy_yielded_owner)
{
	const unsigned int pdev_comm_states[] = {
		DEV_COMM_PENDING, DEV_COMM_ACTIVE, DEV_COMM_ERROR
	};
	struct rmi_test_realm realm;
	struct host_realm host_realm = {};
	struct rmi_realm_params *params;
	struct rmi_vdev_measure_params *measure_params;
	struct rmi_dev_comm_data *comm;
	struct vdev_operation_snapshot snapshot;
	struct smc_result result = {};
	struct host_pdev *pdev;
	struct host_vdev *vdev;
	struct granule *g_pdev;
	struct granule *g_vdev;
	struct pdev *pd;
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
	vdev_id = host_vdev_assign(&host_realm, (unsigned long)pdev_id);
	CHECK_EQUAL(HOST_DA_VDEV_ID, vdev_id);
	pdev = host_pdev_current();
	vdev = host_vdev_current();
	endpoint = host_pdev_ptr(pdev, true);
	vdev_obj = host_vdev_ptr(vdev);
	g_pdev = tr_addr_to_granule((uintptr_t)endpoint);
	g_vdev = tr_addr_to_granule((uintptr_t)vdev_obj);
	comm = host_vdev_comm_data(vdev);
	/* Supply valid parameters so rejection tests busy communication alone. */
	measure_params = (struct rmi_vdev_measure_params *)allocate_granule(1U);
	(void)memset(measure_params, 0, sizeof(*measure_params));

	/*
	 * Model each non-idle PDEV communication state without starting PDEV app
	 * work. An idle VDEV must still accept measurements. Restore the fixture's
	 * PDEV state before driving the real measurement exchanges to completion.
	 */
	for (unsigned int i = 0U; i < ARRAY_SIZE(pdev_comm_states); i++) {
		granule_lock(g_pdev, GRANULE_STATE_PDEV);
		pd = (struct pdev *)buffer_granule_map(g_pdev, SLOT_PDEV);
		CHECK_EQUAL(DEV_COMM_IDLE, pd->dev_comm_state);
		pd->dev_comm_state = pdev_comm_states[i];
		buffer_unmap(pd);
		granule_unlock(g_pdev);

		smc_vdev_get_measurements(realm.rd, (uintptr_t)endpoint, (uintptr_t)vdev_obj,
					 (uintptr_t)measure_params, &result);
		CHECK_EQUAL(RMI_SUCCESS, result.x[0]);
		snapshot = vdev_operation_state(vdev_obj);
		CHECK_EQUAL(VDEV_OP_GET_MEAS, snapshot.op);
		CHECK_EQUAL(DEV_COMM_PENDING, snapshot.comm_state);

		granule_lock(g_pdev, GRANULE_STATE_PDEV);
		pd = (struct pdev *)buffer_granule_map(g_pdev, SLOT_PDEV);
		CHECK_EQUAL(pdev_comm_states[i], pd->dev_comm_state);
		pd->dev_comm_state = DEV_COMM_IDLE;
		buffer_unmap(pd);
		granule_unlock(g_pdev);
		CHECK_EQUAL(0, host_dev_communicate(&host_realm, pdev, true, vdev,
						RMI_VDEV_STATE_UNLOCKED, false));
		snapshot = vdev_operation_state(vdev_obj);
		CHECK_EQUAL(DEV_COMM_IDLE, snapshot.comm_state);
	}

	/* Pending LOCK must not be replaced before its first COMMUNICATE call. */
	host_rmi_vdev_lock(host_realm.rd, endpoint, vdev_obj, &result);
	CHECK_EQUAL(RMI_SUCCESS, result.x[0]);
	smc_vdev_get_measurements(realm.rd, (uintptr_t)endpoint, (uintptr_t)vdev_obj,
				 (uintptr_t)measure_params, &result);
	CHECK_EQUAL(RMI_ERROR_DEVICE, result.x[0]);
	snapshot = vdev_operation_state(vdev_obj);
	CHECK_EQUAL(VDEV_OP_LOCK, snapshot.op);
	CHECK_EQUAL(DEV_COMM_PENDING, snapshot.comm_state);

	/* Start LOCK and leave its app yielded awaiting Host transport. */
	comm->enter.status = RMI_DEV_COMM_ENTER_STATUS_NONE;
	comm->enter.resp_len = 0U;
	host_rmi_vdev_communicate(host_realm.rd, endpoint, vdev_obj, comm, &result);
	CHECK_EQUAL(RMI_SUCCESS, result.x[0]);
	CHECK_EQUAL(RMI_VDEV_STATE_UNLOCKED, vdev_state(vdev_obj));
	snapshot = vdev_operation_state(vdev_obj);
	CHECK_EQUAL(VDEV_OP_LOCK, snapshot.op);
	CHECK_EQUAL(DEV_COMM_ACTIVE, snapshot.comm_state);

	/* Active LOCK must also retain its operation and resume state on rejection. */
	smc_vdev_get_measurements(realm.rd, (uintptr_t)endpoint, (uintptr_t)vdev_obj,
				 (uintptr_t)measure_params, &result);
	CHECK_EQUAL(RMI_ERROR_DEVICE, result.x[0]);
	snapshot = vdev_operation_state(vdev_obj);
	CHECK_EQUAL(VDEV_OP_LOCK, snapshot.op);
	CHECK_EQUAL(DEV_COMM_ACTIVE, snapshot.comm_state);

	/* A yielded LOCK still owns the VDEV even though its RMI state is UNLOCKED. */
	host_rmi_vdev_destroy(host_realm.rd, endpoint, vdev_obj, &result);
	CHECK_EQUAL(RMI_ERROR_DEVICE, result.x[0]);
	CHECK_EQUAL(RMI_VDEV_STATE_UNLOCKED, vdev_state(vdev_obj));
	snapshot = vdev_operation_state(vdev_obj);
	CHECK_EQUAL(VDEV_OP_LOCK, snapshot.op);
	CHECK_EQUAL(DEV_COMM_ACTIVE, snapshot.comm_state);
	granule_lock(g_pdev, GRANULE_STATE_PDEV);
	pd = (struct pdev *)buffer_granule_map(g_pdev, SLOT_PDEV);
	CHECK_EQUAL(APP_EXIT_SVC_YIELD_FLAG, pd->da_app_data.exit_flag);
	POINTERS_EQUAL(g_vdev, pd->da_app_yield_owner);
	CHECK_EQUAL(1U, pd->num_vdevs);
	buffer_unmap(pd);
	granule_unlock(g_pdev);

	/* ABORT must find that same owner, unwind LOCK, and restore comms to IDLE. */
	host_rmi_vdev_abort(host_realm.rd, endpoint, vdev_obj, &result);
	CHECK_EQUAL(RMI_SUCCESS, result.x[0]);
	CHECK_EQUAL(RMI_VDEV_STATE_ERROR, vdev_state(vdev_obj));
	snapshot = vdev_operation_state(vdev_obj);
	CHECK_EQUAL(DEV_COMM_IDLE, snapshot.comm_state);
	granule_lock(g_pdev, GRANULE_STATE_PDEV);
	pd = (struct pdev *)buffer_granule_map(g_pdev, SLOT_PDEV);
	CHECK_EQUAL(APP_EXIT_SVC_EXIT_FLAG, pd->da_app_data.exit_flag);
	POINTERS_EQUAL(NULL, pd->da_app_yield_owner);
	CHECK_EQUAL(1U, pd->num_vdevs);
	buffer_unmap(pd);
	granule_unlock(g_pdev);
}

/*
 * Verify freshness across completed device requests, relock and replacement.
 * RMI_RTT_DEV_VALIDATE must reject a pending request after each freshness
 * change, including recreation of the same VDEV ID.
 */
TEST(host_da_e2e_tests, vdev_freshness_lifecycle)
{
	struct rmi_test_realm realm;
	struct rmi_test_rec rec;
	struct host_realm host_realm = {};
	struct rmi_realm_params *params;
	struct rmi_vdev_measure_params *measure_params;
	struct vdev_freshness freshness;
	struct smc_result result = {};
	struct host_pdev *pdev;
	struct host_vdev *vdev;
	void *endpoint;
	void *vdev_obj;
	const unsigned long ipa = 0x400000UL;
	int pdev_id;
	int vdev_id;
	int rc;

	/* Enable DA and reserve one VDEV slot before creating the Realm. */
	rmi_test_realm_prepare(&realm);
	params = (struct rmi_realm_params *)realm.params;
	params->flags0 = INPLACE(RMI_REALM_FLAGS0_DA, RMI_FEATURE_TRUE);
	params->max_num_vdevs = 1UL;
	rmi_test_realm_create(&realm);
	rmi_test_rec_create(&realm, &rec);
	smc_realm_activate(realm.rd, &result);
	CHECK_EQUAL(RMI_SUCCESS, result.x[0]);
	host_realm.rd = (void *)realm.rd;

	/* Establish SPDM/IDE and a PSMMU stream table for the Realm device. */
	pdev_id = host_pdev_probe_and_setup();
	CHECK_TRUE(pdev_id > 0);
	CHECK_EQUAL(0, host_psmmu_setup(0U, (unsigned long)pdev_id));
	vdev_id = host_vdev_assign(&host_realm, (unsigned long)pdev_id);
	CHECK_EQUAL(HOST_DA_VDEV_ID, vdev_id);
	pdev = host_pdev_current();
	vdev = host_vdev_current();
	endpoint = host_pdev_ptr(pdev, true);
	vdev_obj = host_vdev_ptr(vdev);

	/* INIT leaves all freshness counters at zero; no lock epoch exists yet. */
	freshness = vdev_freshness(vdev_obj);
	UNSIGNED_LONGS_EQUAL(0UL, freshness.lock_seq);
	UNSIGNED_LONGS_EQUAL(0UL, freshness.meas_seq);
	UNSIGNED_LONGS_EQUAL(0UL, freshness.report_seq);
	UNSIGNED_LONGS_EQUAL(0UL, realm_vdev_lock_sequence(realm.rd));

	/* Complete the first LOCK and snapshot epoch 1 in a pending REC mapping. */
	host_rmi_vdev_lock(host_realm.rd, endpoint, vdev_obj, &result);
	CHECK_EQUAL(RMI_SUCCESS, result.x[0]);
	rc = host_dev_communicate(&host_realm, pdev, true, vdev,
				  RMI_VDEV_STATE_LOCKED, false);
	CHECK_EQUAL(0, rc);
	freshness = vdev_freshness(vdev_obj);
	UNSIGNED_LONGS_EQUAL(1UL, freshness.lock_seq);
	UNSIGNED_LONGS_EQUAL(0UL, freshness.meas_seq);
	UNSIGNED_LONGS_EQUAL(0UL, freshness.report_seq);
	UNSIGNED_LONGS_EQUAL(1UL, realm_vdev_lock_sequence(realm.rd));
	set_pending_vdev_mapping(rec.rec, &freshness, ipa);

	/* Measurements advance meas_seq and invalidate the REC's earlier snapshot. */
	measure_params = (struct rmi_vdev_measure_params *)allocate_granule(1U);
	(void)memset(measure_params, 0, sizeof(*measure_params));
	smc_vdev_get_measurements(realm.rd, (uintptr_t)endpoint,
				  (uintptr_t)vdev_obj, (uintptr_t)measure_params, &result);
	CHECK_EQUAL(RMI_SUCCESS, result.x[0]);
	rc = host_dev_communicate(&host_realm, pdev, true, vdev,
				  RMI_VDEV_STATE_LOCKED, false);
	CHECK_EQUAL(0, rc);
	freshness = vdev_freshness(vdev_obj);
	UNSIGNED_LONGS_EQUAL(1UL, freshness.lock_seq);
	UNSIGNED_LONGS_EQUAL(1UL, freshness.meas_seq);
	UNSIGNED_LONGS_EQUAL(0UL, freshness.report_seq);
	smc_rtt_dev_validate(realm.rd, rec.rec, ipa, ipa + GRANULE_SIZE, &result);
	CHECK_EQUAL(RMI_ERROR_DEVICE, result.x[0]);
	set_pending_vdev_mapping(rec.rec, &freshness, ipa);

	/* Advance report_seq against the REC snapshot saved after measurements. */
	smc_vdev_get_interface_report(realm.rd, (uintptr_t)endpoint,
				      (uintptr_t)vdev_obj, &result);
	CHECK_EQUAL(RMI_SUCCESS, result.x[0]);
	rc = host_dev_communicate(&host_realm, pdev, true, vdev,
				  RMI_VDEV_STATE_LOCKED, false);
	CHECK_EQUAL(0, rc);
	freshness = vdev_freshness(vdev_obj);
	UNSIGNED_LONGS_EQUAL(1UL, freshness.lock_seq);
	UNSIGNED_LONGS_EQUAL(1UL, freshness.meas_seq);
	UNSIGNED_LONGS_EQUAL(1UL, freshness.report_seq);
	smc_rtt_dev_validate(realm.rd, rec.rec, ipa, ipa + GRANULE_SIZE, &result);
	CHECK_EQUAL(RMI_ERROR_DEVICE, result.x[0]);
	set_pending_vdev_mapping(rec.rec, &freshness, ipa);

	/* Relock advances lock_seq and resets measurement/report freshness to zero. */
	host_rmi_vdev_unlock(host_realm.rd, endpoint, vdev_obj, &result);
	CHECK_EQUAL(RMI_SUCCESS, result.x[0]);
	rc = host_dev_communicate(&host_realm, pdev, true, vdev,
				  RMI_VDEV_STATE_UNLOCKED, false);
	CHECK_EQUAL(0, rc);
	host_rmi_vdev_lock(host_realm.rd, endpoint, vdev_obj, &result);
	CHECK_EQUAL(RMI_SUCCESS, result.x[0]);
	rc = host_dev_communicate(&host_realm, pdev, true, vdev,
				  RMI_VDEV_STATE_LOCKED, false);
	CHECK_EQUAL(0, rc);
	freshness = vdev_freshness(vdev_obj);
	UNSIGNED_LONGS_EQUAL(2UL, freshness.lock_seq);
	UNSIGNED_LONGS_EQUAL(0UL, freshness.meas_seq);
	UNSIGNED_LONGS_EQUAL(0UL, freshness.report_seq);
	UNSIGNED_LONGS_EQUAL(2UL, realm_vdev_lock_sequence(realm.rd));
	smc_rtt_dev_validate(realm.rd, rec.rec, ipa, ipa + GRANULE_SIZE, &result);
	CHECK_EQUAL(RMI_ERROR_DEVICE, result.x[0]);

	/* Reuse the VDEV ID: its next lock must get a new Realm-wide epoch. */
	CHECK_EQUAL(0, host_vdev_reclaim(&host_realm, vdev_id));
	vdev_id = host_vdev_assign(&host_realm, (unsigned long)pdev_id);
	CHECK_EQUAL(HOST_DA_VDEV_ID, vdev_id);
	vdev_obj = host_vdev_ptr(host_vdev_current());
	freshness = vdev_freshness(vdev_obj);
	UNSIGNED_LONGS_EQUAL(0UL, freshness.lock_seq);
	UNSIGNED_LONGS_EQUAL(2UL, realm_vdev_lock_sequence(realm.rd));
	host_rmi_vdev_lock(host_realm.rd, endpoint, vdev_obj, &result);
	CHECK_EQUAL(RMI_SUCCESS, result.x[0]);
	rc = host_dev_communicate(&host_realm, pdev, true,
				  host_vdev_current(), RMI_VDEV_STATE_LOCKED, false);
	CHECK_EQUAL(0, rc);
	freshness = vdev_freshness(vdev_obj);
	UNSIGNED_LONGS_EQUAL(3UL, freshness.lock_seq);
	UNSIGNED_LONGS_EQUAL(0UL, freshness.meas_seq);
	UNSIGNED_LONGS_EQUAL(0UL, freshness.report_seq);
	UNSIGNED_LONGS_EQUAL(3UL, realm_vdev_lock_sequence(realm.rd));
	smc_rtt_dev_validate(realm.rd, rec.rec, ipa, ipa + GRANULE_SIZE, &result);
	CHECK_EQUAL(RMI_ERROR_DEVICE, result.x[0]);

	CHECK_EQUAL(0, host_vdev_reclaim(&host_realm, vdev_id));
	/* Reclaim root port ID 0 and the endpoint after dropping VDEV references. */
	CHECK_EQUAL(0, host_pdev_reclaim(0));
	CHECK_EQUAL(0, host_pdev_reclaim(pdev_id));
	/* REC destruction returns its auxiliary granules for reclamation. */
	result = {};
	smc_rec_destroy(rec.rec, &result);
	CHECK_EQUAL(RMI_INCOMPLETE, unpack_return_code(result.x[0]).status);
	rmi_test_reclaim(result.x[1], realm.addr_list, rec.num_aux);
	rmi_test_realm_destroy(&realm);
}
