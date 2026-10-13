/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <assert.h>
#include <dev.h>
#include <pdev_comm.h>

/* Return whether an in-progress PDEV operation acts on a stream. */
static bool pdev_comm_operation_is_stream(unsigned long op)
{
	return (op == PDEV_OP_CONNECT) ||
	       (op == PDEV_OP_DISCONNECT) ||
	       (op == PDEV_OP_KEY_REFRESH) ||
	       (op == PDEV_OP_KEY_PURGE);
}

/* Initialize the states for the first PDEV_COMMUNICATE after creation. */
void pdev_comm_init(struct pdev *pd)
{
	assert(pd != NULL);

	pd->rmi_state = RMI_PDEV_STATE_NEW;
	pd->dev_comm_state = DEV_COMM_PENDING;
	pd->op.curr = PDEV_OP_NONE;
	pd->op.stream_op_state = STREAM_OP_STATE_NONE;
}

/* Begin an operation after its command-specific checks have passed. */
void pdev_comm_begin(struct pdev *pd, unsigned long op)
{
	assert(pd != NULL);
	assert(pd->dev_comm_state == DEV_COMM_IDLE);
	assert(op != PDEV_OP_NONE);

	pd->op.curr = op;
	pd->dev_comm_state = DEV_COMM_PENDING;
}

/* Begin the communication which establishes the secure session. */
void pdev_comm_begin_key(struct pdev *pd)
{
	assert(pd != NULL);
	assert(pd->rmi_state == RMI_PDEV_STATE_NEEDS_KEY);

	pd->rmi_state = RMI_PDEV_STATE_HAS_KEY;
	pd->dev_comm_state = DEV_COMM_PENDING;
}

/* Finish STOP only after the app has exited, including on app failure. */
static void pdev_comm_complete_stop(struct pdev *pd)
{
	pd->rmi_state = RMI_PDEV_STATE_STOPPED;
	pd->op.curr = PDEV_OP_NONE;
	pd->op.stream_op_state = STREAM_OP_STATE_NONE;
}

/* Complete a successful or failed non-STOP PDEV transaction. */
static void pdev_comm_complete_operation(struct pdev *pd, bool success)
{
	pd->dev_comm_state = DEV_COMM_IDLE;

	if (!success) {
		pd->rmi_state = RMI_PDEV_STATE_ERROR;
	} else if (pd->rmi_state == RMI_PDEV_STATE_NEW) {
		pd->rmi_state = (PDEV_CATEGORY(pd) == RMI_PDEV_ROOTPORT) ?
			RMI_PDEV_STATE_READY : RMI_PDEV_STATE_NEEDS_KEY;
	} else if (pd->rmi_state == RMI_PDEV_STATE_HAS_KEY) {
		pd->rmi_state = RMI_PDEV_STATE_READY;
	}

	if (pdev_comm_operation_is_stream(pd->op.curr)) {
		pd->op.curr = PDEV_OP_STREAM_COMPLETE;
	} else {
		pd->op.curr = PDEV_OP_NONE;
	}
}

/* Apply a dispatched command's result to the PDEV state machine. */
void pdev_comm_complete(struct pdev *pd, int app_rc, bool app_unwound)
{
	assert(pd != NULL);
	assert((pd->dev_comm_state == DEV_COMM_PENDING) ||
	       (pd->dev_comm_state == DEV_COMM_ACTIVE));

	if (IS_DEV_ASSIGN_STATUS_COMM_BLOCKED(app_rc)) {
		pd->dev_comm_state = DEV_COMM_ACTIVE;
		return;
	}

	if (pd->op.curr == PDEV_OP_STOP) {
		if ((app_rc == DEV_ASSIGN_STATUS_ERROR) && !app_unwound) {
			/* Keep STOP resumable until the app exit is confirmed. */
			pd->dev_comm_state = DEV_COMM_ACTIVE;
			return;
		}

		assert(app_unwound);
		assert((app_rc == DEV_ASSIGN_STATUS_SUCCESS) ||
		       (app_rc == DEV_ASSIGN_STATUS_ERROR));
		pd->dev_comm_state = (app_rc == DEV_ASSIGN_STATUS_SUCCESS) ?
			DEV_COMM_IDLE : DEV_COMM_ERROR;
		pdev_comm_complete_stop(pd);
		return;
	}

	assert((app_rc == DEV_ASSIGN_STATUS_SUCCESS) ||
	       (app_rc == DEV_ASSIGN_STATUS_ERROR));
	pdev_comm_complete_operation(pd, app_rc == DEV_ASSIGN_STATUS_SUCCESS);
}

/* Apply the current implementation's PDEV_ABORT state transition. */
void pdev_comm_abort(struct pdev *pd)
{
	assert(pd != NULL);
	assert(pd->dev_comm_state != DEV_COMM_IDLE);

	pd->rmi_state = RMI_PDEV_STATE_ERROR;
	if (pdev_comm_operation_is_stream(pd->op.curr)) {
		pd->op.curr = PDEV_OP_STREAM_COMPLETE;
	}
	pd->dev_comm_state = DEV_COMM_IDLE;
}

/* Clear the operation after the stream state is committed. */
void pdev_comm_stream_complete(struct pdev *pd)
{
	assert(pd != NULL);
	assert((pd->op.curr == PDEV_OP_STREAM_COMPLETE) ||
	       (pd->op.curr == PDEV_OP_STREAM_ABORTED));

	pd->op.curr = PDEV_OP_NONE;
}
