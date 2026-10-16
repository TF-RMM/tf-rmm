/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef PDEV_COMM_H
#define PDEV_COMM_H

#include <stdbool.h>

struct pdev;

/*
 * PDEV lifecycle, communication and operation transitions are owned here.
 * RMI handlers validate command-specific preconditions before calling these
 * functions while holding the PDEV granule lock.
 */

/* Initialize a newly created PDEV for its first communication request. */
void pdev_comm_init(struct pdev *pd);

/* Begin a PDEV_OP_* operation on an idle PDEV. */
void pdev_comm_begin(struct pdev *pd, unsigned long op);

/* Begin secure-session setup after installing a key. */
void pdev_comm_begin_key(struct pdev *pd);

/*
 * Apply the result of a dispatched PDEV command. A STOP remains active when
 * app_unwound is false so the live app cannot be deinitialized by DESTROY.
 */
void pdev_comm_complete(struct pdev *pd, int app_rc, bool app_unwound);

/* Apply the PDEV_ABORT transition after the DA app exits. */
void pdev_comm_abort(struct pdev *pd);

/* Clear the operation after PDEV_STREAM_COMPLETE commits the stream state. */
void pdev_comm_stream_complete(struct pdev *pd);

#endif /* PDEV_COMM_H */
