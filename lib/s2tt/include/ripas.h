/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef RIPAS_H
#define RIPAS_H

#include <smc-rmi.h>
#include <smc-rsi.h>

/*
 * The RmmRipas enumeration represents realm IPA state.
 *
 * Map RmmRipas to RmiRipas to simplify code/decode operations.
 */
enum ripas {
	RIPAS_EMPTY = RMI_EMPTY,	/* Unused IPA for Realm */
	RIPAS_RAM = RMI_RAM,		/* IPA used for Code/Data by Realm */
	RIPAS_DESTROYED = RMI_DESTROYED,/* IPA is inaccessible to the Realm */
	RIPAS_DEV			/* Address where memory of an assigned
					   Realm device is mapped */
};

/*
 * The RmmRipasChangeDestroyed enumeration represents whether a RIPAS change
 * from DESTROYED should be permitted.
 *
 * Map RmmRipasChangeDestroyed to RsiRipasChangeDestroyed to simplify check
 * operation.
 */
enum ripas_change_destroyed {
	/* A RIPAS change from DESTROYED should not be permitted */
	NO_CHANGE_DESTROYED = RSI_NO_CHANGE_DESTROYED,

	/* A RIPAS change from DESTROYED should be permitted */
	CHANGE_DESTROYED = RSI_CHANGE_DESTROYED
};

/*
 * The RmmRecResponse enumeration represents whether the Host accepted
 * or rejected a Realm request.
 *
 * Map RmmRecResponse to RmiResponse to simplify check operation.
 */
enum ripas_response {
	ACCEPT = RMI_ACCEPT,	/* Host accepted Realm request */
	REJECT = RMI_REJECT	/* Host rejected Realm request */
};

#endif /* RIPAS_H */
