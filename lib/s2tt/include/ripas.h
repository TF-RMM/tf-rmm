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
	/* Address where no Realm resources are mapped */
	RIPAS_EMPTY = RMI_EMPTY,
	/* Address where private code or data owned by the Realm is mapped */
	RIPAS_RAM = RMI_RAM,
	/*
	 * Address which is inaccessible to the Realm due to an action taken
	 * by the Host
	 */
	RIPAS_DESTROYED = RMI_DESTROYED,
	/* Address where memory of an assigned Realm device is mapped */
	RIPAS_DEV = RMI_DEV
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

#endif /* RIPAS_H */
