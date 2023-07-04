/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef RIPAS_H
#define RIPAS_H

#include <smc-rmi.h>

/*
 * The RmmRipas enumeration represents realm IPA state.
 *
 * Map RmmRipas to RmiRipas to simplify code/decode operations.
 */
enum ripas {
	RIPAS_EMPTY = RMI_EMPTY,	/* Unused IPA for Realm */
	RIPAS_RAM = RMI_RAM,		/* IPA used for Code/Data by Realm */
	RIPAS_DESTROYED = RMI_DESTROYED	/* IPA is inaccessible to the Realm */
};

#endif /* RIPAS_H */
