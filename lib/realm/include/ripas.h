/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef RIPAS_H
#define RIPAS_H

/* The RmmRipas enumeration representing realm IPA state */
#define	EMPTY	0U	/* Unused IPA location */
#define	RAM	1U	/* Private code or data owned by the Realm */

/*
 * The RmiRipas enumeration representing realm IPA state.
 *
 * Map RmmRipas to RmiRipas to simplify code/decode operations.
 */
enum ripas {
	RMI_EMPTY = EMPTY,
	RMI_RAM = RAM
};

#endif /* RIPAS_H */
