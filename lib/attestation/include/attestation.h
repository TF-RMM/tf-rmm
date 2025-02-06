/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef ATTESTATION_H
#define ATTESTATION_H

#include <stdbool.h>
#include <stddef.h>

/*
 * Performs any early initialization needed for the crypto library.
 */
int attestation_init(void);

bool attestation_initialised(void);

#endif /* ATTESTATION_H */
