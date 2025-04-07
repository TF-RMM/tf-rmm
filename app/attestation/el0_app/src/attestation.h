/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef ATTESTATION_H
#define ATTESTATION_H

#include <stddef.h>

/*
 * Performs any early initialization needed for the crypto library.
 */
int attestation_init(void);

#endif /* ATTESTATION_H */
