/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef ATTEST_SERVICES_H
#define ATTEST_SERVICES_H

#include <app_common.h>
#include <stdint.h>

#if ATTEST_EL3_TOKEN_SIGN
int el3_token_sign_queue_try_enqueue(struct service_el3_token_sign_request *request);
#endif

#endif /* ATTEST_SERVICES_H */
