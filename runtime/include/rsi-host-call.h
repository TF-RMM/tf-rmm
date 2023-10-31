/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef RSI_HOST_CALL_H
#define RSI_HOST_CALL_H

#include <rsi-walk.h>

struct rec;
struct rmi_rec_enter;

struct rsi_walk_result complete_rsi_host_call(struct rec *rec,
					      struct rmi_rec_enter *rec_enter);

#endif /* RSI_HOST_CALL_H */
