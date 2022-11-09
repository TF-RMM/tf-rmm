/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef	RSI_MEMORY_H
#define	RSI_MEMORY_H

#include <smc-rsi.h>

struct rec;
struct rmi_rec_exit;

bool handle_rsi_ipa_state_set(struct rec *rec, struct rmi_rec_exit *rec_exit);

rsi_status_t handle_rsi_ipa_state_get(struct rec *rec, unsigned long ipa,
				      enum ripas *ripas);

#endif /* RSI_MEMORY_H */
