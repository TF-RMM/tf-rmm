/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef TIMERS_H
#define TIMERS_H

struct rec;
struct rmi_rec_exit;

bool check_pending_timers(struct rec *rec);
void report_timer_state_to_ns(struct rmi_rec_exit *rec_exit);

#endif /* TIMERS_H */
