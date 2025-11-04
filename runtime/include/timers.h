/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef TIMERS_H
#define TIMERS_H

#include <arch.h>
#include <utils_def.h>

struct rec;
struct rmi_rec_exit;
struct rec_plane;
STRUCT_TYPE sysreg_state;

/*
 * Timer context structure.
 * Align on cache writeback granule to minimise cache line thrashing
 * when allocated as an array for use by each CPU.
 */
struct timer_state {
	unsigned long phys_ctl;
	unsigned long phys_cval;
	unsigned long virt_ctl;
	unsigned long virt_cval;
};

bool check_pending_timers(STRUCT_TYPE sysreg_state *sysregs);
void report_timer_state_to_ns(struct rec *rec, struct rmi_rec_exit *rec_exit);
void hyp_timer_save_state(struct timer_state *el2_timer);
void hyp_timer_restore_state(struct timer_state *el2_timer);
bool is_timer_enabled(unsigned long cnt_ctl);
void multiplex_el2_timer(struct rec *rec);

#endif /* TIMERS_H */
