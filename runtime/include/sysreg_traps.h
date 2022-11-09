/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef SYSREGS_H
#define SYSREGS_H

struct rec;
struct rmi_rec_exit;

bool handle_sysreg_access_trap(struct rec *rec, struct rmi_rec_exit *rec_exit,
			       unsigned long esr);

#endif /* SYSREGS_H */
