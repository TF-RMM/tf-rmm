/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef INJECT_EXP_H
#define INJECT_EXP_H

struct rec;

void inject_sync_idabort(unsigned long fsc);
void inject_sync_idabort_rec(struct rec *rec, unsigned long fsc);
void realm_inject_undef_abort(void);

#endif /* INJECT_EXP_H */
