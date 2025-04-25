/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef STACK_PROTECTOR_H
#define STACK_PROTECTOR_H

#include <types.h>

/* Function called when stack protection check fails. */
void __dead2 __stack_chk_fail(void);

/*
 * Initialize or update the canary value.
 */
void rmm_init_stack_canary(void);

#endif /* STACK_PROTECTOR_H */
