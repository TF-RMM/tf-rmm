/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef TB_H__
#define TB_H__

#include "smc-rmi.h"
#include "tb_common.h"
#include "tb_granules.h"
#include "tb_realm.h"
#include "tb_rec.h"

typedef uint64_t rmi_interface_version_t;

/* Initialize the global state based on the commands */
void __init_global_state(unsigned long cmd);

/* Sanity check on the implementation of CBMC */
void global_sanity_check(void);

/* Call the function based on the X0 value in `config` */
void tb_handle_smc(struct tb_regs *config);

/* Assertion used to check consistency of the testbench */
void __tb_expect_fail(void);

#endif /* !TB_H */
