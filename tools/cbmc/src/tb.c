/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include "tb.h"
#include "tb_common.h"
#include "tb_granules.h"

#include "rsi-handler.h"
#include "smc-handler.h"
#include "smc-rsi.h"
#include "smc.h"

void __init_global_state(unsigned long cmd)
{
	REACHABLE;
	global_sanity_check();
	/* Set up all the system register */
	host_util_setup_sysreg_and_boot_manifest();
	switch (cmd) {
	case SMC_RMM_FEATURES: {
			return;
		}
	case SMC_RMM_GRANULE_DELEGATE:
	case SMC_RMM_GRANULE_UNDELEGATE: {
			init_granule_and_page();
			return;
		}
	default:
		ASSERT(false, "tb_handle_smc fail");
	}
}

/* Sanity check on the implementation of CBMC */
void global_sanity_check(void)
{
	__CPROVER_cover(valid_pa(nondet_unsigned_long()));
}

void tb_handle_smc(struct tb_regs *config)
{
	unsigned long result = 0;

	switch (config->X0) {
	case SMC_RMM_GRANULE_DELEGATE:
		result = smc_granule_delegate(config->X1);
		break;
	case SMC_RMM_GRANULE_UNDELEGATE:
		result = smc_granule_undelegate(config->X1);
		break;
	default:
		ASSERT(false, "_tb_handle_smc fail");
	}

	/* Update the return value. */
	config->X0 = result;
}

void __tb_expect_fail(void)
{
	/* Assertion used to check consistency of the testbench */
}
