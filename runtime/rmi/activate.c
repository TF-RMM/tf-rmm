/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */
#include <activate.h>
#include <debug.h>
#include <smc-handler.h>
#include <smc-rmi.h>

static enum rmm_state rmm_state = RMM_STATE_INIT;

/*
 * smc_rmm_activate
 *
 * Input: None
 *
 * Output values:
 * x0		- Command return status
 */

/* @TODO Enhance implementation later */
unsigned long smc_rmm_activate(void)
{
	/* Validate the RMM state */
	if (rmm_state != RMM_STATE_INIT) {
		ERROR("RMM is in invalid state\n");
		return RMI_ERROR_GLOBAL;
	}

	rmm_state = RMM_STATE_ACTIVE;
	return RMI_SUCCESS;
}

enum rmm_state get_rmm_active_state(void)
{
	return rmm_state;
}
