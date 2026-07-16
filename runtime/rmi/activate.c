/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */
#include <activate.h>
#include <debug.h>
#include <glob_data.h>
#include <smc-handler.h>
#include <smc-rmi.h>

/*
 * smc_rmm_activate
 *
 * Input: None
 *
 * Output values:
 * x0		- Command return status
 */

/* @TODO Enhance implementation later */
/* cppcheck-suppress misra-c2012-8.7 */
void smc_rmm_activate(struct smc_result *res)
{
	/* Validate the RMM state */
	if (glob_data_get_rmm_state() != RMM_STATE_INIT) {
		ERROR("RMM is in invalid state\n");
		res->x[0] = RMI_ERROR_GLOBAL;
		return;
	}

	glob_data_set_rmm_state(RMM_STATE_ACTIVE);
	res->x[0] = RMI_SUCCESS;
}

/* cppcheck-suppress misra-c2012-8.7 */
enum rmm_state get_rmm_active_state(void)
{
	return glob_data_get_rmm_state();
}
