/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */
#include <activate.h>
#include <assert.h>
#include <debug.h>
#include <glob_data.h>
#include <smc-handler.h>
#include <smc-rmi.h>
#include <stdbool.h>
#include <tracking_region.h>

/*
 * Activate the RMM after atomically claiming its configured tracking layout.
 * The claim changes the global state from INIT to INTERMEDIATE, excluding
 * configuration and other activation calls while granules are initialized.
 *
 * The struct tracking_region array always has EL3-private backing from cold boot.
 * Initialize FINE when fine backing was also preallocated, or COARSE/NONE
 * when fine backing will be donated later. Publish ACTIVE synchronously;
 * @res receives RMI_SUCCESS, or RMI_ERROR_GLOBAL for an invalid lifecycle state.
 */
/* cppcheck-suppress misra-c2012-8.7 */
void smc_rmm_activate(struct smc_result *res)
{
	bool transitioned;

	/* Claim activation before its metadata layout can be reconfigured. */
	if (!glob_data_transition_rmm_state(RMM_STATE_INIT,
					   RMM_STATE_INTERMEDIATE)) {
		ERROR("RMM is in invalid state\n");
		res->x[0] = RMI_ERROR_GLOBAL;
		return;
	}

#ifdef RMM_ALLOC_TRACKING_DATA
	tracking_region_activate(trs_fine);
#else
	tracking_region_activate(trs_coarse);
#endif
	transitioned = glob_data_transition_rmm_state(RMM_STATE_INTERMEDIATE,
						      RMM_STATE_ACTIVE);
	assert(transitioned);
	(void)transitioned;
	res->x[0] = RMI_SUCCESS;
}

/* cppcheck-suppress misra-c2012-8.7 */
enum rmm_state get_rmm_active_state(void)
{
	return glob_data_get_rmm_state();
}
