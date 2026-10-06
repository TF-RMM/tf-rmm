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
#include <sro_context.h>
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

/*
 * Deactivate an ACTIVE RMM, returning RMI_ERROR_GLOBAL if any Host-managed
 * granule is still in use. The dispatcher must exclude every other RMI call
 * until this handler returns, including SRO follow-ups and tracking queries.
 * Return RMI_BUSY while an unfinished SRO can still refer to the layout.
 *
 * Activation uses only EL3-private backing, so there is no donated memory to
 * reclaim here. Retain that backing and the configuration for reactivation.
 * @res receives RMI_SUCCESS after publishing INIT, or the failure status with
 * the lifecycle and tracking layout unchanged.
 */
void smc_rmm_deactivate(struct smc_result *res)
{
	bool transitioned __unused;

	if (glob_data_get_rmm_state() != RMM_STATE_ACTIVE) {
		res->x[0] = RMI_ERROR_GLOBAL;
		return;
	}

	/* A sealed SRO may retain metadata pointers even with no delegated pages. */
	if (!sro_ctx_is_idle()) {
		res->x[0] = RMI_BUSY;
		return;
	}
	if (!tracking_region_deactivate()) {
		res->x[0] = RMI_ERROR_GLOBAL;
		return;
	}

	transitioned = glob_data_transition_rmm_state(RMM_STATE_ACTIVE,
						      RMM_STATE_INIT);
	assert(transitioned);

	res->x[0] = RMI_SUCCESS;
}

/*
 * Return the architectural RMM state. The ABI encoding is deliberately
 * translated from the internal state, whose enum also contains an
 * intermediate value.
 */
void smc_rmm_state_get(struct smc_result *res)
{
	enum rmm_state state = glob_data_get_rmm_state();

	res->x[0] = RMI_SUCCESS;
	res->x[1] = (state == RMM_STATE_ACTIVE) ?
			RMI_RMM_STATE_ACTIVE : RMI_RMM_STATE_INIT;
}

/* cppcheck-suppress misra-c2012-8.7 */
enum rmm_state get_rmm_active_state(void)
{
	return glob_data_get_rmm_state();
}
