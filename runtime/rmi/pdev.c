/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <app.h>
#include <arch.h>
#include <arch_features.h>
#include <buffer.h>
#include <debug.h>
#include <dev.h>
#include <dev_assign_app.h>
#include <feature.h>
#include <granule.h>
#include <sizes.h>
#include <smc-handler.h>
#include <smc-rmi.h>
#include <string.h>
#include <utils_def.h>

/*
 * This function will only be invoked when the PDEV create fails or when PDEV is
 * being destroyed. Hence the PDEV will not be in use when this function is
 * called and therefore no lock is acquired before its invocation.
 */
static void pdev_restore_aux_granules_state(struct granule *pdev_aux[],
					    unsigned int cnt, bool scrub)
{
	for (unsigned int i = 0U; i < cnt; i++) {
		struct granule *g_pdev_aux = pdev_aux[i];

		granule_lock(g_pdev_aux, GRANULE_STATE_PDEV_AUX);
		if (scrub) {
			buffer_granule_memzero(g_pdev_aux,
			   (enum buffer_slot)((unsigned int)SLOT_PDEV_AUX0 + i));
		}
		granule_unlock_transition(g_pdev_aux, GRANULE_STATE_DELEGATED);
	}
}

/*
 * todo:
 * Validate device specific PDEV parameters by traversing all previously created
 * PDEVs and check against current PDEV parameters. This implements
 * RmiPdevParamsIsValid of RMM specification.
 */
static int validate_rmi_pdev_params(struct rmi_pdev_params *pd_params)

{
	(void)pd_params;
	/*
	 * Check if device identifier, Root Port identifier, IDE stream
	 * identifier, RID range are valid.
	 */

	/*
	 * Check if device identifier is not equal to the device identifier of
	 * another PDEV
	 */

	/* Whether RID range does not overlap the RID range of another PDEV */

	/*
	 * Every address range falls within an MMIO range permitted by the system
	 */

	/*
	 * None of the address ranges overlaps another address range for this
	 * PDEV
	 */

	return 0;
}

static unsigned long pdev_get_aux_count_from_flags(unsigned long pdev_flags)
{
	unsigned long aux_count;

	(void)pdev_flags;

	/*
	 * The current implementation requires that RMI_PDEV_SPDM_TRUE
	 * is set in the flags.
	 */
	assert(EXTRACT(RMI_PDEV_FLAGS_SPDM, pdev_flags) == RMI_PDEV_SPDM_TRUE);

	/*
	 * Currently, the number of pages required to instantiate an app is
	 * hardcoded in the app header. In this implementation, aux_count
	 * does not depend on the flags set in pdev_flags. The worst case
	 * (i.e., the most granules) is assumed.
	 */
	aux_count = app_get_required_granule_count(RMM_DEV_ASSIGN_APP_ID);
	assert(aux_count <= PDEV_PARAM_AUX_GRANULES_MAX);

	return aux_count;
}

/*
 * smc_pdev_aux_count
 *
 * Get number of auxiliary Granules required for a PDEV.
 *
 * flags	- PDEV flags
 * res		- SMC result
 */
void smc_pdev_aux_count(unsigned long flags, struct smc_result *res)
{
	if (is_rmi_feat_da_enabled()) {
		res->x[0] = RMI_SUCCESS;
		res->x[1] = pdev_get_aux_count_from_flags(flags);
	} else {
		res->x[0] = SMC_NOT_SUPPORTED;
	}
}

/*
 * smc_pdev_create
 *
 * pdev_ptr		- PA of the PDEV
 * pdev_params_ptr	- PA of PDEV parameters
 */
unsigned long smc_pdev_create(unsigned long pdev_ptr,
			      unsigned long pdev_params_ptr)
{
	struct granule *g_pdev;
	struct granule *g_pdev_params;
	struct pdev *pd;
	struct rmi_pdev_params pdev_params; /* this consumes 4k of stack */
	struct granule *pdev_aux_granules[PDEV_PARAM_AUX_GRANULES_MAX];
	unsigned long num_aux_req;
	bool ns_access_ok;
	void *aux_mapped_addr;
	struct dev_assign_params dparams;
	unsigned long smc_rc;
	int rc;

	if (!is_rmi_feat_da_enabled()) {
		return SMC_NOT_SUPPORTED;
	}

	if (!GRANULE_ALIGNED(pdev_ptr) ||
	    !GRANULE_ALIGNED(pdev_params_ptr)) {
		return RMI_ERROR_INPUT;
	}

	/* Map and copy PDEV parameters */
	g_pdev_params = find_granule(pdev_params_ptr);
	if ((g_pdev_params == NULL) ||
	    (granule_unlocked_state(g_pdev_params) != GRANULE_STATE_NS)) {
		return RMI_ERROR_INPUT;
	}

	ns_access_ok = ns_buffer_read(SLOT_NS, g_pdev_params, 0U,
				      sizeof(struct rmi_pdev_params),
				      &pdev_params);
	if (!ns_access_ok) {
		return RMI_ERROR_INPUT;
	}

	/*
	 * Validate RmiPdevFlags. RMM supports PCIE off-chip device represented
	 * by flags: SPDM=true, IDE=true, COHERENT=false, P2P= false.
	 */
	/* coverity[uninit_use:SUPPRESS] */
	if ((EXTRACT(RMI_PDEV_FLAGS_SPDM, pdev_params.flags) !=
	     RMI_PDEV_SPDM_TRUE) ||
	    (EXTRACT(RMI_PDEV_FLAGS_IDE, pdev_params.flags) !=
	     RMI_PDEV_IDE_TRUE) ||
	    (EXTRACT(RMI_PDEV_FLAGS_COHERENT, pdev_params.flags) !=
	     RMI_PDEV_COHERENT_FALSE) ||
	    (EXTRACT(RMI_PDEV_FLAGS_P2P, pdev_params.flags) !=
	     RMI_PDEV_COHERENT_FALSE)) {
		return RMI_ERROR_NOT_SUPPORTED;
	}

	/* Validate PDEV parameters num_aux */
	num_aux_req = pdev_get_aux_count_from_flags(pdev_params.flags);
	/* coverity[uninit_use:SUPPRESS] */
	if ((pdev_params.num_aux == 0U) ||
	    (pdev_params.num_aux != num_aux_req)) {
		ERROR("ERROR: PDEV need %ld aux granules, host allocated %ld.\n",
		      num_aux_req, pdev_params.num_aux);
		return RMI_ERROR_INPUT;
	}

	/* Validate PDEV parameters ncoh_num_addr_range. */
	/* coverity[uninit_use:SUPPRESS] */
	if (pdev_params.ncoh_num_addr_range > PDEV_PARAM_NCOH_ADDR_RANGE_MAX) {
		return RMI_ERROR_INPUT;
	}

	/* Validate hash algorithm */
	/* coverity[uninit_use:SUPPRESS] */
	if ((pdev_params.hash_algo != RMI_HASH_SHA_256) &&
	    (pdev_params.hash_algo != RMI_HASH_SHA_512)) {
		return RMI_ERROR_INPUT;
	}

	/* cppcheck-suppress knownConditionTrueFalse */
	if (validate_rmi_pdev_params(&pdev_params) != 0) {
		return RMI_ERROR_INPUT;
	}

	/* Loop through pdev_aux_granules and transit them */
	for (unsigned int i = 0U; i < pdev_params.num_aux; i++) {
		struct granule *g_pdev_aux;

		/* coverity[uninit_use_in_call:SUPPRESS] */
		g_pdev_aux = find_lock_granule(pdev_params.aux[i],
					       GRANULE_STATE_DELEGATED);
		if (g_pdev_aux == NULL) {
			pdev_restore_aux_granules_state(pdev_aux_granules, i,
							false);
			return RMI_ERROR_INPUT;
		}
		granule_unlock_transition(g_pdev_aux, GRANULE_STATE_PDEV_AUX);
		pdev_aux_granules[i] = g_pdev_aux;
	}

	/* Lock pdev granule and map it */
	g_pdev = find_lock_granule(pdev_ptr, GRANULE_STATE_DELEGATED);
	if (g_pdev == NULL) {
		smc_rc = RMI_ERROR_INPUT;
		goto out_restore_pdev_aux_granule_state;
	}

	pd = buffer_granule_map(g_pdev, SLOT_PDEV);
	if (pd == NULL) {
		smc_rc = RMI_ERROR_INPUT;
		granule_unlock_transition(g_pdev, GRANULE_STATE_DELEGATED);
		goto out_restore_pdev_aux_granule_state;
	}

	/* Map all PDEV aux granules to slot starting SLOT_PDEV_AUX0 */
	aux_mapped_addr = buffer_pdev_aux_granules_map(pdev_aux_granules,
						       (unsigned int)pdev_params.num_aux);
	if (aux_mapped_addr == NULL) {
		smc_rc = RMI_ERROR_INPUT;
		goto out_unmap_pdev_slot_buffer;
	}

	/* Call init routine to initialize device class specific state */
	dparams.dev_handle = (void *)pd;
	dparams.rmi_hash_algo = pdev_params.hash_algo;
	dparams.cert_slot_id = (uint8_t)pdev_params.cert_id;

	if (EXTRACT(RMI_PDEV_FLAGS_IDE, pdev_params.flags) ==
	    RMI_PDEV_IDE_TRUE) {
		dparams.has_ide = true;
		dparams.ecam_addr = pdev_params.ecam_addr;
		dparams.rp_id = pdev_params.root_id;
		dparams.ide_sid = pdev_params.ide_sid;
	} else {
		dparams.has_ide = false;
	}
	/* Use the PDEV aux pages for the DA app */
	uintptr_t granule_pas[PDEV_PARAM_AUX_GRANULES_MAX];

	for (unsigned int i = 0; i < pdev_params.num_aux; ++i) {
		granule_pas[i] = granule_addr(pdev_aux_granules[i]);
	}

	rc = dev_assign_app_init(&pd->da_app_data,
		granule_pas,
		pdev_params.num_aux,
		aux_mapped_addr, &dparams);

	if (rc == DEV_ASSIGN_STATUS_SUCCESS) {
		/* Initialize PDEV */
		pd->g_pdev = g_pdev;
		pd->rmi_state = RMI_PDEV_STATE_NEW;
		pd->rmi_flags = pdev_params.flags;
		pd->num_vdevs = 0;
		pd->rmi_hash_algo = pdev_params.hash_algo;
		pd->num_aux = (unsigned int)pdev_params.num_aux;
		(void)memcpy((void *)pd->g_aux, (void *)pdev_aux_granules, pdev_params.num_aux *
			     sizeof(struct granule *));

		/* Initialize PDEV communication state */
		pd->dev_comm_state = DEV_COMM_PENDING;

		/* Initialize PDEV pcie device */
		pd->dev.bdf = pdev_params.pdev_id;
		pd->dev.segment_id = pdev_params.segment_id;
		pd->dev.ecam_addr = pdev_params.ecam_addr;
		pd->dev.root_id = pdev_params.root_id;
		pd->dev.cert_slot_id = pdev_params.cert_id;
		pd->dev.ide_sid = pdev_params.ide_sid;
		pd->dev.rid_base = pdev_params.rid_base;
		pd->dev.rid_top = pdev_params.rid_top;
		pd->dev.ncoh_num_addr_range = pdev_params.ncoh_num_addr_range;
		(void)memcpy(&pd->dev.ncoh_addr_range,
			     &pdev_params.ncoh_addr_range,
			     (sizeof(struct rmi_address_range) *
			      pdev_params.ncoh_num_addr_range));

		smc_rc = RMI_SUCCESS;
	} else {
		smc_rc = RMI_ERROR_INPUT;
	}

	/* Unmap all PDEV aux granules */
	buffer_pdev_aux_unmap(aux_mapped_addr, (unsigned int)pdev_params.num_aux);

out_unmap_pdev_slot_buffer:
	/* unmap PDEV buffer from slot PDEV */
	buffer_unmap(pd);

	/*
	 * On success, unlock and transit the PDEV granule state to
	 * GRANULE_STATE_PDEV else unlock and retain the state at
	 * GRANULE_STATE_DELEGATED.
	 */
	if (smc_rc == RMI_SUCCESS) {
		granule_unlock_transition(g_pdev, GRANULE_STATE_PDEV);
	} else {
		granule_unlock_transition(g_pdev, GRANULE_STATE_DELEGATED);
	}

out_restore_pdev_aux_granule_state:
	if (smc_rc != RMI_SUCCESS) {
		/*
		 * Transit all PDEV AUX granule state back to
		 * GRANULE_STATE_DELEGATED
		 */
		pdev_restore_aux_granules_state(pdev_aux_granules,
				(unsigned int)pdev_params.num_aux, false);
	}

	return smc_rc;
}

/*
 * smc_pdev_get_state
 *
 * Get state of a PDEV.
 *
 * pdev_ptr	- PA of the PDEV
 * res		- SMC result
 */
void smc_pdev_get_state(unsigned long pdev_ptr, struct smc_result *res)
{
	struct granule *g_pdev;
	struct pdev *pd;

	if (!is_rmi_feat_da_enabled()) {
		res->x[0] = SMC_NOT_SUPPORTED;
		return;
	}

	if (!GRANULE_ALIGNED(pdev_ptr)) {
		goto out_err_input;
	}

	/* Lock pdev granule and map it */
	g_pdev = find_lock_granule(pdev_ptr, GRANULE_STATE_PDEV);
	if (g_pdev == NULL) {
		goto out_err_input;
	}

	pd = buffer_granule_map(g_pdev, SLOT_PDEV);
	if (pd == NULL) {
		granule_unlock(g_pdev);
		goto out_err_input;
	}

	assert(pd->g_pdev == g_pdev);
	assert(pd->rmi_state <= RMI_PDEV_STATE_ERROR);
	res->x[0] = RMI_SUCCESS;
	res->x[1] = pd->rmi_state;

	buffer_unmap(pd);
	granule_unlock(g_pdev);

	return;

out_err_input:
	res->x[0] = RMI_ERROR_INPUT;
}

/*
 * Destroy a PDEV. Host can reclaim PDEV resources when the PDEV state is STOPPED
 * using RMI PDEV_DESTROY.
 *
 * pdev_ptr	- PA of the PDEV
 */
unsigned long smc_pdev_destroy(unsigned long pdev_ptr)
{
	int rc __unused;
	struct granule *g_pdev;
	void *aux_mapped_addr;
	struct pdev *pd;

	if (!is_rmi_feat_da_enabled()) {
		return SMC_NOT_SUPPORTED;
	}

	if (!GRANULE_ALIGNED(pdev_ptr)) {
		return RMI_ERROR_INPUT;
	}

	/* Lock pdev granule and map it */
	g_pdev = find_lock_granule(pdev_ptr, GRANULE_STATE_PDEV);
	if (g_pdev == NULL) {
		return RMI_ERROR_INPUT;
	}

	pd = buffer_granule_map(g_pdev, SLOT_PDEV);
	if (pd == NULL) {
		granule_unlock(g_pdev);
		return RMI_ERROR_INPUT;
	}

	if (pd->rmi_state != RMI_PDEV_STATE_STOPPED) {
		buffer_unmap(pd);
		granule_unlock(g_pdev);
		return RMI_ERROR_DEVICE;
	}

	/* Map PDEV aux granules and map PDEV heap */
	aux_mapped_addr = buffer_pdev_aux_granules_map(pd->g_aux, pd->num_aux);
	assert(aux_mapped_addr != NULL);

	/* Deinit the DSM context state */
	rc = (int)app_run(&pd->da_app_data, DEVICE_ASSIGN_APP_FUNC_ID_DEINIT,
				0, 0, 0, 0);
	assert(rc == DEV_ASSIGN_STATUS_SUCCESS);

	/* Unmap all PDEV aux granules and heap */
	buffer_pdev_aux_unmap(aux_mapped_addr, pd->num_aux);

	/*
	 * Scrub PDEV AUX granules and move its state from PDEV_AUX to
	 * delegated.
	 */
	pdev_restore_aux_granules_state(pd->g_aux, pd->num_aux, true);

	/* Move the PDEV granule from PDEV to delegated state */
	granule_memzero_mapped(pd);
	buffer_unmap(pd);

	granule_unlock_transition(g_pdev, GRANULE_STATE_DELEGATED);

	return RMI_SUCCESS;
}
