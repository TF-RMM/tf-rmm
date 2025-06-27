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


/* Validate RmiDevCommData.RmiDevCommEnter argument passed by Host */
static unsigned long copyin_and_validate_dev_comm_enter(
				  unsigned long dev_comm_data_ptr,
				  struct rmi_dev_comm_enter *enter_args,
				  unsigned int dev_comm_state)
{
	struct granule *g_dev_comm_data;
	struct granule *g_buf;
	bool ns_access_ok;

	g_dev_comm_data = find_granule(dev_comm_data_ptr);
	if ((g_dev_comm_data == NULL) ||
	    (granule_unlocked_state(g_dev_comm_data) != GRANULE_STATE_NS)) {
		return RMI_ERROR_INPUT;
	}

	ns_access_ok = ns_buffer_read(SLOT_NS, g_dev_comm_data,
				      RMI_DEV_COMM_ENTER_OFFSET,
				      sizeof(struct rmi_dev_comm_enter),
				      enter_args);
	if (!ns_access_ok) {
		return RMI_ERROR_INPUT;
	}

	if (!GRANULE_ALIGNED(enter_args->req_addr) ||
	    !GRANULE_ALIGNED(enter_args->resp_addr) ||
	    (enter_args->resp_len > GRANULE_SIZE)) {
		return RMI_ERROR_INPUT;
	}

	if ((enter_args->status == RMI_DEV_COMM_ENTER_STATUS_RESPONSE) &&
		(enter_args->resp_len == 0U)) {
		return RMI_ERROR_INPUT;
	}

	/* Check if request and response buffers are in NS PAS */
	g_buf = find_granule(enter_args->req_addr);
	if ((g_buf == NULL) ||
	    (granule_unlocked_state(g_buf) != GRANULE_STATE_NS)) {
		return RMI_ERROR_INPUT;
	}

	g_buf = find_granule(enter_args->resp_addr);
	if ((g_buf == NULL) ||
	    (granule_unlocked_state(g_buf) != GRANULE_STATE_NS)) {
		return RMI_ERROR_INPUT;
	}

	if ((dev_comm_state == DEV_COMM_ACTIVE) &&
	    ((enter_args->status != RMI_DEV_COMM_ENTER_STATUS_RESPONSE) &&
	    (enter_args->status != RMI_DEV_COMM_ENTER_STATUS_ERROR))) {
		return RMI_ERROR_DEVICE;
	}

	if ((dev_comm_state == DEV_COMM_PENDING) &&
	    (enter_args->status != RMI_DEV_COMM_ENTER_STATUS_NONE)) {
		return RMI_ERROR_DEVICE;
	}
	return RMI_SUCCESS;
}

/*
 * copyout DevCommExitArgs
 */
static unsigned long copyout_dev_comm_exit(unsigned long dev_comm_data_ptr,
				   struct rmi_dev_comm_exit *exit_args)
{
	struct granule *g_dev_comm_data;
	bool ns_access_ok;

	g_dev_comm_data = find_granule(dev_comm_data_ptr);
	if ((g_dev_comm_data == NULL) ||
	    (granule_unlocked_state(g_dev_comm_data) != GRANULE_STATE_NS)) {
		return RMI_ERROR_INPUT;
	}

	ns_access_ok = ns_buffer_write(SLOT_NS, g_dev_comm_data,
				       RMI_DEV_COMM_EXIT_OFFSET,
				       sizeof(struct rmi_dev_comm_exit),
				       exit_args);
	if (!ns_access_ok) {
		return RMI_ERROR_INPUT;
	}

	return RMI_SUCCESS;
}

static int pdev_dispatch_cmd(struct pdev *pd, struct rmi_dev_comm_enter *enter_args,
		struct rmi_dev_comm_exit *exit_args)
{
	int rc;
	struct dev_obj_digest *comm_digest_ptr;

	if (pd->rmi_state == RMI_PDEV_STATE_NEW) {
		comm_digest_ptr = &pd->cert_digest;
	} else {
		comm_digest_ptr = NULL;
	}

	if (pd->dev_comm_state == DEV_COMM_ACTIVE) {
		return dev_assign_dev_communicate(&pd->da_app_data, enter_args,
			exit_args, comm_digest_ptr, DEVICE_ASSIGN_APP_FUNC_ID_RESUME);
	}

	switch (pd->rmi_state) {
	case RMI_PDEV_STATE_NEW:
		rc = dev_assign_dev_communicate(&pd->da_app_data, enter_args,
			exit_args, comm_digest_ptr, DEVICE_ASSIGN_APP_FUNC_ID_CONNECT_INIT);
		break;
	case RMI_PDEV_STATE_STOPPING:
		rc = dev_assign_dev_communicate(&pd->da_app_data, enter_args,
			exit_args, comm_digest_ptr, DEVICE_ASSIGN_APP_FUNC_ID_STOP_CONNECTION);
		break;
	default:
		assert(false);
		rc = -1;
	}

	return rc;
}

static unsigned long dev_communicate(struct pdev *pd,
				     unsigned long dev_comm_data_ptr)
{
	struct rmi_dev_comm_enter enter_args;
	struct rmi_dev_comm_exit exit_args;
	void *aux_mapped_addr;
	unsigned long comm_rc;
	int rc;

	assert(pd != NULL);

	if ((pd->dev_comm_state == DEV_COMM_IDLE) ||
			(pd->dev_comm_state == DEV_COMM_ERROR)) {
		return RMI_ERROR_DEVICE;
	}

	/* Validate RmiDevCommEnter arguments in DevCommData */
	/* coverity[uninit_use_in_call:SUPPRESS] */
	comm_rc = copyin_and_validate_dev_comm_enter(dev_comm_data_ptr, &enter_args,
		pd->dev_comm_state);
	if (comm_rc != RMI_SUCCESS) {
		return comm_rc;
	}

	/* Map PDEV aux granules */
	aux_mapped_addr = buffer_pdev_aux_granules_map(pd->g_aux, pd->num_aux);
	assert(aux_mapped_addr != NULL);

	rc = pdev_dispatch_cmd(pd, &enter_args, &exit_args);

	/* Unmap all PDEV aux granules */
	buffer_pdev_aux_unmap(aux_mapped_addr, pd->num_aux);

	comm_rc = copyout_dev_comm_exit(dev_comm_data_ptr,
				       &exit_args);
	if (comm_rc != RMI_SUCCESS) {
		/* todo: device status is updated but copyout data failed? */
		return RMI_ERROR_INPUT;
	}

	/*
	 * Based on the device communication results update the device IO state
	 * and PDEV state.
	 */
	switch (rc) {
	case DEV_ASSIGN_STATUS_COMM_BLOCKED:
		pd->dev_comm_state = DEV_COMM_ACTIVE;
		break;
	case DEV_ASSIGN_STATUS_ERROR:
		pd->dev_comm_state = DEV_COMM_ERROR;
		break;
	case DEV_ASSIGN_STATUS_SUCCESS:
		pd->dev_comm_state = DEV_COMM_IDLE;
		break;
	default:
		assert(false);
	}

	return RMI_SUCCESS;
}

/*
 * smc_pdev_communicate
 *
 * pdev_ptr	- PA of the PDEV
 * data_ptr	- PA of the communication data structure
 */
unsigned long smc_pdev_communicate(unsigned long pdev_ptr,
				   unsigned long dev_comm_data_ptr)
{
	struct granule *g_pdev;
	struct pdev *pd;
	unsigned long rmi_rc;

	if (!is_rmi_feat_da_enabled()) {
		return SMC_NOT_SUPPORTED;
	}

	if (!GRANULE_ALIGNED(pdev_ptr) || !GRANULE_ALIGNED(dev_comm_data_ptr)) {
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

	assert(pd->g_pdev == g_pdev);

	rmi_rc = dev_communicate(pd, dev_comm_data_ptr);

	/*
	 * Based on the device communication results update the device IO state
	 * and PDEV state.
	 */
	switch (pd->dev_comm_state) {
	case DEV_COMM_ERROR:
		if (pd->rmi_state == RMI_PDEV_STATE_STOPPING) {
			pd->rmi_state = RMI_PDEV_STATE_STOPPED;
		} else {
			pd->rmi_state = RMI_PDEV_STATE_ERROR;
		}
		break;
	case DEV_COMM_IDLE:
		if (pd->rmi_state == RMI_PDEV_STATE_NEW) {
			pd->rmi_state = RMI_PDEV_STATE_NEEDS_KEY;
		} else if (pd->rmi_state == RMI_PDEV_STATE_STOPPING) {
			pd->rmi_state = RMI_PDEV_STATE_STOPPED;
		} else {
			pd->rmi_state = RMI_PDEV_STATE_ERROR;
		}
		break;
	case DEV_COMM_ACTIVE:
		/* No state change required */
		break;
	case DEV_COMM_PENDING:
	default:
		assert(false);
	}

	buffer_unmap(pd);
	granule_unlock(g_pdev);

	return rmi_rc;
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

static unsigned long get_expected_key_size(unsigned long rmi_key_algo)
{
	switch (rmi_key_algo) {
	case RMI_SIGNATURE_ALGORITHM_ECDSA_P256:
		return 32;
	case RMI_SIGNATURE_ALGORITHM_ECDSA_P384:
		return 48;
	case RMI_SIGNATURE_ALGORITHM_RSASSA_3072:
		return 384;
	default:
		return 0;
	}
}

static bool public_key_sig_algo_valid(unsigned long rmi_key_algo)
{
	return (rmi_key_algo == RMI_SIGNATURE_ALGORITHM_ECDSA_P256) ||
	       (rmi_key_algo == RMI_SIGNATURE_ALGORITHM_ECDSA_P384) ||
	       (rmi_key_algo == RMI_SIGNATURE_ALGORITHM_RSASSA_3072);
}

/*
 * Provide public key associated with a PDEV.
 *
 * pdev_ptr		- PA of the PDEV
 * pubkey_params_ptr	- PA of the pubkey parameters
 */
unsigned long smc_pdev_set_pubkey(unsigned long pdev_ptr,
				  unsigned long pubkey_params_ptr)
{
	struct granule *g_pdev;
	struct granule *g_pubkey_params;
	void *aux_mapped_addr;
	bool ns_access_ok;
	struct pdev *pd;
	struct rmi_public_key_params pubkey_params;
	unsigned long dev_assign_public_key_sig_algo;
	unsigned long dev_assign_public_key_expected_size;
	unsigned long smc_rc;
	int rc;

	if (!is_rmi_feat_da_enabled()) {
		return SMC_NOT_SUPPORTED;
	}

	if (!GRANULE_ALIGNED(pdev_ptr) || !GRANULE_ALIGNED(pubkey_params_ptr)) {
		return RMI_ERROR_INPUT;
	}

	/* Map and copy public key parameter */
	g_pubkey_params = find_granule(pubkey_params_ptr);
	if ((g_pubkey_params == NULL) ||
	    (granule_unlocked_state(g_pubkey_params) != GRANULE_STATE_NS)) {
		return RMI_ERROR_INPUT;
	}

	ns_access_ok = ns_buffer_read(SLOT_NS, g_pubkey_params, 0U,
				      sizeof(struct rmi_public_key_params),
				      &pubkey_params);
	if (!ns_access_ok) {
		return RMI_ERROR_INPUT;
	}

	/*
	 * Check key_len and metadata_len with max value.
	 */
	/* coverity[uninit_use:SUPPRESS] */
	if ((pubkey_params.key_len > PUBKEY_PARAM_KEY_LEN_MAX) ||
	    (pubkey_params.metadata_len > PUBKEY_PARAM_METADATA_LEN_MAX)) {
		return RMI_ERROR_INPUT;
	}

	/* coverity[uninit_use:SUPPRESS] */
	dev_assign_public_key_sig_algo = pubkey_params.algo;
	if (!public_key_sig_algo_valid(dev_assign_public_key_sig_algo)) {
		return RMI_ERROR_INPUT;
	}

	/*
	 * Validate 'key_len' against expected key length based on algorithm
	 */
	dev_assign_public_key_expected_size = get_expected_key_size(dev_assign_public_key_sig_algo);
	assert(dev_assign_public_key_expected_size != 0U);
	if (pubkey_params.key_len != dev_assign_public_key_expected_size) {
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

	assert(pd->g_pdev == g_pdev);

	if (pd->rmi_state != RMI_PDEV_STATE_NEEDS_KEY) {
		smc_rc = RMI_ERROR_DEVICE;
		goto out_pdev_buf_unmap;
	}

	/* Map PDEV aux granules */
	aux_mapped_addr = buffer_pdev_aux_granules_map(pd->g_aux, pd->num_aux);
	assert(aux_mapped_addr != NULL);

	rc = dev_assign_set_public_key(&pd->da_app_data, &pubkey_params);
	if (rc == DEV_ASSIGN_STATUS_SUCCESS) {
		pd->dev_comm_state = DEV_COMM_PENDING;
		pd->rmi_state = RMI_PDEV_STATE_HAS_KEY;
		smc_rc = RMI_SUCCESS;
	} else {
		smc_rc = RMI_ERROR_DEVICE;
	}

	/* Unmap all PDEV aux granules */
	buffer_pdev_aux_unmap(aux_mapped_addr, pd->num_aux);

out_pdev_buf_unmap:
	buffer_unmap(pd);

	granule_unlock(g_pdev);

	return smc_rc;
}

/*
 * Stop the PDEV. This sets the PDEV state to STOPPING, and a PDEV communicate
 * call can do device specific cleanup like terminating a secure session.
 *
 * pdev_ptr	- PA of the PDEV
 */
unsigned long smc_pdev_stop(unsigned long pdev_ptr)
{
	struct granule *g_pdev;
	unsigned long smc_rc;
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

	if ((pd->rmi_state == RMI_PDEV_STATE_COMMUNICATING) ||
	    (pd->rmi_state == RMI_PDEV_STATE_STOPPING) ||
	    (pd->rmi_state == RMI_PDEV_STATE_STOPPED)) {
		smc_rc = RMI_ERROR_DEVICE;
		goto out_pdev_buf_unmap;
	}

	if (pd->num_vdevs != 0U) {
		smc_rc = RMI_ERROR_DEVICE;
		goto out_pdev_buf_unmap;
	}

	pd->rmi_state = RMI_PDEV_STATE_STOPPING;
	pd->dev_comm_state = DEV_COMM_PENDING;
	smc_rc = RMI_SUCCESS;

out_pdev_buf_unmap:
	buffer_unmap(pd);

	granule_unlock(g_pdev);

	return smc_rc;
}

/*
 * Abort device communication associated with a PDEV.
 *
 * pdev_ptr	- PA of the PDEV
 */
unsigned long smc_pdev_abort(unsigned long pdev_ptr)
{
	int rc __unused;
	struct granule *g_pdev;
	void *aux_mapped_addr;
	unsigned long smc_rc;
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

	if ((pd->rmi_state != RMI_PDEV_STATE_NEW) &&
	    (pd->rmi_state != RMI_PDEV_STATE_HAS_KEY) &&
	    (pd->rmi_state != RMI_PDEV_STATE_COMMUNICATING)) {
		smc_rc = RMI_ERROR_DEVICE;
		goto out_pdev_buf_unmap;
	}

	/*
	 * If there is no active device communication, then mapping aux
	 * granules and cancelling an existing communication is not required.
	 */
	if (pd->dev_comm_state != DEV_COMM_ACTIVE) {
		goto pdev_reset_state;
	}

	/* Map PDEV aux granules */
	aux_mapped_addr = buffer_pdev_aux_granules_map(pd->g_aux, pd->num_aux);
	assert(aux_mapped_addr != NULL);

	/*
	 * This will resume the blocked CMA SPDM command and the recv callback
	 * handler will return error and abort the command.
	 */
	rc = dev_assign_abort_app_operation(&pd->da_app_data);
	assert(rc == 0);

	/* Unmap all PDEV aux granules */
	buffer_pdev_aux_unmap(aux_mapped_addr, pd->num_aux);

pdev_reset_state:
	/*
	 * As the device communication is aborted, if the PDEV is in
	 * communicating state then set the state to READY state.
	 *
	 * For other PDEV states, transition the comm_state to PENDING
	 * indicating RMM has device request which is ready to be sent to the
	 * device.
	 */
	if (pd->rmi_state == RMI_PDEV_STATE_COMMUNICATING) {
		pd->rmi_state = RMI_PDEV_STATE_READY;
		pd->dev_comm_state = DEV_COMM_IDLE;
	} else {
		pd->dev_comm_state = DEV_COMM_PENDING;
	}
	smc_rc = RMI_SUCCESS;

out_pdev_buf_unmap:
	buffer_unmap(pd);

	granule_unlock(g_pdev);

	return smc_rc;
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
