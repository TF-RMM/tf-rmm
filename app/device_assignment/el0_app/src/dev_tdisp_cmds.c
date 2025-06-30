/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <debug.h>
#include <dev_assign_private.h>
#include <library/pci_tdisp_requester_lib.h>
#include <string.h>

int dev_tdisp_lock_main(struct dev_assign_info *info)
{
	libspdm_return_t status;
	pci_tdisp_interface_id_t tdisp_id;
	pci_tdisp_requester_capabilities_t req_caps;
	pci_tdisp_responder_capabilities_t rsp_caps;
	pci_tdisp_lock_interface_param_t lock_param;
	struct dev_assign_tdisp_params *tdisp_params = &info->dev_assign_op_params.tdisp_params;
	uint8_t tdi_state;

	assert(info->dev_assign_op_params.param_type == DEV_ASSIGN_OP_PARAMS_TDISP);

	(void)memset(&tdisp_id, 0, sizeof(pci_tdisp_interface_id_t));

	tdisp_id.function_id = tdisp_params->tdi_id;

	/* TDISP_GET_VERSION */
	status = pci_tdisp_get_version(NULL, info->libspdm_ctx,
				       &info->session_id, &tdisp_id);
	if (status != LIBSPDM_STATUS_SUCCESS) {
		ERROR("%s: pci_tdisp_get_version failed. tdi_id = %u, status = 0x%x\n",
			__func__, tdisp_params->tdi_id, status);
		return DEV_ASSIGN_STATUS_ERROR;
	}

	/* TDISP_GET_CAPABILITIES */
	(void)memset(&req_caps, 0, sizeof(pci_tdisp_requester_capabilities_t));
	req_caps.tsm_caps = 0;
	status = pci_tdisp_get_capabilities(NULL, info->libspdm_ctx,
					    &info->session_id, &tdisp_id,
					    &req_caps, &rsp_caps);
	if (status != LIBSPDM_STATUS_SUCCESS) {
		ERROR("%s: pci_tdisp_get_capabilities failed. tdi_id = %u, status = 0x%x\n",
			__func__, tdisp_params->tdi_id, status);
		return DEV_ASSIGN_STATUS_ERROR;
	}

	/* TDISP_GET_DEVICE_INTERFACE_STATE */
	status = pci_tdisp_get_interface_state(NULL,
					       info->libspdm_ctx,
					       &info->session_id, &tdisp_id,
					       &tdi_state);
	if (status != LIBSPDM_STATUS_SUCCESS) {
		ERROR("%s: pci_tdisp_get_interface_state failed. tdi_id = %u, status = 0x%x\n",
			__func__, tdisp_params->tdi_id, status);
		return DEV_ASSIGN_STATUS_ERROR;
	}

	/* coverity[uninit_use:SUPPRESS] */
	if (tdi_state != (uint8_t)PCI_TDISP_INTERFACE_STATE_CONFIG_UNLOCKED) {
		ERROR("%s: tdi_id %u not in TDSIP unlocked state\n",
			__func__, tdisp_params->tdi_id);
		return DEV_ASSIGN_STATUS_ERROR;
	}

	/* TDISP_LOCK_INTERFACE_REQ */
	(void)memset(&lock_param, 0, sizeof(pci_tdisp_lock_interface_param_t));

	/* TODO: Derive parameters according to current platform */
	/* coverity[uninit_use:SUPPRESS] */
	lock_param.flags = (uint16_t)(rsp_caps.lock_interface_flags_supported &
				      ~U(PCI_TDISP_LOCK_INTERFACE_FLAGS_LOCK_MSIX));
	lock_param.default_stream_id = 0;
	lock_param.mmio_reporting_offset = 0xD0000000;

	assert(tdisp_params->nonce_ptr_is_valid);
	status = pci_tdisp_lock_interface(NULL, info->libspdm_ctx,
					  &info->session_id, &tdisp_id,
					  &lock_param,
					  tdisp_params->start_interface_nonce_buffer);
	if (status != LIBSPDM_STATUS_SUCCESS) {
		ERROR("%s: pci_tdisp_lock_interface failed. tdi_id = %u, status = 0x%x\n",
			__func__, tdisp_params->tdi_id, status);
		return DEV_ASSIGN_STATUS_ERROR;
	}

	tdisp_params->nonce_is_output = true;

	/* TDISP_GET_DEVICE_INTERFACE_STATE after lock */
	status = pci_tdisp_get_interface_state(NULL,
					       info->libspdm_ctx,
					       &info->session_id, &tdisp_id,
					       &tdi_state);
	if (status != LIBSPDM_STATUS_SUCCESS) {
		ERROR("%s: pci_tdisp_get_interface_state failed. tdi_id = %u, status = 0x%x\n",
			__func__, tdisp_params->tdi_id, status);
		return DEV_ASSIGN_STATUS_ERROR;
	}

	if (tdi_state != (uint8_t)PCI_TDISP_INTERFACE_STATE_CONFIG_LOCKED) {
		ERROR("%s: TDI not in LOCKED state. tdi_id = %u\n", __func__, tdisp_params->tdi_id);
		return DEV_ASSIGN_STATUS_ERROR;
	}

	INFO("TDISP lock successful, tdi_id = %u\n", tdisp_params->tdi_id);

	return DEV_ASSIGN_STATUS_SUCCESS;
}

int dev_tdisp_report_main(struct dev_assign_info *info)
{
	libspdm_return_t status;
	pci_tdisp_interface_id_t tdisp_id;
	uint32_t ifc_report_size;
	struct dev_assign_tdisp_params *tdisp_params = &info->dev_assign_op_params.tdisp_params;

	assert(info->dev_assign_op_params.param_type == DEV_ASSIGN_OP_PARAMS_TDISP);

	(void)memset(&tdisp_id, 0, sizeof(pci_tdisp_interface_id_t));

	/* PCI_TDISP_GET_DEVICE_INTERFACE_REPORT */
	tdisp_id.function_id = tdisp_params->tdi_id;

	/*
	 * RMM does not store interface report in CMA SPDM context, instead
	 * the content is cached by NS host and a digest is computed by RMM.
	 * Limit the max meas_length to be 4096 bytes, this can be increased
	 * once CHUNK support is enabled.
	 */
	ifc_report_size = 4096U;

	status = pci_tdisp_get_interface_report(NULL,
						info->libspdm_ctx,
						&info->session_id, &tdisp_id,
						NULL, &ifc_report_size);
	if (status != LIBSPDM_STATUS_SUCCESS) {
		ERROR("%s: pci_tdisp_get_interface_report failed. tdi_id = %u, status = 0x%x\n",
			__func__, tdisp_params->tdi_id, status);
		return DEV_ASSIGN_STATUS_ERROR;
	}

	info->dev_assign_op_params.tdisp_params.nonce_is_output = false;

	INFO("TDISP report successful, tdi_id = %u\n", tdisp_params->tdi_id);

	return DEV_ASSIGN_STATUS_SUCCESS;
}

int dev_tdisp_start_main(struct dev_assign_info *info)
{
	libspdm_return_t status = LIBSPDM_STATUS_SUCCESS;
	pci_tdisp_interface_id_t tdisp_id;
	uint8_t tdi_state;
	struct dev_assign_tdisp_params *tdisp_params = &info->dev_assign_op_params.tdisp_params;
	int ret = DEV_ASSIGN_STATUS_SUCCESS;

	assert(info->dev_assign_op_params.param_type == DEV_ASSIGN_OP_PARAMS_TDISP);

	(void)memset(&tdisp_id, 0, sizeof(pci_tdisp_interface_id_t));

	/* Enable TDISP at Root Port DVSEC RME DA control register */
	if (dvsec_tdisp_enable(info) != 0) {
		ERROR("%s: dvsec_tdisp_enable failed.\n", __func__);
		ret = DEV_ASSIGN_STATUS_ERROR;
		goto out;
	}

	/* TDISP_START_INTERFACE_REQ */
	tdisp_id.function_id = tdisp_params->tdi_id;

	assert(tdisp_params->nonce_ptr_is_valid);

#ifndef NDEBUG
	status = pci_tdisp_get_interface_state(NULL,
					       info->libspdm_ctx,
					       &info->session_id, &tdisp_id,
					       &tdi_state);
	if (status != LIBSPDM_STATUS_SUCCESS) {
		ERROR("%s: pci_tdisp_get_interface_state failed. tdi_id = %u, status = 0x%x\n",
			__func__, tdisp_params->tdi_id, status);
		status = LIBSPDM_STATUS_INVALID_STATE_PEER;
		ret = DEV_ASSIGN_STATUS_ERROR;
		goto out;
	}

	/* coverity[uninit_use:SUPPRESS] */
	assert(tdi_state == (uint8_t)PCI_TDISP_INTERFACE_STATE_CONFIG_LOCKED);
#endif

	status = pci_tdisp_start_interface(NULL, info->libspdm_ctx,
					   &info->session_id, &tdisp_id,
					   tdisp_params->start_interface_nonce_buffer);
	if (status != LIBSPDM_STATUS_SUCCESS) {
		ERROR("%s: pci_tdisp_start_interface failed. tdi_id = %u, status = 0x%x\n",
			__func__, tdisp_params->tdi_id, status);
		ret = DEV_ASSIGN_STATUS_ERROR;
		goto out;
	}

	tdisp_params->nonce_is_output = false;

	/* TDISP_GET_DEVICE_INTERFACE_STATE after start */
	status = pci_tdisp_get_interface_state(NULL,
					       info->libspdm_ctx,
					       &info->session_id, &tdisp_id,
					       &tdi_state);

	if ((status == LIBSPDM_STATUS_SUCCESS) &&
	    (tdi_state == (uint8_t)PCI_TDISP_INTERFACE_STATE_RUN)) {
		goto out;
	}

	ERROR("%s: pci_tdisp_get_interface_state failed. tdi_id = %u, status = 0x%x\n",
		__func__, tdisp_params->tdi_id, status);
	ret = DEV_ASSIGN_STATUS_ERROR;

out:
	INFO("TDISP start: tdi_id = %d, status = 0x%x\n",
		tdisp_params->tdi_id, status);
	return ret;
}

int dev_tdisp_stop_main(struct dev_assign_info *info)
{
	libspdm_return_t status;
	pci_tdisp_interface_id_t tdisp_id;
	uint8_t tdi_state;
	struct dev_assign_tdisp_params *tdisp_params = &info->dev_assign_op_params.tdisp_params;
	int ret = DEV_ASSIGN_STATUS_SUCCESS;

	assert(info->dev_assign_op_params.param_type == DEV_ASSIGN_OP_PARAMS_TDISP);

	(void)memset(&tdisp_id, 0, sizeof(pci_tdisp_interface_id_t));

	/* TDISP_STOP_INTERFACE_REQ */
	tdisp_id.function_id = tdisp_params->tdi_id;

	status = pci_tdisp_stop_interface(NULL, info->libspdm_ctx,
					  &info->session_id, &tdisp_id);
	if (status != LIBSPDM_STATUS_SUCCESS) {
		ERROR("%s: pci_tdisp_stop_interface failed. tdi_id = %u, status = 0x%x\n",
			__func__, tdisp_params->tdi_id, status);
		goto out_tdisp_disable;
	}

	/* TDISP_GET_DEVICE_INTERFACE_STATE after stop */
	status = pci_tdisp_get_interface_state(NULL,
					       info->libspdm_ctx,
					       &info->session_id, &tdisp_id,
					       &tdi_state);
	if (status != LIBSPDM_STATUS_SUCCESS) {
		ERROR("%s: pci_tdisp_get_interface_state failed. tdi_id = %u, status = 0x%x\n",
			__func__, tdisp_params->tdi_id, status);
		return DEV_ASSIGN_STATUS_ERROR;
	}

	/* coverity[uninit_use:SUPPRESS] */
	if (tdi_state != (uint8_t)PCI_TDISP_INTERFACE_STATE_CONFIG_UNLOCKED) {
		ERROR("%s: TDI: %u state is %d [not CONFIG_UNLOCKED]\n",
		      __func__, tdisp_id.function_id, tdi_state);
		ret = DEV_ASSIGN_STATUS_ERROR;
	}

	INFO("%s: TDI: 0x%x state is CONFIG_UNLOCKED\n", __func__, tdisp_id.function_id);

out_tdisp_disable:

	tdisp_params->nonce_is_output = false;

	INFO("%s: cmd_rc: 0x%x, tdi_id = %u\n", __func__, status, tdisp_params->tdi_id);
	return ret;
}
