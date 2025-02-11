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
	uint8_t tdi_state;

	(void)memset(&tdisp_id, 0, sizeof(pci_tdisp_interface_id_t));

	tdisp_id.function_id = info->tdisp_params.tdi_id;

	/* TDISP_GET_VERSION */
	status = pci_tdisp_get_version(NULL, info->libspdm_ctx,
				       &info->session_id, &tdisp_id);
	if (status != LIBSPDM_STATUS_SUCCESS) {
		ERROR("%s: pci_tdisp_get_version failed. tdi_id = %u, status = 0x%x\n",
			__func__, info->tdisp_params.tdi_id, status);
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
			__func__, info->tdisp_params.tdi_id, status);
		return DEV_ASSIGN_STATUS_ERROR;
	}

	/* TDISP_GET_DEVICE_INTERFACE_STATE */
	status = pci_tdisp_get_interface_state(NULL,
					       info->libspdm_ctx,
					       &info->session_id, &tdisp_id,
					       &tdi_state);
	if (status != LIBSPDM_STATUS_SUCCESS) {
		ERROR("%s: pci_tdisp_get_interface_state failed. tdi_id = %u, status = 0x%x\n",
			__func__, info->tdisp_params.tdi_id, status);
		return DEV_ASSIGN_STATUS_ERROR;
	}

	/* coverity[uninit_use:SUPPRESS] */
	if (tdi_state != (uint8_t)PCI_TDISP_INTERFACE_STATE_CONFIG_UNLOCKED) {
		ERROR("%s: tdi_id %u not in TDSIP unlocked state\n",
			__func__, info->tdisp_params.tdi_id);
		return DEV_ASSIGN_STATUS_ERROR;
	}

	/* TDISP_LOCK_INTERFACE_REQ */
	(void)memset(&lock_param, 0, sizeof(pci_tdisp_lock_interface_param_t));

	/* TODO: Derive parameters according to current platform */
	/* coverity[uninit_use:SUPPRESS] */
	lock_param.flags = rsp_caps.lock_interface_flags_supported;
	lock_param.default_stream_id = 0;
	lock_param.mmio_reporting_offset = 0xD0000000;

	assert(info->tdisp_params.nonce_ptr_is_valid);
	status = pci_tdisp_lock_interface(NULL, info->libspdm_ctx,
					  &info->session_id, &tdisp_id,
					  &lock_param,
					  info->tdisp_params.start_interface_nonce_buffer);
	if (status != LIBSPDM_STATUS_SUCCESS) {
		ERROR("%s: pci_tdisp_lock_interface failed. tdi_id = %u, status = 0x%x\n",
			__func__, info->tdisp_params.tdi_id, status);
		return DEV_ASSIGN_STATUS_ERROR;
	}

	info->tdisp_params.nonce_is_output = true;

	/* TDISP_GET_DEVICE_INTERFACE_STATE after lock */
	status = pci_tdisp_get_interface_state(NULL,
					       info->libspdm_ctx,
					       &info->session_id, &tdisp_id,
					       &tdi_state);
	if (status != LIBSPDM_STATUS_SUCCESS) {
		ERROR("%s: pci_tdisp_get_interface_state failed. tdi_id = %u, status = 0x%x\n",
			__func__, info->tdisp_params.tdi_id, status);
		return DEV_ASSIGN_STATUS_ERROR;
	}

	if (tdi_state != (uint8_t)PCI_TDISP_INTERFACE_STATE_CONFIG_LOCKED) {
		ERROR("%s: TDI not in LOCKED state. tdi_id = %u\n",
			__func__, info->tdisp_params.tdi_id);
		return DEV_ASSIGN_STATUS_ERROR;
	}

	INFO("TDISP lock successful, tdi_id = %u\n", info->tdisp_params.tdi_id);

	return DEV_ASSIGN_STATUS_SUCCESS;
}

int dev_tdisp_report_main(struct dev_assign_info *info)
{
	libspdm_return_t status;
	pci_tdisp_interface_id_t tdisp_id;
	uint32_t ifc_report_size;

	(void)memset(&tdisp_id, 0, sizeof(pci_tdisp_interface_id_t));

	/* PCI_TDISP_GET_DEVICE_INTERFACE_REPORT */
	tdisp_id.function_id = info->tdisp_params.tdi_id;

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
			__func__, info->tdisp_params.tdi_id, status);
		return DEV_ASSIGN_STATUS_ERROR;
	}

	info->tdisp_params.nonce_is_output = false;

	INFO("TDISP report successful, tdi_id = %u\n", info->tdisp_params.tdi_id);

	return DEV_ASSIGN_STATUS_SUCCESS;
}

int dev_tdisp_start_main(struct dev_assign_info *info)
{
	libspdm_return_t status;
	pci_tdisp_interface_id_t tdisp_id;
	uint8_t tdi_state;

	(void)memset(&tdisp_id, 0, sizeof(pci_tdisp_interface_id_t));

	/* TDISP_START_INTERFACE_REQ */
	tdisp_id.function_id = info->tdisp_params.tdi_id;

	assert(info->tdisp_params.nonce_ptr_is_valid);

#ifndef NDEBUG
	status = pci_tdisp_get_interface_state(NULL,
					       info->libspdm_ctx,
					       &info->session_id, &tdisp_id,
					       &tdi_state);
	if (status != LIBSPDM_STATUS_SUCCESS) {
		ERROR("%s: pci_tdisp_get_interface_state failed. tdi_id = %u, status = 0x%x\n",
			__func__, info->tdisp_params.tdi_id, status);
		return DEV_ASSIGN_STATUS_ERROR;
	}

	/* coverity[uninit_use:SUPPRESS] */
	assert(tdi_state == (uint8_t)PCI_TDISP_INTERFACE_STATE_CONFIG_LOCKED);
#endif

	status = pci_tdisp_start_interface(NULL, info->libspdm_ctx,
					   &info->session_id, &tdisp_id,
					   info->tdisp_params.start_interface_nonce_buffer);
	if (status != LIBSPDM_STATUS_SUCCESS) {
		ERROR("%s: pci_tdisp_start_interface failed. tdi_id = %u, status = 0x%x\n",
			__func__, info->tdisp_params.tdi_id, status);
		return DEV_ASSIGN_STATUS_ERROR;
	}

	info->tdisp_params.nonce_is_output = false;

	/* TDISP_GET_DEVICE_INTERFACE_STATE after start */
	status = pci_tdisp_get_interface_state(NULL,
					       info->libspdm_ctx,
					       &info->session_id, &tdisp_id,
					       &tdi_state);
	if (status != LIBSPDM_STATUS_SUCCESS) {
		ERROR("%s: pci_tdisp_get_interface_state failed. tdi_id = %u, status = 0x%x\n",
			__func__, info->tdisp_params.tdi_id, status);
		return DEV_ASSIGN_STATUS_ERROR;
	}

	if (tdi_state != (uint8_t)PCI_TDISP_INTERFACE_STATE_RUN) {
		ERROR("%s: TDI not in RUN state. tdi_id = %u\n",
			__func__, info->tdisp_params.tdi_id);
		return DEV_ASSIGN_STATUS_ERROR;
	}

	INFO("TDISP start successful, tdi_id = %u\n", info->tdisp_params.tdi_id);

	return DEV_ASSIGN_STATUS_SUCCESS;
}

int dev_tdisp_stop_main(struct dev_assign_info *info)
{
	libspdm_return_t status;
	pci_tdisp_interface_id_t tdisp_id;
	uint8_t tdi_state;

	(void)memset(&tdisp_id, 0, sizeof(pci_tdisp_interface_id_t));

	/* TDISP_STOP_INTERFACE_REQ */
	tdisp_id.function_id = info->tdisp_params.tdi_id;

	status = pci_tdisp_stop_interface(NULL, info->libspdm_ctx,
					  &info->session_id, &tdisp_id);
	if (status != LIBSPDM_STATUS_SUCCESS) {
		ERROR("%s: pci_tdisp_stop_interface failed. tdi_id = %u, status = 0x%x\n",
			__func__, info->tdisp_params.tdi_id, status);
		return DEV_ASSIGN_STATUS_ERROR;
	}

	/* TDISP_GET_DEVICE_INTERFACE_STATE after stop */
	status = pci_tdisp_get_interface_state(NULL,
					       info->libspdm_ctx,
					       &info->session_id, &tdisp_id,
					       &tdi_state);
	if (status != LIBSPDM_STATUS_SUCCESS) {
		ERROR("%s: pci_tdisp_get_interface_state failed. tdi_id = %u, status = 0x%x\n",
			__func__, info->tdisp_params.tdi_id, status);
		return DEV_ASSIGN_STATUS_ERROR;
	}

	info->tdisp_params.nonce_is_output = false;

	/* coverity[uninit_use:SUPPRESS] */
	if (tdi_state != (uint8_t)PCI_TDISP_INTERFACE_STATE_CONFIG_UNLOCKED) {
		ERROR("%s: DSM: TDISP: tdi_id = %u state is %d [not CONFIG_UNLOCKED]\n",
		      __func__, info->tdisp_params.tdi_id, tdi_state);
		return DEV_ASSIGN_STATUS_ERROR;
	}

	INFO("TDISP stop successful, tdi_id = %u\n", info->tdisp_params.tdi_id);

	return DEV_ASSIGN_STATUS_SUCCESS;
}
