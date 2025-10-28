/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <app_common.h>
#include <debug.h>
#include <dev_assign_private.h>
#include <dev_assign_structs.h>
#include <el0_app_helpers.h>
#include <library/pci_ide_km_requester_lib.h>
#include <library/spdm_crypt_lib.h>
#include <string.h>

/* SUB_STREAM_PR, SUB_STREAM_NPR, SUB_STREAM_CPL */
#define IDE_SUBSTREAM_MAX		((unsigned char)3)

static bool ide_init_key_buffer(pci_ide_km_aes_256_gcm_key_buffer_t *key_buffer)
{
	bool got_rand_number;

	(void)memset(key_buffer, 0, sizeof(pci_ide_km_aes_256_gcm_key_buffer_t));
	got_rand_number = libspdm_get_random_number(sizeof(key_buffer->key),
						    (void *)key_buffer->key);
	if (got_rand_number) {
		/* Initialization Vector (IV) */
		key_buffer->iv[0] = 0;
		key_buffer->iv[1] = 1;
	}

	return got_rand_number;
}

static int rmm_rp_ide_key_prog(struct dev_assign_info *info,
			       pci_ide_km_aes_256_gcm_key_buffer_t *key_buf,
			       uint8_t kslot, uint8_t sub_stream,
			       uint8_t key_direction)
{
	struct service_rp_ide_op_struct *service_params;
	bool is_rx;

	if (key_direction == U(PCI_IDE_KM_KEY_DIRECTION_RX)) {
		is_rx = true;
	} else {
		is_rx = false;
	}

	service_params = get_shared_mem_start();

	assert(sizeof(service_params->key) == sizeof(key_buf->key));
	(void)memcpy(service_params->key, key_buf->key, sizeof(service_params->key));
	assert(sizeof(service_params->iv) == sizeof(key_buf->iv));
	(void)memcpy(service_params->iv, key_buf->iv, sizeof(service_params->iv));

	service_params->ecam_addr = info->ecam_addr;
	service_params->rp_id = info->rp_id;
	service_params->ide_sid = info->ide_sid;

	return (int)el0_app_service_call(APP_SERVICE_RP_IDE_KEY_PROGRAM,
		kslot, (is_rx ? 1U : 0U), sub_stream, 0);
}

static int rmm_rp_ide_key_set_go(struct dev_assign_info *info, uint8_t kslot,
				 uint8_t sub_stream, uint8_t key_direction)
{
	struct service_rp_ide_op_struct *service_params;
	bool is_rx;

	if (key_direction == U(PCI_IDE_KM_KEY_DIRECTION_RX)) {
		is_rx = true;
	} else {
		is_rx = false;
	}

	service_params = get_shared_mem_start();

	service_params->ecam_addr = info->ecam_addr;
	service_params->rp_id = info->rp_id;
	service_params->ide_sid = info->ide_sid;

	return (int)el0_app_service_call(APP_SERVICE_RP_IDE_KEY_SET_GO,
		kslot, (is_rx ? 1U : 0U), sub_stream, 0);
}

static int rmm_rp_ide_key_set_stop(struct dev_assign_info *info, uint8_t sub_stream,
				   uint8_t key_direction)
{
	struct service_rp_ide_op_struct *service_params;
	bool is_rx;

	if (key_direction == U(PCI_IDE_KM_KEY_DIRECTION_RX)) {
		is_rx = true;
	} else {
		is_rx = false;
	}

	service_params = get_shared_mem_start();

	service_params->ecam_addr = info->ecam_addr;
	service_params->rp_id = info->rp_id;
	service_params->ide_sid = info->ide_sid;

	return (int)el0_app_service_call(APP_SERVICE_RP_IDE_KEY_SET_STOP,
		info->ide_kslot_cur, (is_rx ? 1U : 0U), sub_stream, 0);
}

static libspdm_return_t
ide_km_endpoint_rp_key_set_stop(struct dev_assign_info *info, uint8_t key_direction)
{
	libspdm_return_t status;
	uint8_t sub_stream;
	uint8_t port_index;
	uint8_t stream_id;

	stream_id = (uint8_t)info->ide_sid;

	/*
	 * TODO: Check whether using port_index 1 is necessary here, would 0
	 * do as well?
	 */
	port_index = 1;

	/* IDE_KM_KEY_SET_STOP: upstream port */
	INFO("IDE_KM_KEY_SET_STOP: Endpoint dir: %d id/sub_id: %d/[0-%d]\n",
		key_direction, stream_id, IDE_SUBSTREAM_MAX - 1U);
	for (sub_stream = 0; sub_stream < IDE_SUBSTREAM_MAX; sub_stream++) {
		uint8_t key_sub_stream;

		key_sub_stream = (info->ide_kslot_cur | key_direction |
				  (sub_stream << 4));

		status = pci_ide_km_key_set_stop(NULL,
						 info->libspdm_ctx,
						 &info->session_id, stream_id,
						 key_sub_stream, port_index);
		if (status != LIBSPDM_STATUS_SUCCESS) {
			ERROR("IDE_KM_KEY_SET_STOP Failed: Endpoint dir: %d id/sub_id: %d/%d\n",
				key_direction, stream_id, sub_stream);
			return status;
		}
	}

	/* EL3_IDE_KEY_SET_STOP to rootport */
	INFO("EL3_IDE_KEY_SET_STOP: rootport dir: %d id/sub_id: %d/[0-%d]\n",
		key_direction, stream_id, IDE_SUBSTREAM_MAX - 1U);
	for (sub_stream = 0; sub_stream < IDE_SUBSTREAM_MAX; sub_stream++) {
		int rc;

		rc = rmm_rp_ide_key_set_stop(info, sub_stream, key_direction);
		if (rc != 0) {
			ERROR("EL3_IDE_KEY_SET_STOP Failed: rootport dir: %d id/sub_id: %d/%d\n",
				key_direction, stream_id, sub_stream);
			return (libspdm_return_t)-1;
		}
	}

	return status;
}

static libspdm_return_t
ide_km_endpoint_rp_key_set_go(struct dev_assign_info *info, uint8_t kslot,
			      uint8_t key_direction)
{
	libspdm_return_t status;
	uint8_t sub_stream;
	uint8_t port_index;
	uint8_t stream_id;

	stream_id = (uint8_t)info->ide_sid;
	/*
	 * TODO: Check whether using port_index 1 is necessary here, would 0
	 * do as well?
	 */
	port_index = 1;

	/* IDE_KM_KEY_SET_GO: upstream port */
	INFO("IDE_KM_KEY_SET_GO: Endpoint dir: %d id/sub_id: %d/[0-%d]\n",
		key_direction, stream_id, IDE_SUBSTREAM_MAX - 1U);
	for (sub_stream = 0; sub_stream < IDE_SUBSTREAM_MAX; sub_stream++) {
		uint8_t key_sub_stream;

		key_sub_stream = (kslot | key_direction | (sub_stream << 4));

		status = pci_ide_km_key_set_go(NULL,
					       info->libspdm_ctx,
					       &info->session_id, stream_id,
					       key_sub_stream, port_index);
		if (status != LIBSPDM_STATUS_SUCCESS) {
			ERROR("IDE_KM_KEY_SET_GO Failed: Endpoint dir: %d id/sub_id: %d/%d\n",
				key_direction, stream_id, sub_stream);
			return status;
		}
	}

	/* EL3_IDE_KEY_SET_GO to rootport */
	INFO("EL3_IDE_KEY_SET_GO: rootport dir: %d id/sub_id: %d/[0-%d]\n",
		key_direction, stream_id, IDE_SUBSTREAM_MAX - 1U);
	for (sub_stream = 0; sub_stream < IDE_SUBSTREAM_MAX; sub_stream++) {
		int rc;

		rc = rmm_rp_ide_key_set_go(info, kslot, sub_stream,
					   key_direction);
		if (rc != 0) {
			ERROR("EL3_IDE_KEY_SET_GO Failed: rootport dir: %d id/sub_id: %d/%d\n",
			     key_direction, stream_id, sub_stream);
			return (libspdm_return_t)-1;
		}
	}

	return status;
}

static libspdm_return_t
ide_km_endpoint_rp_key_prog(struct dev_assign_info *info, uint8_t kslot)
{
	libspdm_return_t status;
	pci_ide_km_aes_256_gcm_key_buffer_t rx_key_buffer;
	pci_ide_km_aes_256_gcm_key_buffer_t tx_key_buffer;
	uint8_t sub_stream;
	uint8_t port_index;
	uint8_t kp_ack_status;
	uint8_t stream_id;
	bool result;

	/*
	 * TODO: Check whether using port_index 1 is necessary here, would 0
	 * do as well?
	 */
	port_index = 1;
	stream_id = (uint8_t)info->ide_sid;

	result = ide_init_key_buffer(&rx_key_buffer);
	if (!result) {
		return LIBSPDM_STATUS_LOW_ENTROPY;
	}

	result = ide_init_key_buffer(&tx_key_buffer);
	if (!result) {
		return LIBSPDM_STATUS_LOW_ENTROPY;
	}

	/* IDE_KM_KEY_PROG: upstream port RX/TX */
	INFO("IDE_KM_KEY_PROG: Endpoint RX/TX id/sub_id: %d/[0-%d]\n",
		stream_id, IDE_SUBSTREAM_MAX - 1U);
	for (sub_stream = 0; sub_stream < IDE_SUBSTREAM_MAX; sub_stream++) {
		status = pci_ide_km_key_prog(NULL, info->libspdm_ctx,
					     &info->session_id, stream_id,
					     (uint8_t)(kslot |
					      U(PCI_IDE_KM_KEY_DIRECTION_RX) |
					      (sub_stream << 4U)), port_index,
					     &rx_key_buffer, &kp_ack_status);
		if (status != LIBSPDM_STATUS_SUCCESS) {
			ERROR("IDE_KM_KEY_PROG Failed: Endpoint RX id/sub_id: %d/%d\n",
				stream_id, sub_stream);
			return status;
		}

		/* coverity[uninit_use:SUPPRESS] */
		if (kp_ack_status != U(PCI_IDE_KM_KP_ACK_STATUS_SUCCESS)) {
			ERROR("IDE_KM_KEY_PROG Ack failed: Endpoint RX id/sub_id: %d/%d\n",
				stream_id, sub_stream);
			return LIBSPDM_STATUS_INVALID_MSG_FIELD;
		}

		status = pci_ide_km_key_prog(NULL, info->libspdm_ctx,
					     &info->session_id, stream_id,
					     (uint8_t)(kslot |
					      U(PCI_IDE_KM_KEY_DIRECTION_TX) |
					      (sub_stream << 4U)), port_index,
					     &tx_key_buffer, &kp_ack_status);
		if (status != LIBSPDM_STATUS_SUCCESS) {
			ERROR("IDE_KM_KEY_PROG Failed: Endpoint TX id/sub_id: %d/%d\n",
			     stream_id, sub_stream);
			return status;
		}

		if (kp_ack_status != U(PCI_IDE_KM_KP_ACK_STATUS_SUCCESS)) {
			ERROR("IDE_KM_KEY_PROG Ack failed: Endpoint TX id/sub_id: %d/%d\n",
			     stream_id, sub_stream);
			return LIBSPDM_STATUS_INVALID_MSG_FIELD;
		}
	}

	/* EL3_IDE_KEY_PROG: program rootport RX/TX */
	INFO("EL3_IDE_KEY_PROG: Root Port RX/TX id/sub_id: %d/[0-%d]\n",
		stream_id, IDE_SUBSTREAM_MAX - 1U);
	for (sub_stream = 0; sub_stream < IDE_SUBSTREAM_MAX; sub_stream++) {
		int rc;

		rc = rmm_rp_ide_key_prog(info, &rx_key_buffer, kslot, sub_stream,
					 PCI_IDE_KM_KEY_DIRECTION_RX);
		if (rc != 0) {
			ERROR("EL3_IDE_KEY_PROG Failed: Root Port RX id/sub_id: %d/%d\n",
				stream_id, sub_stream);
			return (libspdm_return_t)-1;
		}

		rc = rmm_rp_ide_key_prog(info, &tx_key_buffer, kslot, sub_stream,
					 PCI_IDE_KM_KEY_DIRECTION_TX);
		if (rc != 0) {
			ERROR("EL3_IDE_KEY_PROG Failed: Root Port TX id/sub_id: %d/%d\n",
				stream_id, sub_stream);
			return (libspdm_return_t)-1;
		}
	}

	return status;
}

/* Key program and set_go Endpoint and Root Port */
static libspdm_return_t dev_assign_ide_refresh(struct dev_assign_info *info, uint8_t kslot)
{
	libspdm_return_t status;

	/* Step 1 & 2: Key program upstream port and root port */
	status = ide_km_endpoint_rp_key_prog(info, kslot);
	if (status != LIBSPDM_STATUS_SUCCESS) {
		goto krefresh_err_out;
	}

	/* Step 3 & 4: Trigger IDE at upstream port and root port for RX */
	status = ide_km_endpoint_rp_key_set_go(info, kslot,
					       PCI_IDE_KM_KEY_DIRECTION_RX);
	if (status != LIBSPDM_STATUS_SUCCESS) {
		goto krefresh_err_out;
	}

	/* Step 5 & 6: Trigger IDE at upstream port and root port for TX */
	status = ide_km_endpoint_rp_key_set_go(info, kslot,
					       PCI_IDE_KM_KEY_DIRECTION_TX);

	/* Update the in use key slot */
	if (status == LIBSPDM_STATUS_SUCCESS) {
		INFO("IDE Refresh: Current active key slot: %d\n", kslot);
		info->ide_kslot_cur = kslot;
	}

krefresh_err_out:
	return status;
}

/*
 * Start IDM Key programming both at Upsream port and at Root port. Programming
 * IDE keys to both Upsream port and at Root port is handled in one function.
 *
 * The sequence mentioned by PCI spec is
 * 1. Distribute keys to Upstream Port for each Sub-Stream & Rx/Tx
 * 2. Use internal interface to program keys to Root Port for each Sub-Stream
 *    & Rx/Tx
 * 3. Trigger IDE at Upstream Port for Rx for each Sub-Stream
 * 4. Use internal interface to trigger IDE at Root Port for Rx for each
 *    Sub-Stream
 * 5. Trigger IDE at Upstream Port for Tx for each Sub-Stream**
 * 6. Use internal interface to trigger IDE at Root Port for Tx for each
 *    Sub-Stream
 *
 * Programming the keys to Upstream port uses SSPDM/DOE communication by NS
 * host and programming the keys to Root Port uses EL3 interface. The Root Port
 * programming ABIs in EL3 is platform dependent and the communication to the
 * Root Port could be blocking or non-blocking.
 */
libspdm_return_t dev_assign_ide_setup(struct dev_assign_info *info)
{
	libspdm_return_t status;
	/* cppcheck-suppress misra-c2012-12.1 */
	uint32_t ide_reg_block[PCI_IDE_KM_IDE_REG_BLOCK_SUPPORTED_COUNT];
	uint32_t ide_reg_block_count;
	uint8_t dev_func_num;
	uint8_t bus_num;
	uint8_t segment;
	uint8_t max_port_index;
	int rc;

	rc = dvsec_init(info);
	if (rc != 0) {
		ERROR("IDE Setup: dvsec init failed\n");
		return (libspdm_return_t)-1;
	}

	rc = dvsec_stream_lock(info);
	if (rc != 0) {
		ERROR("IDE Setup: dvsec stream lock failed\n");
		return (libspdm_return_t)-1;
	}

	/*
	 * todo:
	 * 1. Read stream config from RP IDE Extended Capability registers
	 * 2. Check against dsm stream id
	 */

	/* Transmit IDE_KM_QUERY */
	/* cppcheck-suppress misra-c2012-12.1 */
	/* coverity[misra_c_2012_rule_12_1_violation:SUPPRESS] */
	ide_reg_block_count = PCI_IDE_KM_IDE_REG_BLOCK_SUPPORTED_COUNT;
	status = pci_ide_km_query(NULL, info->libspdm_ctx,
				  &info->session_id, 1, &dev_func_num,
				  &bus_num, &segment, &max_port_index,
				  ide_reg_block, &ide_reg_block_count);
	if (status != LIBSPDM_STATUS_SUCCESS) {
		goto out_set_cmd_rc;
	}

	/*
	 * todo:
	 * From IDE_KM_RESP, check EP capability matches with Extended Capability
	 */

	/* Step 1-6: Setup IDE in Endpoint and at RootPort using key slot 0 */
	status = dev_assign_ide_refresh(info, PCI_IDE_KM_KEY_SET_K0);

	/* Test DVSEC status */
	assert(dvsec_is_stream_locked(info));

out_set_cmd_rc:
	INFO("%s: ret: 0x%x\n", __func__, status);
	return status;
}

static libspdm_return_t update_teardown_status(libspdm_return_t old_status,
					       libspdm_return_t new_status)
{
	if (old_status == LIBSPDM_STATUS_SUCCESS) {
		return new_status;
	}
	return old_status;
}

/*
 * Teardown IDE Key programming both at Upstream port and at Root port.
 *
 * 1. Stop IDE at Upstream Port for Tx for each Sub-Stream
 * 2. Use internal interface to stop IDE at Root Port for Tx for each
 *    Sub-Stream
 * 3. Stop IDE at Upstream Port for Rx for each Sub-Stream
 * 4. Use internal interface to stop IDE at Root Port for Rx for each
 *    Sub-Stream
 */
libspdm_return_t dev_assing_ide_teardown(struct dev_assign_info *info)
{
	int rc;
	libspdm_return_t status;
	libspdm_return_t next_status;

	/* Step 1 & 2: Stop IDE at upstream port and root port for TX */
	status = ide_km_endpoint_rp_key_set_stop(info,
						 PCI_IDE_KM_KEY_DIRECTION_TX);
	if (status != LIBSPDM_STATUS_SUCCESS) {
		ERROR("IDE Teardown: Setting stop for TX failed, status=0x%x\n", status);
		/* Do not return, attempt to continue teardown */
	}

	/* Step 3 & 4: Stop IDE at upstream port and root port for RX */
	next_status = ide_km_endpoint_rp_key_set_stop(info,
						 PCI_IDE_KM_KEY_DIRECTION_RX);
	if (next_status != LIBSPDM_STATUS_SUCCESS) {
		ERROR("IDE Teardown: Setting stop for RX failed, status=0x%x\n", next_status);
		/* Do not return, attempt to continue teardown */
	}
	status = update_teardown_status(status, next_status);

	/* DVSEC unlock stream */
	rc = dvsec_stream_unlock(info);
	if (rc != 0) {
		ERROR("IDE Teardown: dvsec unlock failed\n");
		status = update_teardown_status(status, (libspdm_return_t)-1);
		/* Do not return, attempt to continue teardown */
	}

	/* DVSEC deinit */
	rc = dvsec_deinit(info);
	if (rc != 0) {
		ERROR("IDE Teardown: dvsec deinit failed\n");
		status = update_teardown_status(status, (libspdm_return_t)-1);
	}

	INFO("%s: ret: 0x%x\n", __func__, status);
	return status;
}

/*
 * Refresh IDM Key programming both at Upstream port and at Root port using the
 * next key slot.
 *
 * 1. Transmit IDE_KM QUERY
 * 2. Receive IDE_KM QUERY_RESP
 * 3. Check EP IDE stream is in Secure state, Enabled and is using dsm->kslot_cur
 * 4. Read the Root port IDE capabilities in config space and ensure that IDE
 *    Stream is in Secure state and enabled.
 * 5. Ensure that the stream is still locked (RMEDA_CTL2.SEL_STR_LOCK==1)
 * 6. Switch the keyslot and call refresh to EP and RP
 */
int dev_assign_ide_refresh_main(struct dev_assign_info *info)
{
	libspdm_return_t status;
	uint8_t kslot_next;

	if (!info->has_ide) {
		return DEV_ASSIGN_STATUS_ERROR;
	}

	/*
	 * todo:
	 * Step 1 to 4
	 */

	/* Step 5: Ensure that the stream is still locked */
	if (!dvsec_is_stream_locked(info)) {
		ERROR("IDE Refresh: dvsec stream not locked\n");
		return DEV_ASSIGN_STATUS_ERROR;
	}

	/* 6. Switch the keyslot and call refresh to EP and RP */
	if (info->ide_kslot_cur == U(PCI_IDE_KM_KEY_SET_K0)) {
		kslot_next = PCI_IDE_KM_KEY_SET_K1;
	} else {
		kslot_next = PCI_IDE_KM_KEY_SET_K0;
	}

	status = dev_assign_ide_refresh(info, kslot_next);
	INFO("%s: ret: 0x%x\n", __func__, status);
	if (status != LIBSPDM_STATUS_SUCCESS) {
		return DEV_ASSIGN_STATUS_ERROR;
	}

	return DEV_ASSIGN_STATUS_SUCCESS;
}

/* Reset IDE link at Endpoint and at RootPort and reset DVSEC */
int dev_assign_ide_reset_main(struct dev_assign_info *info)
{
	__unused libspdm_return_t status;
	int ret = DEV_ASSIGN_STATUS_SUCCESS;

	if (!info->has_ide) {
		return DEV_ASSIGN_STATUS_ERROR;
	}

	status = dev_assing_ide_teardown(info);
	if (status == LIBSPDM_STATUS_SUCCESS) {
		status = dev_assign_ide_setup(info);
	}

	INFO("%s: ret: 0x%x\n", __func__, status);
	return ret;
}
