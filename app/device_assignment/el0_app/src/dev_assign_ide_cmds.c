/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <debug.h>
#include <dev_assign_private.h>
#include <dev_assign_structs.h>
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

	/* todo: EL3_IDE_KEY_SET_STOP: rootport port */
	INFO("EL3_IDE_KEY_SET_STOP: rootport dir: %d id/sub_id: %d/[0-%d]\n",
		key_direction, stream_id, IDE_SUBSTREAM_MAX - 1U);
	for (sub_stream = 0; sub_stream < IDE_SUBSTREAM_MAX; sub_stream++) {
		/* TODO: Call IDE key stop */
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

	/* todo: EL3_IDE_KEY_SET_GO: rootport port */
	INFO("EL3_IDE_KEY_SET_GO: rootport dir: %d id/sub_id: %d/[0-%d]\n",
		key_direction, stream_id, IDE_SUBSTREAM_MAX - 1U);
	for (sub_stream = 0; sub_stream < IDE_SUBSTREAM_MAX; sub_stream++) {
		/* TODO: Call IDE key set go */
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

	/* todo: EL3_IDE_KEY_PROG: rootport port RX/TX */
	INFO("EL3_IDE_KEY_PROG: Root Port RX/TX id/sub_id: %d/[0-%d]\n",
		stream_id, IDE_SUBSTREAM_MAX - 1U);
	for (sub_stream = 0; sub_stream < IDE_SUBSTREAM_MAX; sub_stream++) {
		/* TODO: Call Ide key prog for RX and TX */
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
		INFO("DSM: IDE: Current active key slot: %d\n", kslot);
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

	/* todo: DVSEC programming */

	/* pci_ide_km_query */
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

	/* Setup IDE in Endpoint and at RootPort using key slot 0 */
	status = dev_assign_ide_refresh(info, PCI_IDE_KM_KEY_SET_K0);

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
	libspdm_return_t status;
	libspdm_return_t next_status;

	/* Step 1 & 2: Stop IDE at upstream port and root port for TX */
	status = ide_km_endpoint_rp_key_set_stop(info,
						 PCI_IDE_KM_KEY_DIRECTION_TX);
	if (status != LIBSPDM_STATUS_SUCCESS) {
		ERROR("DSM: IDE_teardown: Setting stop for TX failed, status=0x%x\n", status);
		/* Do not return, attempt to continue teardown */
	}

	/* Step 3 & 4: Stop IDE at upstream port and root port for RX */
	next_status = ide_km_endpoint_rp_key_set_stop(info,
						 PCI_IDE_KM_KEY_DIRECTION_RX);
	if (next_status != LIBSPDM_STATUS_SUCCESS) {
		ERROR("DSM: IDE_teardown: Setting stop for RX failed, status=0x%x\n", next_status);
		/* Do not return, attempt to continue teardown */
	}
	status = update_teardown_status(status, next_status);

	INFO("%s: ret: 0x%x\n", __func__, status);
	return status;
}

/*
 * Refresh IDM Key programming both at Upstream port and at Root port using the
 * next key slot.
 */
int dev_assign_ide_refresh_main(struct dev_assign_info *info)
{
	libspdm_return_t status;
	uint8_t kslot_next;

	if (!info->has_ide) {
		return DEV_ASSIGN_STATUS_ERROR;
	}

	/* todo: Check DVSEC for IDE still in secure state and locked */

	/* todo: Query IDE KM and check key slot in use matches with DSM state */

	if (info->ide_kslot_cur == U(PCI_IDE_KM_KEY_SET_K0)) {
		kslot_next = PCI_IDE_KM_KEY_SET_K1;
	} else {
		kslot_next = PCI_IDE_KM_KEY_SET_K0;
	}

	/* Setup IDE in Endpoint and at RootPort using next key slot */
	status = dev_assign_ide_refresh(info, kslot_next);
	INFO("%s: ret: 0x%x\n", __func__, status);
	if (status != LIBSPDM_STATUS_SUCCESS) {
		return DEV_ASSIGN_STATUS_ERROR;
	}

	return DEV_ASSIGN_STATUS_SUCCESS;
}

/*
 * Reset IDE link at Endpoint and at RootPort.
 * 1. IDE KEY_SET_STOP
 * 2. Using key slot 0 do KEY_PROG and KEY_SET_GO
 */
int dev_assign_ide_reset_main(struct dev_assign_info *info)
{
	__unused libspdm_return_t status;
	int ret = DEV_ASSIGN_STATUS_SUCCESS;

	if (!info->has_ide) {
		return DEV_ASSIGN_STATUS_ERROR;
	}

	/* todo: DVSEC re-programming? */

	/*  IDE KEY_SET_STOP at Endpoint and at RootPort */
	status = dev_assing_ide_teardown(info);
	if (status != LIBSPDM_STATUS_SUCCESS) {
		ERROR("DSM_IDE_RESET: KEY_SET_STOP failed\n");
		ret = DEV_ASSIGN_STATUS_ERROR;
		goto out_err_ide_reset;
	}

	/* Setup IDE in Endpoint and at RootPort using key slot 0 */
	status = dsm_spdm_vdm_ide_refresh(info, PCI_IDE_KM_KEY_SET_K0);
	if (status != LIBSPDM_STATUS_SUCCESS) {
		ERROR("DSM_IDE_RESET: KEY_PROG and KEY_SET_GO failed\n");
		ret = DEV_ASSIGN_STATUS_ERROR;
	}

out_err_ide_reset:
	INFO("%s: ret: 0x%x\n", __func__, status);
	return ret;
}
