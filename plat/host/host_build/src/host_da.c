/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch_helpers.h>
#include <assert.h>
#include <debug.h>
#include <host_crypto_utils.h>
#include <host_realm.h>
#include <host_rmi_wrappers.h>
#include <host_spdm_rsp_ifc.h>
#include <host_utils.h>
#include <host_utils_pci.h>
#include <platform_api.h>
#include <rmm_el3_ifc.h>
#include <smc-rmi.h>
#include <stdlib.h>
#include <string.h>

#define IS_RMI_RESULT_SUCCESS(_r)	((_r).x[0] == RMI_SUCCESS)

/* SPDM_MAX_CERTIFICATE_CHAIN_SIZE is 64KB */
#define HOST_PDEV_CERT_LEN_MAX		(64U * 1024U)

/* A single page for storing VCA should be enough */
#define HOST_PDEV_VCA_LEN_MAX		(4U * 1024U)
#define HOST_VDEV_MEAS_LEN_MAX		(4U * 1024U)

#define HOST_VDEV_IFC_REPORT_LEN_MAX	(8U * 1024U)

struct host_pdev {
	/* PDEV related fields */
	void *pdev_ptr;

	/* PDEV id. SPDM responder_emu ID */
	unsigned long pdev_id;
	unsigned long pdev_flags;
	void *pdev_aux[PDEV_PARAM_AUX_GRANULES_MAX];
	uint32_t pdev_aux_num;
	struct rmi_dev_comm_data *dev_comm_data;

	/* Algorithm used to generate device digests */
	uint8_t hash_algo;

	/* Certificate, public key fields */
	uint8_t cert_slot_id;
	uint8_t *cert_chain;
	size_t cert_chain_len;
	uint8_t *vca;
	size_t vca_len;
	void *public_key;
	size_t public_key_len;
	void *public_key_metadata;
	size_t public_key_metadata_len;
	unsigned char public_key_sig_algo;

	/* Root Port ID and ECAM_SPACE */
	uint16_t root_id;
	unsigned long ecam_addr;
};

struct host_vdev {
	void *vdev_ptr;
	void *pdev_ptr;

	/*
	 * NS host assigns the vdev_id, and this same id is used by Realm when
	 * it enumerates the PCI devices
	 */
	unsigned long vdev_id;

	/*
	 * The TEE device interface ID. Currently NS host assigns the whole
	 * device, this value is same as PDEV's ID (bdf).
	 */
	unsigned long tdi_id;

	unsigned long flags;

	void *vdev_aux[VDEV_PARAM_AUX_GRANULES_MAX];
	uint32_t vdev_aux_num;

	struct rmi_dev_comm_data *dev_comm_data;

	/* Fields related to cached device measurements. */
	uint8_t *meas;
	size_t meas_len;

	/* Fields related to cached interface report. */
	uint8_t *ifc_report;
	size_t ifc_report_len;
};

static struct host_pdev gbl_host_pdev;
static struct host_vdev gbl_host_vdev;

void *allocate_granule(void);

static void host_pdev_cleanup(struct host_pdev *dev)
{
	if (dev->pdev_id != 0UL) {
		(void)host_spdm_rsp_deinit((int)dev->pdev_id);
		dev->pdev_id = 0UL;
	}

	free(dev->cert_chain);
	dev->cert_chain = NULL;
	dev->cert_chain_len = 0;

	free(dev->vca);
	dev->vca = NULL;
	dev->vca_len = 0;
	struct smc_result result;
	uint32_t i;

	if (dev->pdev_ptr != NULL) {
		host_rmi_granule_undelegate(dev->pdev_ptr, &result);
		dev->pdev_ptr = NULL;
	}

	for (i = 0; i < dev->pdev_aux_num; i++) {
		if (dev->pdev_aux[i] != NULL) {
			host_rmi_granule_undelegate(dev->pdev_aux[i], &result);
			dev->pdev_aux[i] = NULL;
		}
	}
	dev->pdev_aux_num = 0;
}

static void host_vdev_cleanup(struct host_vdev *dev)
{
	struct smc_result result;

	free(dev->meas);
	dev->meas = NULL;
	dev->meas_len = 0;

	free(dev->ifc_report);
	dev->ifc_report = NULL;
	dev->ifc_report_len = 0;

	if (dev->vdev_ptr != NULL) {
		host_rmi_granule_undelegate(dev->vdev_ptr, &result);
		dev->vdev_ptr = NULL;
	}
	dev->dev_comm_data = NULL;
}

static const char *const pdev_state_str[] = {
	"PDEV_STATE_NEW",
	"PDEV_STATE_NEEDS_KEY",
	"PDEV_STATE_HAS_KEY",
	"PDEV_STATE_READY",
	"PDEV_STATE_IDE_RESETTING",
	"PDEV_STATE_COMMUNICATING",
	"PDEV_STATE_STOPPING",
	"PDEV_STATE_STOPPED",
	"RMI_PDEV_STATE_ERROR"
};

#define PDEV_STATE_STR_COUNT	(ARRAY_SIZE(pdev_state_str))

static const char *get_pdev_state_str(unsigned char state)
{
	if (state < PDEV_STATE_STR_COUNT) {
		return pdev_state_str[state];
	}
	return "UNKNOWN_STATE";
}

static int host_pdev_get_state(struct host_pdev *dev, unsigned char *state)
{
	struct smc_result result;

	host_rmi_pdev_get_state(dev->pdev_ptr, &result);
	if (result.x[0] != RMI_SUCCESS) {
		return -1;
	}

	*state = (unsigned char)result.x[1];

	return 0;
}

static bool is_host_pdev_state(struct host_pdev *dev, unsigned char exp_state)
{
	unsigned char cur_state;

	if (host_pdev_get_state(dev, &cur_state) != 0) {
		return false;
	}

	if (cur_state != exp_state) {
		return false;
	}

	return true;
}

static struct host_pdev *get_host_pdev_from_ptr(void *pdev_ptr)
{
	if (gbl_host_pdev.pdev_ptr == pdev_ptr) {
		return &gbl_host_pdev;
	}

	return NULL;
}

static struct host_vdev *get_host_vdev_from_ptr(void *vdev_ptr)
{
	if (gbl_host_vdev.vdev_ptr == vdev_ptr) {
		return &gbl_host_vdev;
	}

	return NULL;
}

static void *host_find_vdev_from_id(unsigned long vdev_id)
{
	struct host_vdev *h_vdev;

	h_vdev = &gbl_host_vdev;
	if (h_vdev->vdev_id == vdev_id) {
		return h_vdev->vdev_ptr;
	}

	return NULL;
}

static void *host_find_pdev_from_vdev(void *vdev_ptr)
{
	struct host_vdev *h_vdev;

	h_vdev = &gbl_host_vdev;
	if (h_vdev->vdev_ptr == vdev_ptr) {
		return h_vdev->pdev_ptr;
	}

	return NULL;
}

static int host_vdev_get_state(struct host_vdev *h_vdev, unsigned char *state)
{
	struct smc_result result;

	host_rmi_vdev_get_state(h_vdev->vdev_ptr, &result);
	if (result.x[0] != RMI_SUCCESS) {
		return -1;
	}

	*state = (unsigned char)result.x[1];

	return 0;
}

static int host_pdev_create(struct host_pdev *dev)
{
	struct rmi_pdev_params *pdev_params;
	struct smc_result result;
	uint32_t i;

	pdev_params = allocate_granule();
	memset(pdev_params, 0, GRANULE_SIZE);

	pdev_params->flags = dev->pdev_flags;
	pdev_params->cert_id = dev->cert_slot_id;
	pdev_params->pdev_id = dev->pdev_id;
	pdev_params->num_aux = dev->pdev_aux_num;
	pdev_params->hash_algo = dev->hash_algo;
	pdev_params->root_id = dev->root_id;
	pdev_params->ecam_addr = dev->ecam_addr;
	for (i = 0; i < dev->pdev_aux_num; i++) {
		pdev_params->aux[i] = (uintptr_t)dev->pdev_aux[i];
	}

	host_rmi_pdev_create(dev->pdev_ptr, pdev_params, &result);
	if (!IS_RMI_RESULT_SUCCESS(result)) {
		return -1;
	}

	return 0;
}

static int host_pdev_set_key(struct host_pdev *dev)
{
	struct rmi_public_key_params *pubkey_params;
	struct smc_result result;

	pubkey_params = allocate_granule();
	memset(pubkey_params, 0, GRANULE_SIZE);

	memcpy(pubkey_params->key, dev->public_key, dev->public_key_len);
	memcpy(pubkey_params->metadata,
	       dev->public_key_metadata,
	       dev->public_key_metadata_len);
	pubkey_params->key_len = dev->public_key_len;
	pubkey_params->metadata_len = dev->public_key_metadata_len;
	pubkey_params->algo = dev->public_key_sig_algo;

	host_rmi_pdev_set_pubkey(dev->pdev_ptr, pubkey_params, &result);
	if (!IS_RMI_RESULT_SUCCESS(result)) {
		return -1;
	}

	return 0;
}

static int host_pdev_stop(struct host_pdev *dev)
{
	struct smc_result result;

	host_rmi_pdev_stop(dev->pdev_ptr, &result);
	if (!IS_RMI_RESULT_SUCCESS(result)) {
		return -1;
	}

	return 0;
}

static int host_pdev_destroy(struct host_pdev *dev)
{
	struct smc_result result;

	host_rmi_pdev_destroy(dev->pdev_ptr, &result);
	if (!IS_RMI_RESULT_SUCCESS(result)) {
		return -1;
	}

	return 0;
}

static int host_pdev_ide_key_refresh(struct host_pdev *dev, unsigned int ev)
{
	struct smc_result result;

	host_rmi_pdev_ide_key_refresh(dev->pdev_ptr, ev, &result);
	if (!IS_RMI_RESULT_SUCCESS(result)) {
		return -1;
	}

	return 0;
}

static int host_pdev_ide_reset(struct host_pdev *dev)
{
	struct smc_result result;

	host_rmi_pdev_ide_reset(dev->pdev_ptr, &result);
	if (!IS_RMI_RESULT_SUCCESS(result)) {
		return -1;
	}

	return 0;
}

static int host_dev_get_state(struct host_pdev *h_pdev,
			      struct host_vdev *h_vdev,
			      unsigned char *state)
{
	if (h_vdev) {
		return host_vdev_get_state(h_vdev, state);
	} else {
		return host_pdev_get_state(h_pdev, state);
	}
}

static unsigned long host_rmi_dev_communicate(struct host_realm *realm,
					      struct host_pdev *h_pdev,
					      struct host_vdev *h_vdev)
{
	struct smc_result result;

	if (h_vdev) {
		assert(realm != NULL);
		host_rmi_vdev_communicate(realm->rd,
					  h_vdev->pdev_ptr,
					  h_vdev->vdev_ptr,
					  h_vdev->dev_comm_data,
					  &result);
	} else {
		host_rmi_pdev_communicate(h_pdev->pdev_ptr,
					  h_pdev->dev_comm_data,
					  &result);
	}

	return result.x[0];
}

static int host_pdev_cache_device_object(struct host_pdev *h_pdev,
					 uint8_t dev_obj_id,
					 const uint8_t *dev_obj_buf,
					 unsigned long dev_obj_buf_len)
{
	int rc = -1;

	/*
	 * During PDEV communicate device object of type certificate or VCA is
	 * cached
	 */
	if (dev_obj_id == RMI_DEV_COMM_OBJECT_CERTIFICATE) {
		if ((h_pdev->cert_chain_len + dev_obj_buf_len) >
		    (size_t)HOST_PDEV_CERT_LEN_MAX) {
			return -1;
		}

		INFO("%s: cache_cert: offset: 0x%lx, len: 0x%lx\n",
		     __func__,
		     h_pdev->cert_chain_len,
		     dev_obj_buf_len);

		memcpy((void *)(h_pdev->cert_chain + h_pdev->cert_chain_len),
		       dev_obj_buf,
		       dev_obj_buf_len);
		h_pdev->cert_chain_len += dev_obj_buf_len;
		rc = 0;
	} else if (dev_obj_id == RMI_DEV_COMM_OBJECT_VCA) {
		if ((h_pdev->vca_len + dev_obj_buf_len) >
		    (size_t)HOST_PDEV_VCA_LEN_MAX) {
			return -1;
		}

		INFO("%s: vca: offset: 0x%lx, len: 0x%lx\n",
		     __func__,
		     h_pdev->vca_len,
		     dev_obj_buf_len);

		memcpy((void *)(h_pdev->vca + h_pdev->vca_len),
		       dev_obj_buf,
		       dev_obj_buf_len);
		h_pdev->vca_len += dev_obj_buf_len;
		rc = 0;
	}

	return rc;
}

static int host_vdev_cache_device_object(struct host_vdev *h_vdev,
					 uint8_t dev_obj_id,
					 const uint8_t *dev_obj_buf,
					 unsigned long dev_obj_buf_len)
{
	(void)h_vdev;
	(void)dev_obj_id;
	(void)dev_obj_buf;
	(void)dev_obj_buf_len;
	return -1;
}

static int host_dev_cache_device_object(struct host_pdev *h_pdev,
					struct host_vdev *h_vdev,
					uint8_t *dev_obj_buf,
					unsigned char cache_obj_id,
					size_t cache_offset,
					size_t cache_len)
{
	int rc;

	if ((cache_len == 0) ||
	    ((cache_offset + cache_len) > GRANULE_SIZE)) {
		INFO("Invalid cache offset/length\n");
		return -1;
	}

	dev_obj_buf = dev_obj_buf + cache_offset;

	if (h_vdev) {
		rc = host_vdev_cache_device_object(h_vdev,
						   cache_obj_id,
						   dev_obj_buf,
						   cache_len);
	} else {
		rc = host_pdev_cache_device_object(h_pdev,
						   cache_obj_id,
						   dev_obj_buf,
						   cache_len);
	}

	if (rc != 0) {
		INFO("%s: failed\n", __func__);
	}

	return rc;
}

static int host_dev_cache_dev_req_resp(struct host_pdev *h_pdev,
				       struct host_vdev *h_vdev,
				       struct rmi_dev_comm_enter *dcomm_enter,
				       struct rmi_dev_comm_exit *dcomm_exit)
{
	int rc;

	rc = 0;

	if ((dcomm_exit->flags & RMI_DEV_COMM_EXIT_FLAGS_REQ_CACHE_BIT) != 0U) {
		rc = host_dev_cache_device_object(h_pdev,
						  h_vdev,
						  (uint8_t *)dcomm_enter->req_addr,
						  dcomm_exit->cache_obj_id,
						  dcomm_exit->cache_req_offset,
						  dcomm_exit->cache_req_len);
		if (rc != 0) {
			INFO("host_dev_cache_device_object REQ failed\n");
			return -1;
		}
	}

	if ((dcomm_exit->flags & RMI_DEV_COMM_EXIT_FLAGS_RSP_CACHE_BIT) != 0U) {
		rc = host_dev_cache_device_object(h_pdev,
						  h_vdev,
						  (uint8_t *)dcomm_enter->resp_addr,
						  dcomm_exit->cache_obj_id,
						  dcomm_exit->cache_rsp_offset,
						  dcomm_exit->cache_rsp_len);
		if (rc != 0) {
			INFO("host_dev_cache_device_object RSP failed\n");
			return -1;
		}
	}

	return rc;
}

static int host_pdev_spdm_rsp_communicate(struct host_pdev *h_pdev,
					  struct rmi_dev_comm_enter *dcomm_enter,
					  struct rmi_dev_comm_exit *dcomm_exit)
{
	bool is_sspdm;
	size_t resp_len;
	int rc;

	/* todo: validate DevCommExit flags */
	if (dcomm_exit->protocol == RMI_DEV_COMM_PROTOCOL_SPDM) {
		is_sspdm = false;
	} else if (dcomm_exit->protocol == RMI_DEV_COMM_PROTOCOL_SECURE_SPDM) {
		is_sspdm = true;
	} else {
		INFO("Invalid dev_comm_exit.protocol\n");
		return -1;
	}

	resp_len = 0UL;
	assert(h_pdev->pdev_id <= INT32_MAX);
	rc = host_spdm_rsp_communicate((int)h_pdev->pdev_id,
				       (void *)dcomm_enter->req_addr,
				       dcomm_exit->req_len,
				       (void *)dcomm_enter->resp_addr,
				       &resp_len,
				       is_sspdm);

	/*
	 * Set IoEnter args for next pdev_communicate. Upon
	 * success or error call pdev_communicate
	 */
	if (rc == 0) {
		dcomm_enter->status = RMI_DEV_COMM_ENTER_STATUS_RESPONSE;
		dcomm_enter->resp_len = resp_len;
	} else {
		dcomm_enter->status = RMI_DEV_COMM_ENTER_STATUS_ERROR;
		dcomm_enter->resp_len = 0;
		rc = -1;
	}

	return rc;
}

/*
 * Call either PDEV or VDEV communicate until the target state is reached for
 * either PDEV or VDEV
 */
int host_dev_communicate(struct host_realm *realm,
			 struct host_pdev *h_pdev,
			 struct host_vdev *h_vdev,
			 unsigned char target_state)
{
	int rc;
	unsigned char state;
	u_register_t error_state;
	u_register_t ret;
	struct rmi_dev_comm_enter *dcomm_enter;
	struct rmi_dev_comm_exit *dcomm_exit;
	bool stop;

	if (h_vdev) {
		if (h_vdev->dev_comm_data == NULL) {
			return -1;
		}

		dcomm_enter = &h_vdev->dev_comm_data->enter;
		dcomm_exit = &h_vdev->dev_comm_data->exit;

		error_state = RMI_VDEV_STATE_ERROR;
	} else {
		if (h_pdev->dev_comm_data == NULL) {
			return -1;
		}

		dcomm_enter = &h_pdev->dev_comm_data->enter;
		dcomm_exit = &h_pdev->dev_comm_data->exit;

		error_state = RMI_PDEV_STATE_ERROR;
	}

	dcomm_enter->status = RMI_DEV_COMM_ENTER_STATUS_NONE;
	dcomm_enter->resp_len = 0;

	rc = host_dev_get_state(h_pdev, h_vdev, &state);
	if (rc != 0) {
		return rc;
	}

	stop = false;
	do {
		ret = host_rmi_dev_communicate(realm, h_pdev, h_vdev);
		if (ret != RMI_SUCCESS) {
			ERROR("host_rmi_dev_communicate failed\n");
			rc = -1;
			break;
		}

		/*
		 * If cache is set, then the corresponding buffer(s) has the
		 * device object to be cached.
		 */
		if ((dcomm_exit->flags & RMI_DEV_COMM_EXIT_FLAGS_REQ_CACHE_BIT) != 0U ||
		    (dcomm_exit->flags & RMI_DEV_COMM_EXIT_FLAGS_RSP_CACHE_BIT) != 0U) {
			rc = host_dev_cache_dev_req_resp(h_pdev,
							 h_vdev,
							 dcomm_enter,
							 dcomm_exit);
			if (rc != 0) {
				ERROR("host_dev_cache_dev_req_resp failed\n");
				break;
			}
		}

		/* Send request to PDEV's DOE and get response */
		if ((dcomm_exit->flags & RMI_DEV_COMM_EXIT_FLAGS_REQ_SEND_BIT) != 0U) {
			rc = host_pdev_spdm_rsp_communicate(h_pdev, dcomm_enter, dcomm_exit);
			if (rc != 0) {
				ERROR("host_pdev_doe_communicate failed\n");
				break;
			}
		} else {
			dcomm_enter->status = RMI_DEV_COMM_ENTER_STATUS_NONE;
		}

		rc = host_dev_get_state(h_pdev, h_vdev, &state);
		if (rc != 0) {
			break;
		}
		if (state == target_state) {
			/*
			 * The target state was reached, but for some
			 * transitions this is not enough, need to continue
			 * calling it till certain flags are cleared in the
			 * exit. wait for that to happen.
			 */
			stop = dcomm_exit->flags == 0U;
		} else if (state == error_state) {
			ERROR("Failed to reach target_state %u instead of %u\n",
			      state,
			      (unsigned int)target_state);
			rc = -1;
			stop = true;
		}
	} while (!stop);

	return rc;
}

/*
 * Invoke RMI handler to transition PDEV state to 'to_state'
 */
static int host_pdev_transition(struct host_pdev *h_pdev, unsigned char to_state)
{
	int rc;

	switch (to_state) {
	case RMI_PDEV_STATE_NEW:
		rc = host_pdev_create(h_pdev);
		break;
	case RMI_PDEV_STATE_NEEDS_KEY:
		rc = host_dev_communicate(NULL, h_pdev, NULL, RMI_PDEV_STATE_NEEDS_KEY);
		break;
	case RMI_PDEV_STATE_HAS_KEY:
		rc = host_pdev_set_key(h_pdev);
		break;
	case RMI_PDEV_STATE_READY:
		rc = host_dev_communicate(NULL, h_pdev, NULL, RMI_PDEV_STATE_READY);
		break;
	case RMI_PDEV_STATE_STOPPING:
		rc = host_pdev_stop(h_pdev);
		break;
	case RMI_PDEV_STATE_STOPPED:
		rc = host_dev_communicate(NULL, h_pdev, NULL, RMI_PDEV_STATE_STOPPED);
		break;
	case RMI_PDEV_STATE_COMMUNICATING:
		rc = host_pdev_ide_key_refresh(h_pdev, RMI_PDEV_EVENT_IDE_KEY_REFRESH);
		break;
	case RMI_PDEV_STATE_IDE_RESETTING:
		rc = host_pdev_ide_reset(h_pdev);
		break;
	default:
		rc = -1;
	}

	if (rc != 0) {
		INFO("RMI command failed\n");
		return -1;
	}

	if (!is_host_pdev_state(h_pdev, to_state)) {
		ERROR("PDEV state not [%s]\n", get_pdev_state_str(to_state));
		return -1;
	}

	return 0;
}

static int host_pdev_do_ide_ops(struct host_pdev *pdev)
{
	int rc;

	/* PDEV to COMMUNICATING state, calls PDEV_notify.IDE_KEY_REFRESH */
	rc = host_pdev_transition(pdev, RMI_PDEV_STATE_COMMUNICATING);
	if (rc != 0) {
		INFO("PDEV transition: PDEV_READY -> COMMUNICATING failed\n");
		return -1;
	}

	/* Call rmi_pdev_communicate to do IDE key refresh */
	rc = host_pdev_transition(pdev, RMI_PDEV_STATE_READY);
	if (rc != 0) {
		INFO("PDEV transition: COMMUNICATING -> PDEV_READY failed\n");
		return -1;
	}

	/* PDEV to IDE_RESET state, calls PDEV_IDE_RESET */
	rc = host_pdev_transition(pdev, RMI_PDEV_STATE_IDE_RESETTING);
	if (rc != 0) {
		INFO("PDEV transition: PDEV_READY -> IDE_RESETTING failed\n");
		return -1;
	}

	/* Call rmi_pdev_communicate to do IDE reset */
	rc = host_pdev_transition(pdev, RMI_PDEV_STATE_READY);
	if (rc != 0) {
		INFO("PDEV transition: IDE_RESETTING -> PDEV_READY failed\n");
		return -1;
	}
	return rc;
}

/*
 * Allocate granules needed for a PDEV object like device communication data,
 * response buffer, PDEV AUX granules and memory required to store cert_chain
 */
static int host_pdev_setup(struct host_pdev *dev)
{
	struct smc_result result;
	int rc = -1;
	int spdm_rsp_id = -1;
	uint32_t i;

	memset(dev, 0, sizeof(struct host_pdev));

	/* Connect with SPDM responder emu */
	rc = host_spdm_rsp_connect(&spdm_rsp_id);
	if (rc != 0) {
		INFO("Connect to SPDM responder failed.\n");
		return -1;
	}
	/* Set the SPDM responder emu id */
	dev->pdev_id = (unsigned long)spdm_rsp_id;

	/* Allocate granule for PDEV and delegate */
	dev->pdev_ptr = allocate_granule();
	memset(dev->pdev_ptr, 0, GRANULE_SIZE);
	host_rmi_granule_delegate(dev->pdev_ptr, &result);
	if (!IS_RMI_RESULT_SUCCESS(result)) {
		rc = -1;
		goto out_cleanup;
	}

	/*
	 * Off chip PCIe device - set flags as non-coherent device protected by
	 * end to end IDE, with SPDM.
	 */
	dev->pdev_flags = (INPLACE(RMI_PDEV_FLAGS_SPDM, RMI_PDEV_SPDM_TRUE) |
			   INPLACE(RMI_PDEV_FLAGS_NCOH_IDE, RMI_PDEV_IDE_TRUE));

	/* Create a extended capability DVSEC in Root Port config space */
	if (EXTRACT(RMI_PDEV_FLAGS_NCOH_IDE, dev->pdev_flags) == RMI_PDEV_IDE_TRUE) {
		dev->root_id = 0U;
		dev->ecam_addr = host_utils_pci_get_ecam_base();

		rc = host_utils_pci_rp_dvsec_setup(dev->root_id);
		if (rc != 0) {
			INFO("pci_rp_dvsec_setup failed.\n");
			rc = -1;
			goto out_cleanup;
		}
	} else {
		dev->ecam_addr = 0UL;
	}

	/* Get num of aux granules required for this PDEV */
	host_rmi_pdev_aux_count(dev->pdev_flags, &result);
	if (!IS_RMI_RESULT_SUCCESS(result)) {
		rc = -1;
		goto out_cleanup;
	}
	dev->pdev_aux_num = result.x[1];

	/* Allocate aux granules for PDEV and delegate */
	INFO("PDEV create requires %u aux pages\n", dev->pdev_aux_num);
	for (i = 0; i < dev->pdev_aux_num; i++) {
		dev->pdev_aux[i] = allocate_granule();
		host_rmi_granule_delegate(dev->pdev_aux[i], &result);
		if (!IS_RMI_RESULT_SUCCESS(result)) {
			rc = -1;
			goto out_cleanup;
		}
	}

	/* Allocate dev_comm_data and send/recv buffer for Dev communication */
	dev->dev_comm_data = (struct rmi_dev_comm_data *)allocate_granule();
	memset(dev->dev_comm_data, 0, sizeof(struct rmi_dev_comm_data));
	dev->dev_comm_data->enter.req_addr = (unsigned long)allocate_granule();
	dev->dev_comm_data->enter.resp_addr = (unsigned long)allocate_granule();

	/* Allocate buffer to cache device certificate */
	dev->cert_slot_id = 0;
	dev->cert_chain = (uint8_t *)malloc((size_t)HOST_PDEV_CERT_LEN_MAX);
	dev->cert_chain_len = 0;
	if (dev->cert_chain == NULL) {
		rc = -1;
		goto out_cleanup;
	}

	/* Allocate buffer to cache device VCA */
	dev->vca = (uint8_t *)malloc((size_t)HOST_PDEV_VCA_LEN_MAX);
	dev->vca_len = 0;
	if (dev->vca == NULL) {
		rc = -1;
		goto out_cleanup;
	}

	/* Allocate buffer to store extracted public key */
	dev->public_key = allocate_granule();
	if (dev->public_key == NULL) {
		rc = -1;
		goto out_cleanup;
	}
	dev->public_key_len = GRANULE_SIZE;

	/* Allocate buffer to store public key metadata */
	dev->public_key_metadata = allocate_granule();
	if (dev->public_key_metadata == NULL) {
		rc = -1;
		goto out_cleanup;
	}
	dev->public_key_metadata_len = GRANULE_SIZE;

	/* Set algorithm to use for device digests */
	dev->hash_algo = RMI_HASH_SHA_512;

	return 0;

out_cleanup:
	host_pdev_cleanup(dev);
	return rc;
}

/*
 * Find devices (spdm_responder) and if any device exist create a PDEV instance
 * of the device with RMM and establish a secure session with the device.
 *
 * Returns:
 *	0	- No device found or DA is disabled in RMI features
 *	-1	- Error during device setup
 *	int	- Value other than 0 or -1 corresponds to the device id
 */
int host_pdev_probe_and_setup(void)
{
	unsigned long feat_reg0;
	struct smc_result result;
	struct host_pdev *pdev;
	uint8_t public_key_algo;
	int rc;

	pdev = &gbl_host_pdev;

	/* Check if DA enabled in RMI features */
	host_rmi_features(RMI_FEATURE_REGISTER_0_INDEX, &result);
	if (!IS_RMI_RESULT_SUCCESS(result)) {
		return -1;
	}
	feat_reg0 = result.x[1];

	if (EXTRACT(RMI_FEATURE_REGISTER_0_DA_EN, feat_reg0) ==
	    RMI_FEATURE_FALSE) {
		INFO("RMI FEAT DA not enabled. Skipping DA ABIs\n");
		return 0;
	}

	/* Allocate granules. Skip DA ABIs if host_pdev_setup fails */
	rc = host_pdev_setup(pdev);
	if (rc == -1) {
		INFO("host_pdev_setup failed. skipping DA ABIs...\n");
		return 0;
	}

	/* Call rmi_pdev_create to transition PDEV to STATE_NEW */
	rc = host_pdev_transition(pdev, RMI_PDEV_STATE_NEW);
	if (rc != 0) {
		ERROR("PDEV transition: NULL -> STATE_NEW failed\n");
		host_pdev_cleanup(pdev);
		return -1;
	}

	/* Call rmi_pdev_communicate to transition PDEV to NEEDS_KEY */
	rc = host_pdev_transition(pdev, RMI_PDEV_STATE_NEEDS_KEY);
	if (rc != 0) {
		ERROR("PDEV transition: PDEV_NEW -> PDEV_NEEDS_KEY failed\n");
		(void)host_pdev_reclaim((int)pdev->pdev_id);
		return -1;
	}

	/* Get public key. Verifying cert_chain not done by host but by Realm? */
	rc = host_get_public_key_from_cert_chain(pdev->cert_chain,
						 pdev->cert_chain_len,
						 pdev->public_key,
						 &pdev->public_key_len,
						 pdev->public_key_metadata,
						 &pdev->public_key_metadata_len,
						 &public_key_algo);
	if (rc != 0) {
		ERROR("Get public key failed\n");
		(void)host_pdev_reclaim((int)pdev->pdev_id);
		return -1;
	}

	if (public_key_algo == PUBLIC_KEY_ALGO_ECDSA_ECC_NIST_P256) {
		pdev->public_key_sig_algo = RMI_SIGNATURE_ALGORITHM_ECDSA_P256;
	} else if (public_key_algo == PUBLIC_KEY_ALGO_ECDSA_ECC_NIST_P384) {
		pdev->public_key_sig_algo = RMI_SIGNATURE_ALGORITHM_ECDSA_P384;
	} else {
		pdev->public_key_sig_algo = RMI_SIGNATURE_ALGORITHM_RSASSA_3072;
	}
	INFO("DEV public key len/sig_algo: %ld/%d\n",
	     pdev->public_key_len,
	     pdev->public_key_sig_algo);

	/* Call rmi_pdev_set_key transition PDEV to HAS_KEY */
	rc = host_pdev_transition(pdev, RMI_PDEV_STATE_HAS_KEY);
	if (rc != 0) {
		INFO("PDEV transition: PDEV_NEEDS_KEY -> PDEV_HAS_KEY failed\n");
		(void)host_pdev_reclaim((int)pdev->pdev_id);
		return -1;
	}

	/* Call rmi_pdev_communicate to transition PDEV to READY state */
	rc = host_pdev_transition(pdev, RMI_PDEV_STATE_READY);
	if (rc != 0) {
		INFO("PDEV transition: PDEV_HAS_KEY -> PDEV_READY failed\n");
		(void)host_pdev_reclaim((int)pdev->pdev_id);
		return -1;
	}

	/* do host_pdev IDE key refresh and IDE reset */
	if (EXTRACT(RMI_PDEV_FLAGS_NCOH_IDE, pdev->pdev_flags) == RMI_PDEV_IDE_TRUE) {
		rc = host_pdev_do_ide_ops(pdev);
		if (rc != 0) {
			INFO("PDEV IDE refresh, reset failed\n");
			(void)host_pdev_reclaim((int)pdev->pdev_id);
			return -1;
		}
	}

	return (int)pdev->pdev_id;
}

/*
 * Stop PDEV and terminate secure session and call PDEV destroy
 */
int host_pdev_reclaim(int host_pdev_id)
{
	struct host_pdev *pdev;
	int rc;

	pdev = &gbl_host_pdev;
	if (pdev->pdev_id != (unsigned long)host_pdev_id) {
		return -1;
	}

	rc = 0;

	/* Move the device to STOPPING state */
	if (host_pdev_transition(pdev, RMI_PDEV_STATE_STOPPING) != 0) {
		INFO("PDEV transition: to PDEV_STATE_STOPPING failed\n");
		rc = -1;
	}

	/* Do pdev_communicate to terminate secure session */
	if (host_pdev_transition(pdev, RMI_PDEV_STATE_STOPPED) != 0) {
		INFO("PDEV transition: to PDEV_STATE_STOPPED failed\n");
		rc = -1;
	}

	if (host_pdev_destroy(pdev) != 0) {
		INFO("PDEV transition: to STATE_NULL failed\n");
		rc = -1;
	}

	host_pdev_cleanup(pdev);
	return rc;
}

/*
 * Allocate granules needed for a VDEV object like device communication data,
 * response buffer, VDEV AUX granules and memory required to device
 * measurements, interface report.
 */
static int host_vdev_setup(struct host_pdev *h_pdev,
			   struct host_vdev *h_vdev,
			   unsigned long vdev_tdi_id)
{
	struct smc_result result;
	int rc;

	memset(h_vdev, 0, sizeof(struct host_vdev));

	/*
	 * Currently assigning one device is supported, for more than one device
	 * the VMM view of vdev_id and Realm view of device_id must match
	 */
	h_vdev->vdev_id = HOST_DA_VDEV_ID;

	/* This is TDI id, this must be same as PDEV ID */
	assert(h_pdev->pdev_id == vdev_tdi_id);
	h_vdev->tdi_id = vdev_tdi_id;

	h_vdev->flags = 0UL;
	h_vdev->pdev_ptr = h_pdev->pdev_ptr;

	/* Allocate granule for VDEV and delegate */
	h_vdev->vdev_ptr = allocate_granule();
	memset(h_vdev->vdev_ptr, 0, GRANULE_SIZE);
	host_rmi_granule_delegate(h_vdev->vdev_ptr, &result);
	if (!IS_RMI_RESULT_SUCCESS(result)) {
		rc = -1;
		goto out_cleanup;
	}

	/* Allocate dev_comm_data and send/recv buffer for Dev communication */
	h_vdev->dev_comm_data = (struct rmi_dev_comm_data *)allocate_granule();
	memset(h_vdev->dev_comm_data, 0, sizeof(struct rmi_dev_comm_data));
	h_vdev->dev_comm_data->enter.req_addr = (unsigned long)
			allocate_granule();
	h_vdev->dev_comm_data->enter.resp_addr = (unsigned long)
			allocate_granule();

	/* Allocate buffer to cache device measurements */
	h_vdev->meas = (uint8_t *)malloc((size_t)HOST_VDEV_MEAS_LEN_MAX);
	h_vdev->meas_len = 0;
	if (h_vdev->meas == NULL) {
		rc = -1;
		goto out_cleanup;
	}

	/* Allocate buffer to cache device interface report */
	h_vdev->ifc_report = (uint8_t *)malloc((size_t)HOST_VDEV_IFC_REPORT_LEN_MAX);
	h_vdev->ifc_report_len = 0;
	if (h_vdev->ifc_report == NULL) {
		rc = -1;
		goto out_cleanup;
	}

	return (int)h_vdev->vdev_id;

out_cleanup:
	host_vdev_cleanup(h_vdev);
	return rc;
}

/* Bind the vdev to the Realm */
int host_vdev_assign(struct host_realm *realm, unsigned long host_vdev_tdi_id)
{
	struct rmi_vdev_params *vdev_params;
	struct smc_result result;
	struct host_pdev *h_pdev;
	struct host_vdev *h_vdev;
	int host_vdev_id;

	h_pdev = &gbl_host_pdev;
	h_vdev = &gbl_host_vdev;

	/*
	 * Set up host VDEV. Allocate vdev granules and vdev communication
	 * data
	 */
	host_vdev_id = host_vdev_setup(h_pdev, h_vdev, host_vdev_tdi_id);
	if (host_vdev_id < 0) {
		INFO("host_vdev_setup failed\n");
		return -1;
	}

	/* Create vdev and bind it to the Realm */
	vdev_params = allocate_granule();
	memset(vdev_params, 0, GRANULE_SIZE);

	vdev_params->vdev_id = h_vdev->vdev_id;
	vdev_params->tdi_id = h_vdev->tdi_id;
	vdev_params->flags = h_vdev->flags;
	vdev_params->num_aux = 0;

	host_rmi_vdev_create(realm->rd,
			     h_pdev->pdev_ptr,
			     h_vdev->vdev_ptr,
			     vdev_params,
			     &result);
	if (!IS_RMI_RESULT_SUCCESS(result)) {
		host_vdev_cleanup(h_vdev);
		return -1;
	}

	return host_vdev_id;
}

int host_vdev_reclaim(struct host_realm *realm, int host_vdev_id)
{
	void *rd_ptr;
	void *pdev_ptr;
	void *vdev_ptr;
	struct host_pdev *h_pdev;
	struct host_vdev *h_vdev;
	struct smc_result result;
	int rc;
	unsigned char state;

	assert(host_vdev_id >= 0);

	vdev_ptr = host_find_vdev_from_id(host_vdev_id);
	pdev_ptr = host_find_pdev_from_vdev(vdev_ptr);

	h_pdev = get_host_pdev_from_ptr(pdev_ptr);
	h_vdev = get_host_vdev_from_ptr(vdev_ptr);

	assert(vdev_ptr != NULL);
	assert(pdev_ptr != NULL);
	assert(h_pdev != NULL);
	assert(h_vdev != NULL);

	rd_ptr = realm->rd;

	rc = host_vdev_get_state(h_vdev, &state);
	if (rc != 0) {
		rc = -1;
		goto out_destroy;
	}

	if ((state == RMI_VDEV_STATE_LOCKED) || (state == RMI_VDEV_STATE_STARTED)) {
		host_rmi_vdev_unlock(rd_ptr, pdev_ptr, vdev_ptr, &result);
		if (!IS_RMI_RESULT_SUCCESS(result)) {
			rc = -1;
		}

		/* Do vdev_communicate to move to UNLOCKED state */
		if (host_dev_communicate(realm, h_pdev, h_vdev,
					 RMI_VDEV_STATE_UNLOCKED) != 0) {
			INFO("VDEV unlock -> UNLOCKED failed\n");
			rc = -1;
		}
	} else if (state > RMI_VDEV_STATE_ERROR) {
		INFO("Unexpected VDEV state %u\n", state);
		rc = -1;
	}

out_destroy:
	host_rmi_vdev_destroy(rd_ptr, pdev_ptr, vdev_ptr, &result);
	if (!IS_RMI_RESULT_SUCCESS(result)) {
		rc = -1;
	}

	host_vdev_cleanup(h_vdev);
	return rc;
}

/*
 * Run realm to call DA related RSI to get device attestation records
 */
int host_realm_run_da(struct host_realm *realm)
{
	struct smc_result result;

	realm->rec_params->pc = (uintptr_t)host_realm_da_rsi_main;

	/* Run the Realm to call DA RSIs */
	memset(realm->rec_run, 0, sizeof(*realm->rec_run));
	host_rmi_rec_enter(realm->rec, realm->rec_run, &result);
	if (!IS_RMI_RESULT_SUCCESS(result)) {
		return -1;
	}

	if (realm->rec_run->exit.exit_reason == RMI_EXIT_FIQ) {
		INFO("Realm executed DA RSI successfully\n");
	}

	return 0;
}
