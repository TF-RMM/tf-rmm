/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <host_rmi_wrappers.h>

/* Declaring SMC handler */
void handle_ns_smc(unsigned int function_id,
		   unsigned long arg0,
		   unsigned long arg1,
		   unsigned long arg2,
		   unsigned long arg3,
		   unsigned long arg4,
		   unsigned long arg5,
		   unsigned long arg6,
		   struct smc_result *res);

void host_rmi_version(unsigned long rmi_version, struct smc_result *res)
{
	handle_ns_smc(SMC_RMI_VERSION,
		      rmi_version,
		      0, 0, 0, 0, 0,
		      0, res);
}

void host_rmm_activate(struct smc_result *res)
{
	handle_ns_smc(SMC_RMI_RMM_ACTIVATE,
		      0, 0, 0, 0, 0, 0, 0,
		      res);
}

void host_rmi_granule_range_delegate(void *granule_start, void *granule_end,
				     struct smc_result *res)
{
	handle_ns_smc(SMC_RMI_GRANULE_RANGE_DELEGATE,
		      (uintptr_t)granule_start,
		      (uintptr_t)granule_end,
		      0, 0, 0, 0, 0,
		      res);
}

void host_rmi_granule_range_undelegate(void *granule_start, void *granule_end,
				       struct smc_result *res)
{
	handle_ns_smc(SMC_RMI_GRANULE_RANGE_UNDELEGATE,
		      (uintptr_t)granule_start,
		      (uintptr_t)granule_end,
		      0, 0, 0, 0, 0,
		      res);
}

void host_rmi_rtt_data_map_init(void *rd, void *data, uintptr_t ipa, void *src,
			  uint64_t flags, struct smc_result *res)
{
	handle_ns_smc(SMC_RMI_RTT_DATA_MAP_INIT,
		      (uintptr_t)rd,
		      (uintptr_t)data, ipa,
		      (uintptr_t)src, flags, 0,
		      0, res);
}

void host_rmi_realm_activate(void *rd, struct smc_result *res)
{
	handle_ns_smc(SMC_RMI_REALM_ACTIVATE,
		      (uintptr_t)rd,
		      0, 0, 0, 0, 0,
		      0, res);
}

void host_rmi_realm_create(void *rd, void *params_ptr, struct smc_result *res)
{
	handle_ns_smc(SMC_RMI_REALM_CREATE,
		      (uintptr_t)rd,
		      (uintptr_t)params_ptr,
		      0, 0, 0, 0,
		      0, res);
}

void host_rmi_realm_destroy(void *rd, struct smc_result *res)
{
	handle_ns_smc(SMC_RMI_REALM_DESTROY,
		      (uintptr_t)rd,
		      0, 0, 0, 0, 0,
		      0, res);
}

void host_rmi_rec_create(void *rd, void *rec, void *params_ptr,
			 void *handle, void *donate_req,
			 struct smc_result *res)
{
	unsigned long *handle_ptr = (unsigned long *)handle;
	unsigned long *req_ptr = (unsigned long *)donate_req;

	handle_ns_smc(SMC_RMI_REC_CREATE,
		      (uintptr_t)rd,
		      (uintptr_t)rec,
		      (uintptr_t)params_ptr,
		      0, 0, 0, 0,
		      res);

	*handle_ptr = res->x[1];
	*req_ptr = res->x[2];
}

void host_rmi_rec_destroy(void *rec, void *handle, struct smc_result *res)
{
	unsigned long *handle_ptr = (unsigned long *)handle;

	handle_ns_smc(SMC_RMI_REC_DESTROY,
		      (uintptr_t)rec,
		      0, 0, 0, 0, 0, 0,
		      res);

	*handle_ptr = res->x[1];
}

void host_rmi_rec_enter(void *rec, void *run_ptr, struct smc_result *res)
{
	handle_ns_smc(SMC_RMI_REC_ENTER,
		      (uintptr_t)rec,
		      (uintptr_t)run_ptr,
		      0, 0, 0, 0,
		      0, res);
}

void host_rmi_rtt_create(void *rd, void *rtt, void *ipa, unsigned int level,
			 struct smc_result *res)
{
	handle_ns_smc(SMC_RMI_RTT_CREATE,
		      (uintptr_t)rd,
		      (uintptr_t)rtt,
		      (uintptr_t)ipa,
		      level,
		      0, 0,
		      0, res);
}

void host_rmi_rtt_destroy(void *rd, void *ipa, unsigned int level, struct smc_result *res)
{
	handle_ns_smc(SMC_RMI_RTT_DESTROY,
		      (uintptr_t)rd,
		      (uintptr_t)ipa,
		      level,
		      0, 0, 0,
		      0, res);
}

void host_rmi_rtt_aux_create(void *rd, void *rtt, void *ipa, unsigned int level,
			     unsigned int index, struct smc_result *res)
{
	handle_ns_smc(SMC_RMI_RTT_CREATE,
		(uintptr_t)rd,
		(uintptr_t)rtt,
		(uintptr_t)ipa,
		level,
		index,
		0,
		0, res);
}

void host_rmi_rtt_aux_destroy(void *rd, void *ipa, unsigned int level,
			      unsigned int index, struct smc_result *res)
{
	handle_ns_smc(SMC_RMI_RTT_DESTROY,
		(uintptr_t)rd,
		(uintptr_t)ipa,
		level,
		index,
		0, 0,
		0, res);
}

void host_rmi_rtt_map_unprotected(void *rd, uintptr_t ipa, uintptr_t level,
				  uintptr_t desc, struct smc_result *res)
{
	handle_ns_smc(SMC_RMI_RTT_MAP_UNPROTECTED,
		      (uintptr_t)rd,
		      ipa,
		      level,
		      desc, 0, 0,
		      0, res);
}

void host_rmi_rtt_read_entry(void *rd, uintptr_t ipa, uintptr_t level, struct smc_result *res)
{
	handle_ns_smc(SMC_RMI_RTT_READ_ENTRY,
		      (uintptr_t)rd,
		      ipa,
		      level,
		      0, 0, 0,
		      0, res);
}

void host_rmi_rtt_unmap_unprotected(void *rd, uintptr_t ipa, uintptr_t level,
				    struct smc_result *res)
{
	handle_ns_smc(SMC_RMI_RTT_UNMAP_UNPROTECTED,
		      (uintptr_t)rd,
		      ipa,
		      level,
		      0, 0, 0,
		      0, res);
}

void host_rmi_rtt_data_unmap(void *rd, uintptr_t base, uintptr_t top,
			     unsigned long flags, uintptr_t oaddr,
			     struct smc_result *res)
{
	handle_ns_smc(SMC_RMI_RTT_DATA_UNMAP,
		      (uintptr_t)rd,
		      base,
		      top,
		      flags,
		      oaddr,
		      0,
		      0,
		      res);
}

void host_rmi_rtt_data_map(void *rd, uintptr_t base, uintptr_t top,
			   unsigned long flags, uintptr_t oaddr,
			   struct smc_result *res)
{
	handle_ns_smc(SMC_RMI_RTT_DATA_MAP,
		      (uintptr_t)rd,
		      base,
		      top,
		      flags,
		      oaddr,
		      0,
		      0,
		      res);
}

void host_rmi_psci_complete(void *calling_rec, void *target_rec, uintptr_t status,
		struct smc_result *res)
{
	handle_ns_smc(SMC_RMI_PSCI_COMPLETE,
		      (uintptr_t)calling_rec,
		      (uintptr_t)target_rec,
		      status,
		      0, 0, 0,
		      0, res);
}

void host_rmi_features(unsigned long index, struct smc_result *res)
{
	handle_ns_smc(SMC_RMI_FEATURES,
		      index,
		      0, 0, 0, 0, 0,
		      0, res);
}

void host_rmi_rtt_fold(void *rd, uintptr_t ipa, uintptr_t level,
		       struct smc_result *res)
{
	handle_ns_smc(SMC_RMI_RTT_FOLD,
		      (uintptr_t)rd,
		      ipa,
		      level,
		      0, 0, 0,
		      0, res);
}

void host_rmi_rtt_init_ripas(void *rd, uintptr_t base, uintptr_t top,
			     struct smc_result *res)
{
	handle_ns_smc(SMC_RMI_RTT_INIT_RIPAS,
		      (uintptr_t)rd,
		      base, top,
		      0, 0, 0,
		      0, res);
}

void host_rmi_rtt_set_ripas(void *rd, void *rec, uintptr_t base, uintptr_t top,
			    struct smc_result *res)
{
	handle_ns_smc(SMC_RMI_RTT_SET_RIPAS,
		      (uintptr_t)rd,
		      (uintptr_t)rec,
		      base, top,
		      0, 0,
		      0, res);
}

void host_rmi_pdev_create(void *pdev, void *pdev_params_ptr,
			  struct smc_result *res)
{
	handle_ns_smc(SMC_RMI_PDEV_CREATE, (uintptr_t)pdev,
		      (uintptr_t)pdev_params_ptr, 0, 0, 0, 0, 0, res);
}

void host_rmi_pdev_aux_count(unsigned long pdev_flags, struct smc_result *res)
{
	handle_ns_smc(SMC_RMI_PDEV_AUX_COUNT, (uintptr_t)pdev_flags,
		      0, 0, 0, 0, 0, 0, res);
}

void host_rmi_pdev_communicate(void *pdev, void *io_data_ptr,
			       struct smc_result *res)
{
	handle_ns_smc(SMC_RMI_PDEV_COMMUNICATE, (uintptr_t)pdev,
		      (uintptr_t)io_data_ptr, 0, 0, 0, 0, 0, res);
}

void host_rmi_pdev_get_state(void *pdev, struct smc_result *res)
{
	handle_ns_smc(SMC_RMI_PDEV_GET_STATE, (uintptr_t)pdev,
		      0, 0, 0, 0, 0, 0, res);
}

void host_rmi_pdev_set_pubkey(void *pdev, void *pubkey_params_ptr,
			      struct smc_result *res)
{
	handle_ns_smc(SMC_RMI_PDEV_SET_PUBKEY, (uintptr_t)pdev,
		      (uintptr_t)pubkey_params_ptr, 0, 0, 0, 0, 0, res);
}

void host_rmi_pdev_abort(void *pdev, struct smc_result *res)
{
	handle_ns_smc(SMC_RMI_PDEV_ABORT, (uintptr_t)pdev, 0, 0, 0, 0, 0, 0, res);
}

void host_rmi_pdev_stop(void *pdev, struct smc_result *res)
{
	handle_ns_smc(SMC_RMI_PDEV_STOP, (uintptr_t)pdev, 0, 0, 0, 0, 0, 0, res);
}

void host_rmi_pdev_destroy(void *pdev, struct smc_result *res)
{
	handle_ns_smc(SMC_RMI_PDEV_DESTROY, (uintptr_t)pdev, 0, 0, 0, 0, 0, 0, res);
}

void host_rmi_pdev_ide_key_refresh(void *pdev, unsigned long ev, struct smc_result *res)
{
	handle_ns_smc(SMC_RMI_PDEV_IDE_KEY_REFRESH, (uintptr_t)pdev, (uintptr_t)ev, 0, 0,
		      0, 0, 0, res);
}

void host_rmi_pdev_ide_reset(void *pdev, struct smc_result *res)
{
	handle_ns_smc(SMC_RMI_PDEV_IDE_RESET, (uintptr_t)pdev, 0, 0, 0, 0, 0,
		      0, res);
}

void host_rmi_vdev_create(void *rd, void *pdev_ptr, void *vdev_ptr,
			  void *vdev_params_ptr, struct smc_result *res)
{
	handle_ns_smc(SMC_RMI_VDEV_CREATE, (uintptr_t)rd, (uintptr_t)pdev_ptr,
		      (uintptr_t)vdev_ptr, (uintptr_t)vdev_params_ptr, 0, 0,
		      0, res);
}

void host_rmi_vdev_communicate(void *rd, void *pdev_ptr, void *vdev_ptr,
			       void *data_ptr, struct smc_result *res)
{
	handle_ns_smc(SMC_RMI_VDEV_COMMUNICATE, (uintptr_t) rd, (uintptr_t)pdev_ptr,
		      (uintptr_t)vdev_ptr, (uintptr_t)data_ptr, 0, 0, 0, res);
}

void host_rmi_vdev_complete(void *rec_ptr, void *vdev_ptr,
			    struct smc_result *res)
{
	handle_ns_smc(SMC_RMI_VDEV_COMPLETE, (uintptr_t)rec_ptr,
		      (uintptr_t)vdev_ptr, 0, 0, 0, 0, 0, res);
}

void host_rmi_vdev_get_state(void *vdev, struct smc_result *res)
{
	handle_ns_smc(SMC_RMI_VDEV_GET_STATE, (uintptr_t)vdev,
		      0, 0, 0, 0, 0, 0, res);
}

void host_rmi_vdev_abort(void *vdev, struct smc_result *res)
{
	handle_ns_smc(SMC_RMI_VDEV_ABORT, (uintptr_t)vdev,
		      0, 0, 0, 0, 0, 0, res);
}

void host_rmi_vdev_unlock(void *rd, void *pdev, void *vdev,
			  struct smc_result *res)
{
	handle_ns_smc(SMC_RMI_VDEV_UNLOCK, (uintptr_t)rd,
		(uintptr_t)pdev, (uintptr_t)vdev, 0, 0, 0, 0, res);
}

void host_rmi_vdev_destroy(void *rd, void *pdev, void *vdev,
			   struct smc_result *res)
{
	handle_ns_smc(SMC_RMI_VDEV_DESTROY, (uintptr_t)rd, (uintptr_t)pdev,
		      (uintptr_t)vdev, 0, 0, 0, 0, res);
}

void host_rmi_granule_tracking_get(unsigned long addr, struct smc_result *res)
{
	handle_ns_smc(SMC_RMI_GRANULE_TRACKING_GET,
		      addr,
		      0, 0, 0, 0, 0, 0,
		      res);
}

void host_rmi_rmm_config_get(unsigned long config_ptr, struct smc_result *res)
{
	handle_ns_smc(SMC_RMI_RMM_CONFIG_GET,
		      config_ptr,
		      0, 0, 0, 0, 0, 0,
		      res);
}

void host_rmi_rmm_config_set(unsigned long config_ptr, struct smc_result *res)
{
	handle_ns_smc(SMC_RMI_RMM_CONFIG_SET,
		      config_ptr,
		      0, 0, 0, 0, 0, 0,
		      res);
}

void host_rmi_op_mem_donate(unsigned long handle, void *list_addr,
			    unsigned long list_count,
			    void *donation_req, void *consumed_entries,
			    struct smc_result *res)
{
	unsigned long *req = (unsigned long *)donation_req;
	unsigned long *consumed = (unsigned long *)consumed_entries;;

	handle_ns_smc(SMC_RMI_OP_MEM_DONATE,
		      handle,
		      (uintptr_t)list_addr,
		      list_count,
		      0, 0, 0, 0,
		      res);

	*consumed = res->x[1];
	*req = res->x[2];
}

void host_rmi_op_mem_reclaim(unsigned long handle, void *list_addr,
			     unsigned long list_count,
			     void *consumed_entries,
			     struct smc_result *res)
{
	unsigned long *entries = (unsigned long *)consumed_entries;

	handle_ns_smc(SMC_RMI_OP_MEM_RECLAIM,
		      handle,
		      (uintptr_t)list_addr,
		      list_count,
		      0, 0, 0, 0,
		      res);

	*entries = res->x[1];
}

void host_rmi_op_continue(void *handle, unsigned long flags,
			  void *donate_req, struct smc_result *res)
{
	unsigned long *req = (unsigned long *)donate_req;
	unsigned long *hdlr = (unsigned long *)handle;

	handle_ns_smc(SMC_RMI_OP_CONTINUE,
		      *hdlr,
		      flags,
		      0, 0, 0, 0, 0,
		      res);

	*hdlr = res->x[1];
	*req = res->x[2];
}

void host_rmi_op_cancel(unsigned long handle, unsigned long flags,
			struct smc_result *res)
{
	handle_ns_smc(SMC_RMI_OP_CANCEL,
		      flags,
		      handle,
		      0, 0, 0, 0, 0,
		      res);
}
