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
		   struct smc_result *res);

void host_rmi_version(unsigned long rmi_version, struct smc_result *res)
{
	handle_ns_smc(SMC_RMI_VERSION,
		      rmi_version,
		      0, 0, 0, 0, 0,
		      res);
}

void host_rmi_granule_delegate(void *granule_address, struct smc_result *res)
{
	handle_ns_smc(SMC_RMI_GRANULE_DELEGATE,
		      (uintptr_t)granule_address,
		      0, 0, 0, 0, 0,
		      res);
}

void host_rmi_granule_undelegate(void *granule_address, struct smc_result *res)
{
	handle_ns_smc(SMC_RMI_GRANULE_UNDELEGATE,
		      (uintptr_t)granule_address,
		      0, 0, 0, 0, 0,
		      res);
}

void host_rmi_data_create(void *rd, void *data, uintptr_t ipa, void *src,
			  uint64_t flags, struct smc_result *res)
{
	handle_ns_smc(SMC_RMI_DATA_CREATE,
		      (uintptr_t)rd,
		      (uintptr_t)data, ipa,
		      (uintptr_t)src, flags, 0,
		      res);
}

void host_rmi_data_create_unknown(void *rd, uintptr_t data, uintptr_t ipa,
				  struct smc_result *res)
{
	handle_ns_smc(SMC_RMI_DATA_CREATE_UNKNOWN,
		      (uintptr_t)rd,
		      data, ipa,
		      0, 0, 0,
		      res);
}

void host_rmi_data_destroy(void *rd, uintptr_t ipa, struct smc_result *res)
{
	handle_ns_smc(SMC_RMI_DATA_DESTROY,
		      (uintptr_t)rd, ipa,
		      0, 0, 0, 0,
		      res);
}

void host_rmi_realm_activate(void *rd, struct smc_result *res)
{
	handle_ns_smc(SMC_RMI_REALM_ACTIVATE,
		      (uintptr_t)rd,
		      0, 0, 0, 0, 0,
		      res);
}

void host_rmi_realm_create(void *rd, void *params_ptr, struct smc_result *res)
{
	handle_ns_smc(SMC_RMI_REALM_CREATE,
		      (uintptr_t)rd,
		      (uintptr_t)params_ptr,
		      0, 0, 0, 0,
		      res);
}

void host_rmi_realm_destroy(void *rd, struct smc_result *res)
{
	handle_ns_smc(SMC_RMI_REALM_DESTROY,
		      (uintptr_t)rd,
		      0, 0, 0, 0, 0,
		      res);
}

void host_rmi_rec_create(void *rd, void *rec, void *params_ptr, struct smc_result *res)
{
	handle_ns_smc(SMC_RMI_REC_CREATE,
		      (uintptr_t)rd,
		      (uintptr_t)rec,
		      (uintptr_t)params_ptr,
		      0, 0, 0,
		      res);
}

void host_rmi_rec_destroy(void *rec, struct smc_result *res)
{
	handle_ns_smc(SMC_RMI_REC_DESTROY,
		      (uintptr_t)rec,
		      0, 0, 0, 0, 0,
		      res);
}

void host_rmi_rec_enter(void *rec, void *run_ptr, struct smc_result *res)
{
	handle_ns_smc(SMC_RMI_REC_ENTER,
		      (uintptr_t)rec,
		      (uintptr_t)run_ptr,
		      0, 0, 0, 0,
		      res);
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
		      res);
}

void host_rmi_rtt_destroy(void *rd, void *ipa, unsigned int level, struct smc_result *res)
{
	handle_ns_smc(SMC_RMI_RTT_DESTROY,
		      (uintptr_t)rd,
		      (uintptr_t)ipa,
		      level,
		      0, 0, 0,
		      res);
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
		res);
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
		res);
}

void host_rmi_rtt_map_unprotected(void *rd, uintptr_t ipa, uintptr_t level,
				  uintptr_t desc, struct smc_result *res)
{
	handle_ns_smc(SMC_RMI_RTT_MAP_UNPROTECTED,
		      (uintptr_t)rd,
		      ipa,
		      level,
		      desc, 0, 0,
		      res);
}

void host_rmi_rtt_read_entry(void *rd, uintptr_t ipa, uintptr_t level, struct smc_result *res)
{
	handle_ns_smc(SMC_RMI_RTT_READ_ENTRY,
		      (uintptr_t)rd,
		      ipa,
		      level,
		      0, 0, 0,
		      res);
}

void host_rmi_rtt_unmap_unprotected(void *rd, uintptr_t ipa, uintptr_t level,
				    struct smc_result *res)
{
	handle_ns_smc(SMC_RMI_RTT_UNMAP_UNPROTECTED,
		      (uintptr_t)rd,
		      ipa,
		      level,
		      0, 0, 0,
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
		      res);
}

void host_rmi_features(unsigned long index, struct smc_result *res)
{
	handle_ns_smc(SMC_RMI_FEATURES,
		      index,
		      0, 0, 0, 0, 0,
		      res);
}

void host_rmi_rtt_fold(void *rd, uintptr_t ipa, uintptr_t level,
		       struct smc_result *res)
{
	handle_ns_smc(SMC_RMI_RTT_FOLD,
		      (uintptr_t)rd,
		      ipa,
		      level,
		      0, 0, 0,
		      res);
}

void host_rmi_rec_aux_count(void *rd, struct smc_result *res)
{
	handle_ns_smc(SMC_RMI_REC_AUX_COUNT,
		      (uintptr_t)rd,
		      0, 0, 0, 0, 0,
		      res);
}

void host_rmi_rtt_init_ripas(void *rd, uintptr_t base, uintptr_t top,
			     struct smc_result *res)
{
	handle_ns_smc(SMC_RMI_RTT_INIT_RIPAS,
		      (uintptr_t)rd,
		      base, top,
		      0, 0, 0,
		      res);
}

void host_rmi_rtt_set_ripas(void *rd, void *rec, uintptr_t base, uintptr_t top,
			    struct smc_result *res)
{
	handle_ns_smc(SMC_RMI_RTT_SET_RIPAS,
		      (uintptr_t)rd,
		      (uintptr_t)rec,
		      base, top,
		      0, 0,
		      res);
}
