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

void host_rmi_version(unsigned long rmi_verion, struct smc_result *res)
{
	handle_ns_smc(SMC_RMI_VERSION,
		rmi_verion,
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

void host_rmi_rtt_create(void *rd, void *rtt, void *ipa, unsigned int level, struct smc_result *res)
{
	handle_ns_smc(SMC_RMI_RTT_CREATE,
		(uintptr_t)rd,
		(uintptr_t)rtt,
		(uintptr_t)ipa,
		level,
		0, 0,
		res);
}

void host_rmi_rtt_destroy(void *rd, void *ipa, unsigned int level,
			  struct smc_result *res)
{
	handle_ns_smc(SMC_RMI_RTT_DESTROY,
		(uintptr_t)rd,
		(uintptr_t)ipa,
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

void host_rmi_realm_activate(void *rd, struct smc_result *res)
{
	handle_ns_smc(SMC_RMI_REALM_ACTIVATE,
		(uintptr_t)rd,
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

void host_rmi_data_create(uintptr_t data, void *rd, uintptr_t ipa,
			 uintptr_t src, struct smc_result *res)
{
	handle_ns_smc(SMC_RMI_DATA_CREATE,
		data,
		(uintptr_t)rd, ipa, src,
		0, 0,
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

void host_rmi_rtt_init_ripas(void *rd, uintptr_t base, uintptr_t top,
			struct smc_result *res)
{
	handle_ns_smc(SMC_RMI_RTT_INIT_RIPAS,
		(uintptr_t)rd,
		base, top,
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
