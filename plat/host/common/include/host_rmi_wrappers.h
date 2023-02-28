/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef HOST_RMI_WRAPPERS_H
#define HOST_RMI_WRAPPERS_H

#include <smc-rmi.h>

void host_rmi_granule_delegate(void *granule_address, struct smc_result *ret);
void host_rmi_granule_undelegate(void *granule_address, struct smc_result *ret);
void host_rmi_realm_create(void *rd, void *params_ptr, struct smc_result *ret);
void host_rmi_realm_destroy(void *rd, struct smc_result *ret);
void host_rmi_rtt_create(void *rtt, void *rd, void *ipa,
			 unsigned int level, struct smc_result *ret);
void host_rmi_rtt_destroy(void *rtt, void *rd, void *ipa,
			  unsigned int level, struct smc_result *ret);
void host_rmi_rec_aux_count(void *rd, struct smc_result *ret);
void host_rmi_rec_create(void *rec, void *rd, void *params_ptr,
			 struct smc_result *ret);
void host_rmi_rec_destroy(void *rec, struct smc_result *ret);
void host_rmi_realm_activate(void *rd, struct smc_result *ret);
void host_rmi_rec_enter(void *rec, void *run_ptr, struct smc_result *ret);

#endif /* HOST_RMI_WRAPPERS_H */
