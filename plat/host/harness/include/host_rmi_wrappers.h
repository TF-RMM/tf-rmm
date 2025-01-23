/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef HOST_RMI_WRAPPERS_H
#define HOST_RMI_WRAPPERS_H

#include <smc-rmi.h>

void host_rmi_version(unsigned long rmi_version, struct smc_result *res);
void host_rmi_granule_delegate(void *granule_address, struct smc_result *res);
void host_rmi_granule_undelegate(void *granule_address, struct smc_result *res);
void host_rmi_data_create(void *rd, void *data, uintptr_t ipa, void *src,
		uint64_t flags, struct smc_result *res);
void host_rmi_data_create_unknown(void *rd, uintptr_t data, uintptr_t ipa, struct smc_result *res);
void host_rmi_data_destroy(void *rd, uintptr_t ipa, struct smc_result *res);

void host_rmi_realm_activate(void *rd, struct smc_result *res);
void host_rmi_realm_create(void *rd, void *params_ptr, struct smc_result *res);
void host_rmi_realm_destroy(void *rd, struct smc_result *res);
void host_rmi_rec_create(void *rd, void *rec, void *params_ptr, struct smc_result *res);
void host_rmi_rtt_create(void *rd, void *rtt, void *ipa,
			 unsigned int level, struct smc_result *res);
void host_rmi_rtt_aux_create(void *rd, void *rtt, void *ipa, unsigned int level,
			     unsigned int index, struct smc_result *res);
void host_rmi_rtt_destroy(void *rd, void *ipa, unsigned int level,
			  struct smc_result *res);
void host_rmi_rtt_aux_destroy(void *rd, void *ipa, unsigned int level,
			      unsigned int index, struct smc_result *res);
void host_rmi_rec_aux_count(void *rd, struct smc_result *res);
void host_rmi_rec_create(void *rd, void *rec, void *params_ptr,
			 struct smc_result *res);
void host_rmi_rec_destroy(void *rec, struct smc_result *res);
void host_rmi_rec_enter(void *rec, void *run_ptr, struct smc_result *res);
void host_rmi_rtt_create(void *rd, void *rtt, void *ipa,
		unsigned int level, struct smc_result *res);
void host_rmi_rtt_destroy(void *rd, void *ipa, unsigned int level, struct smc_result *res);
void host_rmi_rtt_map_unprotected(void *rd, uintptr_t ipa, uintptr_t level,
		uintptr_t desc, struct smc_result *res);

void host_rmi_rtt_read_entry(void *rd, uintptr_t ipa, uintptr_t level, struct smc_result *res);
void host_rmi_rtt_unmap_unprotected(void *rd, uintptr_t ipa, uintptr_t level,
		struct smc_result *res);

void host_rmi_psci_complete(void *calling_rec, void *target_rec, uintptr_t status,
		struct smc_result *res);
void host_rmi_features(unsigned long index, struct smc_result *res);
void host_rmi_rtt_fold(void *rd, uintptr_t ipa, uintptr_t level, struct smc_result *res);
void host_rmi_rec_aux_count(void *rd, struct smc_result *res);
void host_rmi_rtt_init_ripas(void *rd, uintptr_t base, uintptr_t top, struct smc_result *res);
void host_rmi_rtt_set_ripas(void *rd, void *rec, uintptr_t base, uintptr_t top,
		struct smc_result *res);

#endif /* HOST_RMI_WRAPPERS_H */
