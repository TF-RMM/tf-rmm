/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef SMC_HANDLER_H
#define SMC_HANDLER_H

#include <smc.h>

void smc_version(unsigned long rmi_version,
				struct smc_result *res);

void smc_read_feature_register(unsigned long index,
				struct smc_result *res);

unsigned long smc_data_create(unsigned long rd_addr,
			      unsigned long data_addr,
			      unsigned long map_addr,
			      unsigned long src_addr,
			      unsigned long flags);

unsigned long smc_data_create_unknown(unsigned long rd_addr,
				      unsigned long data_addr,
				      unsigned long map_addr);

void smc_data_destroy(unsigned long rd_addr,
		      unsigned long map_addr,
		      struct smc_result *res);

unsigned long smc_granule_delegate(unsigned long addr);

unsigned long smc_granule_undelegate(unsigned long addr);

unsigned long smc_realm_activate(unsigned long rd_addr);

unsigned long smc_realm_create(unsigned long rd_addr,
				unsigned long realm_params_addr);

unsigned long smc_realm_destroy(unsigned long rd_addr);

unsigned long smc_rec_create(unsigned long rd_addr,
			     unsigned long rec_addr,
			     unsigned long rec_params_addr);

unsigned long smc_rec_destroy(unsigned long rec_addr);

unsigned long smc_rec_enter(unsigned long rec_addr,
			    unsigned long rec_run_addr);

void smc_rec_aux_count(unsigned long rd_addr,
			struct smc_result *res);

unsigned long smc_rtt_create(unsigned long rd_addr,
			     unsigned long rtt_addr,
			     unsigned long map_addr,
			     unsigned long ulevel);

unsigned long smc_rtt_aux_create(unsigned long rd_addr,
				 unsigned long rtt_addr,
				 unsigned long map_addr,
				 unsigned long ulevel,
				 unsigned long index);

void smc_rtt_destroy(unsigned long rd_addr,
		     unsigned long map_addr,
		     unsigned long ulevel,
		     struct smc_result *res);

void smc_rtt_aux_destroy(unsigned long rd_addr,
			 unsigned long map_addr,
			 unsigned long ulevel,
			 unsigned long index,
			 struct smc_result *res);

void smc_rtt_fold(unsigned long rd_addr,
		  unsigned long map_addr,
		  unsigned long ulevel,
		  struct smc_result *res);

void smc_rtt_aux_fold(unsigned long rd_addr,
		      unsigned long map_addr,
		      unsigned long ulevel,
		      unsigned long index,
		      struct smc_result *res);

unsigned long smc_rtt_map_unprotected(unsigned long rd_addr,
				      unsigned long map_addr,
				      unsigned long ulevel,
				      unsigned long s2tte);

void smc_rtt_unmap_unprotected(unsigned long rd_addr,
				unsigned long map_addr,
				unsigned long ulevel,
				struct smc_result *res);

void smc_rtt_dev_mem_validate(unsigned long rd_addr, unsigned long rec_addr,
			      unsigned long base, unsigned long top,
			      struct smc_result *res);

void smc_rtt_read_entry(unsigned long rd_addr,
			unsigned long map_addr,
			unsigned long ulevel,
			struct smc_result *res);

unsigned long smc_psci_complete(unsigned long calling_rec_addr,
				unsigned long target_rec_addr,
				unsigned long status);

void smc_rtt_init_ripas(unsigned long rd_addr,
			unsigned long base,
			unsigned long top,
			struct smc_result *res);

void smc_rtt_set_ripas(unsigned long rd_addr,
			unsigned long rec_addr,
			unsigned long base,
			unsigned long top,
			struct smc_result *res);

void smc_rtt_set_s2ap(unsigned long rd_addr, unsigned long rec_addr,
		      unsigned long base, unsigned long top,
		      struct smc_result *res);

void smc_rtt_aux_map_protected(unsigned long rd_addr,
			       unsigned long map_addr,
			       unsigned long index,
			       struct smc_result *res);

void smc_rtt_aux_map_unprotected(unsigned long rd_addr,
				 unsigned long map_addr,
				 unsigned long index,
				 struct smc_result *res);

void smc_rtt_aux_unmap_protected(unsigned long rd_addr,
				 unsigned long unmap_addr,
				 unsigned long index,
				 struct smc_result *res);

void smc_rtt_aux_unmap_unprotected(unsigned long rd_addr,
				   unsigned long unmap_addr,
				   unsigned long index,
				   struct smc_result *res);

unsigned long smc_vdev_map(unsigned long rd_addr,
			   unsigned long vdev_addr,
			   unsigned long map_addr,
			   unsigned long ulevel,
			   unsigned long dev_mem_addr);

void smc_vdev_unmap(unsigned long rd_addr,
		   unsigned long vdev_addr,
		   unsigned long map_addr,
		   unsigned long ulevel,
		   struct smc_result *res);

unsigned long smc_pdev_create(unsigned long pdev_addr,
			      unsigned long pdev_params_addr);

void smc_pdev_aux_count(unsigned long flags, struct smc_result *res);

unsigned long smc_pdev_communicate(unsigned long pdev_addr,
				   unsigned long dev_comm_data_addr);

void smc_pdev_get_state(unsigned long pdev_addr, struct smc_result *res);

unsigned long smc_pdev_set_pubkey(unsigned long pdev_addr,
				  unsigned long pubkey_params_addr);

unsigned long smc_pdev_abort(unsigned long pdev_addr);

unsigned long smc_pdev_stop(unsigned long pdev_addr);

unsigned long smc_pdev_destroy(unsigned long pdev_addr);

unsigned long smc_pdev_ide_key_refresh(unsigned long pdev_addr, unsigned long coh);

unsigned long smc_pdev_ide_reset(unsigned long pdev_addr);

unsigned long smc_mec_set_shared(unsigned long mecid);

unsigned long smc_mec_set_private(unsigned long mecid);

unsigned long smc_vdev_create(unsigned long rd_addr, unsigned long pdev_addr,
			      unsigned long vdev_addr,
			      unsigned long vdev_params_addr);

unsigned long smc_vdev_complete(unsigned long rec_addr, unsigned long vdev_addr);

unsigned long smc_vdev_communicate(unsigned long rd_addr,
				   unsigned long pdev_addr,
				   unsigned long vdev_addr,
				   unsigned long dev_comm_data_addr);

void smc_vdev_get_state(unsigned long vdev_addr, struct smc_result *res);

unsigned long smc_vdev_unlock(unsigned long rd_addr, unsigned long pdev_addr,
				unsigned long vdev_addr);

void smc_vdev_aux_count(unsigned long pdev_flags, unsigned long vdev_flags,
			struct smc_result *res);

unsigned long smc_vdev_abort(unsigned long vdev_addr);

unsigned long smc_vdev_destroy(unsigned long rd_addr, unsigned long pdev_addr,
			       unsigned long vdev_addr);
unsigned long smc_vdev_get_interface_report(unsigned long rd_addr, unsigned long pdev_addr,
					    unsigned long vdev_addr);
unsigned long smc_vdev_get_measurements(unsigned long rd_addr, unsigned long pdev_addr,
					unsigned long vdev_addr, unsigned long params_addr);
unsigned long smc_vdev_lock(unsigned long rd_addr, unsigned long pdev_addr,
					unsigned long vdev_addr);
unsigned long smc_vdev_start(unsigned long rd_addr, unsigned long pdev_addr,
					unsigned long vdev_addr);

#endif /* SMC_HANDLER_H */
