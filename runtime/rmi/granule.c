/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch_features.h>
#include <buffer.h>
#include <debug.h>
#include <dev_granule.h>
#include <granule.h>
#include <mec.h>
#include <rmm_el3_ifc.h>
#include <smc-handler.h>
#include <smc-rmi.h>
#include <smc.h>

static unsigned long dev_granule_delegate(unsigned long addr)
{
	enum dev_coh_type type;

	/* Try to find device granule */
	struct dev_granule *g = find_dev_granule(addr, &type);

	if (g == NULL) {
		return RMI_ERROR_INPUT;
	}

	if (!dev_granule_lock_on_state_match(g, DEV_GRANULE_STATE_NS)) {
		return RMI_ERROR_INPUT;
	}

	/*
	 * It is possible that the device granule was delegated by EL3
	 * to Secure on request from SPM and hence this request can fail.
	 */
	if (rmm_el3_ifc_gtsi_delegate(addr) != SMC_SUCCESS) {
		dev_granule_unlock(g);
		return RMI_ERROR_INPUT;
	}

	dev_granule_set_state(g, DEV_GRANULE_STATE_DELEGATED);
	dev_granule_unlock(g);
	return RMI_SUCCESS;
}

static unsigned long dev_granule_undelegate(unsigned long addr)
{
	enum dev_coh_type type;

	/* Try to find device granule */
	struct dev_granule *g = find_dev_granule(addr, &type);

	if (g == NULL) {
		return RMI_ERROR_INPUT;
	}

	if (!dev_granule_lock_on_state_match(g, DEV_GRANULE_STATE_DELEGATED)) {
		return RMI_ERROR_INPUT;
	}

	/*
	 * A delegated device granule should only be undelegated on request from RMM.
	 * If this call fails, we have an unrecoverable error in EL3/RMM.
	 */
	if (rmm_el3_ifc_gtsi_undelegate(addr) != SMC_SUCCESS) {
		ERROR("Granule 0x%lx undelegate call failed\n", addr);
		dev_granule_unlock(g);
		panic();
	}

	dev_granule_set_state(g, DEV_GRANULE_STATE_NS);
	dev_granule_unlock(g);
	return RMI_SUCCESS;
}

unsigned long smc_granule_delegate(unsigned long addr)
{
	/* Try to find memory granule */
	struct granule *g = find_granule(addr);

	if (g != NULL) {
		if (!granule_lock_on_state_match(g, GRANULE_STATE_NS)) {
			return RMI_ERROR_INPUT;
		}

		/*
		 * It is possible that the memory granule was delegated by EL3
		 * to Secure on request from SPM and hence this request can fail.
		 */
		if (rmm_el3_ifc_gtsi_delegate(addr) != SMC_SUCCESS) {
			granule_unlock(g);
			return RMI_ERROR_INPUT;
		}

		/*
		 * The granule will be initialized later when the granule transitions
		 * to other states. RMM does not scrub here as the initilization makes
		 * the scrub redundant.
		 */
		granule_unlock_transition(g, GRANULE_STATE_DELEGATED);

		return RMI_SUCCESS;
	}

	/* Delegate device granule */
	return dev_granule_delegate(addr);
}

/* @TODO Enhance implementation later */
void smc_granule_range_delegate(unsigned long addr,
				unsigned long end_addr,
				struct smc_result *res)
{
	res->x[0] = RMI_ERROR_INPUT;
	res->x[1] = addr;

	/* Simplified implementation delegates exactly one granule. */
	if (!ALIGNED(addr, GRANULE_SIZE) ||
	    !ALIGNED(end_addr, GRANULE_SIZE) ||
	    (end_addr < (addr + GRANULE_SIZE))) {
		return;
	}

	res->x[0] = smc_granule_delegate(addr);
	if (res->x[0] == RMI_SUCCESS) {
		res->x[1] = addr + GRANULE_SIZE;
	}
}

/* @TODO Enhance implementation later */
void smc_granule_range_undelegate(unsigned long addr,
				  unsigned long end_addr,
				  struct smc_result *res)
{
	res->x[0] = RMI_ERROR_INPUT;
	res->x[1] = addr;

	/* Simplified implementation undelegates exactly one granule. */
	if (!ALIGNED(addr, GRANULE_SIZE) ||
	    !ALIGNED(end_addr, GRANULE_SIZE) ||
	    (end_addr < (addr + GRANULE_SIZE))) {
		return;
	}

	res->x[0] = smc_granule_undelegate(addr);
	if (res->x[0] == RMI_SUCCESS) {
		res->x[1] = addr + GRANULE_SIZE;
	}
}

unsigned long smc_granule_undelegate(unsigned long addr)
{
	/* Try to find memory granule */
	struct granule *g = find_granule(addr);

	if (g != NULL) {
		if (!granule_lock_on_state_match(g, GRANULE_STATE_DELEGATED)) {
			return RMI_ERROR_INPUT;
		}

		/* Scrub any Realm world data before returning granule to NS */
		buffer_granule_sanitize(g);

		/* DCCI PoPA as part of undelegate in EL3 will flush to PoE */

		/*
		 * A delegated memory granule should only be undelegated on request from RMM.
		 * If this call fails, we have an unrecoverable error in EL3/RMM.
		 */
		if (rmm_el3_ifc_gtsi_undelegate(addr) != SMC_SUCCESS) {
			ERROR("Granule 0x%lx undelegate call failed\n", addr);
			granule_unlock(g);
			panic();
		}

		granule_unlock_transition(g, GRANULE_STATE_NS);
		return RMI_SUCCESS;
	}

	/* Undelegate device granule */
	return dev_granule_undelegate(addr);
}

/*
 * For this implementation, the only supported system granularity is
 * 4KB, thus the valid tracking size can only be 1GB.
 *
 * @TODO.This needs to be made dynamic later.
 */
/* RMI interface defined value for the Granule and TrackingRegion Sizes we use */
#define RMI_GRANULE_SIZE		RMI_GRANULE_SIZE_4KB
#define RMI_TRACKING_REGION_SIZE	RMI_GRAN_4KB_TRACKING_REGION_SIZE_1GB
/* Internal only symbol for the size */
#define RMM_INTERNAL_TRACKING_REGION_SIZE	(1UL << 30UL) /* 1GB */

void smc_granule_tracking_get(unsigned long addr,
			      struct smc_result *res)
{
	struct granule *g;
	struct dev_granule *dg;
	enum dev_coh_type type;
	unsigned int pasz = arch_feat_get_pa_width();
	unsigned long max_pa = ((1UL << pasz) - 1UL);

	res->x[0] = RMI_ERROR_INPUT;

	/* Reject addresses beyond implemented PA size */
	if (addr > max_pa) {
		return;
	}

	if (!ALIGNED(addr, RMM_INTERNAL_TRACKING_REGION_SIZE)) {
		return;
	}

	g = find_granule(addr);
	if (g != NULL) {
		res->x[0] = RMI_SUCCESS;
		res->x[1] = RMI_MEM_CATEGORY_CONVENTIONAL;
		res->x[2] = RMI_TRACKING_FINE;
		return;
	}

	/* Try to find device granule */
	dg = find_dev_granule(addr, &type);
	if (dg != NULL) {
		res->x[0] = RMI_SUCCESS;
		res->x[2] = RMI_TRACKING_FINE;
		res->x[1] = (type == DEV_MEM_NON_COHERENT) ?
				RMI_MEM_CATEGORY_DEV_NCOH :
				RMI_MEM_CATEGORY_DEV_COH;
		return;
	}

	/*
	 * Aligned region with no granule or device mapped: report
	 * that the region is valid but currently untracked.
	 */
	res->x[0] = RMI_SUCCESS;
	res->x[1] = RMI_MEM_CATEGORY_CONVENTIONAL;
	res->x[2] = RMI_TRACKING_NONE;
}

unsigned long smc_rmm_config_set(unsigned long config_ptr)
{
	struct rmi_rmm_config cfg = { 0 };

	if (!ALIGNED(config_ptr, SZ_4K)) {
		return RMI_ERROR_INPUT;
	}

	if (!ns_buffer_read_early(config_ptr, sizeof(cfg), &cfg)) {
		return RMI_ERROR_INPUT;
	}

	/* TODO: At the moment, only 4KB granularity size is supported */
	if ((cfg.rmi_granule_size != RMI_GRANULE_SIZE) ||
	    (cfg.tracking_region_size != RMI_TRACKING_REGION_SIZE)) {
		return RMI_ERROR_INPUT;
	}

	return RMI_SUCCESS;
}

unsigned long smc_rmm_config_get(unsigned long config_ptr)
{
	struct rmi_rmm_config cfg = { 0 };

	if (!ALIGNED(config_ptr, SZ_4K)) {
		return RMI_ERROR_INPUT;
	}

	cfg.rmi_granule_size = RMI_GRANULE_SIZE;
	cfg.tracking_region_size = RMI_TRACKING_REGION_SIZE;

	if (!ns_buffer_write_early(config_ptr, sizeof(cfg), &cfg)) {
		return RMI_ERROR_INPUT;
	}

	return RMI_SUCCESS;
}

/* FIXME: This should come from FIRME ABI */
#define RMM_L0GPTSZ	SZ_1G
void smc_gpt_l1_create(unsigned long addr, struct smc_result *res)
{
	if (!ALIGNED(addr, RMM_L0GPTSZ)) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	/*
	 * FIXME:  We have statically created L1 GPTs, thus return ERROR_GPT.
	 * For Dynamic GPT, we need the SRO and request memory
	 * from the Host, once we have walked the GPT and if a table is
	 * really required.
	 */
	res->x[0] = RMI_ERROR_GPT;
}
