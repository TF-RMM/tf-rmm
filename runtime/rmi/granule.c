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

#ifdef RMM_V1_1
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
#else
static unsigned long dev_granule_delegate(unsigned long addr)
{
	(void)addr;

	return RMI_ERROR_INPUT;
}

static unsigned long dev_granule_undelegate(unsigned long addr)
{
	(void)addr;

	return RMI_ERROR_INPUT;
}
#endif /* RMM_V1_1 */

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

unsigned long smc_granule_undelegate(unsigned long addr)
{
	/* Try to find memory granule */
	struct granule *g = find_granule(addr);

	if (g != NULL) {
		if (!granule_lock_on_state_match(g, GRANULE_STATE_DELEGATED)) {
			return RMI_ERROR_INPUT;
		}

		/* Scrub any Realm world data before returning granule to NS */
#if (RMM_MEM_SCRUB_METHOD == 1)
		/* Any Slot which uses RMM MECID will do, use SLOT_RD for now */
		void *buf = buffer_granule_map(g, SLOT_RD);
		granule_sanitize_1_mapped(buf);
		buffer_unmap(buf);
#elif (RMM_MEM_SCRUB_METHOD == 2)
		/* Change to the reserved Scrub MECID */
		mec_init_scrub_mecid_s1();
		/* A Slot which uses Realm MECID needs to be used */
		void *buf = buffer_granule_map(g, SLOT_REALM);
		granule_sanitize_mapped(buf);
		buffer_unmap(buf);
		mec_reset_realm_mecid();
#else
		/* Any Slot which uses RMM MECID will do, use SLOT_RD for now */
		void *buf = buffer_granule_map(g, SLOT_RD);
		granule_sanitize_mapped(buf);
		buffer_unmap(buf);
#endif
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
