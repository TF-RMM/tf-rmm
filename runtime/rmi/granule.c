/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <buffer.h>
#include <debug.h>
#include <granule.h>
#include <rmm_el3_ifc.h>
#include <smc-handler.h>
#include <smc-rmi.h>
#include <smc.h>

unsigned long smc_granule_delegate(unsigned long addr)
{
	struct granule *g;

	g = find_lock_granule(addr, GRANULE_STATE_NS);
	if (g == NULL) {
		return RMI_ERROR_INPUT;
	}

	/*
	 * It is possible that the granule was delegated by EL3
	 * to Secure on request from SPM and hence this request can fail.
	 */
	if (rmm_el3_ifc_gtsi_delegate(addr) != SMC_SUCCESS) {
		granule_unlock(g);
		return RMI_ERROR_INPUT;
	}

	granule_set_state(g, GRANULE_STATE_DELEGATED);
	buffer_granule_memzero(g, SLOT_DELEGATED);

	granule_unlock(g);
	return RMI_SUCCESS;
}

unsigned long smc_granule_undelegate(unsigned long addr)
{
	struct granule *g;

	g = find_lock_granule(addr, GRANULE_STATE_DELEGATED);
	if (g == NULL) {
		return RMI_ERROR_INPUT;
	}

	/*
	 * A delegated granule should only be undelegated on request from RMM.
	 * If this call fails, we have an unrecoverable error in EL3/RMM.
	 */
	if (rmm_el3_ifc_gtsi_undelegate(addr) != SMC_SUCCESS) {
		ERROR("Granule 0x%lx undelegate call failed\n", addr);
		granule_unlock(g);
		panic();
	}

	granule_set_state(g, GRANULE_STATE_NS);

	granule_unlock(g);
	return RMI_SUCCESS;
}
