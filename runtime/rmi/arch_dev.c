/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <granule.h>
#include <smc-handler.h>
#include <smc-rmi.h>
#include <smc.h>

static bool arch_dev_range_inputs_valid(unsigned long rd_addr,
					unsigned long dev_addr,
					unsigned long base,
					unsigned long top)
{
	return GRANULE_ALIGNED(rd_addr) && GRANULE_ALIGNED(dev_addr) &&
	       GRANULE_ALIGNED(base) && GRANULE_ALIGNED(top) && (base < top);
}

/* cppcheck-suppress misra-c2012-8.7 */
void smc_rtt_arch_dev_map(unsigned long rd_addr, unsigned long dev_addr,
			  unsigned long base, unsigned long top,
			  struct smc_result *res)
{
	struct granule *g_rd;
	struct granule *g_dev;

	if (!arch_dev_range_inputs_valid(rd_addr, dev_addr, base, top)) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	if (!find_lock_two_granules(rd_addr, GRANULE_STATE_RD, &g_rd,
				    dev_addr, GRANULE_STATE_VDEV, &g_dev)) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	/*
	 * TODO: Check FEAT_VSMMU, VSMMU ownership, protected IPA bounds,
	 * output address bounds, and the RTT entry state, size and RIPAS
	 * required by the map operation.
	 */

	/* To be implemented: create the architectural device RTT mappings. */
	res->x[0] = RMI_SUCCESS;
	/* To be implemented: return the actual top IPA that was processed. */
	res->x[1] = 0UL;

	granule_unlock(g_dev);
	granule_unlock(g_rd);
}

/* cppcheck-suppress misra-c2012-8.7 */
void smc_rtt_arch_dev_unmap(unsigned long rd_addr, unsigned long dev_addr,
			    unsigned long base, unsigned long top,
			    struct smc_result *res)
{
	struct granule *g_rd;
	struct granule *g_dev;

	if (!arch_dev_range_inputs_valid(rd_addr, dev_addr, base, top)) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	if (!find_lock_two_granules(rd_addr, GRANULE_STATE_RD, &g_rd,
				    dev_addr, GRANULE_STATE_VDEV, &g_dev)) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	/*
	 * TODO: Check VSMMU ownership, protected IPA bounds, and the RTT entry
	 * address, state and size required by the unmap operation.
	 */

	/* To be implemented: remove the architectural device RTT mappings. */
	res->x[0] = RMI_SUCCESS;
	/* To be implemented: return the actual top IPA that was processed. */
	res->x[1] = 0UL;

	granule_unlock(g_dev);
	granule_unlock(g_rd);
}
