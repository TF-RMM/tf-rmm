/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <granule.h>
#include <smc-handler.h>
#include <smc-rmi.h>
#include <smc.h>

/* Return whether the object PAs and non-empty IPA range are Granule aligned. */
static bool arch_dev_range_inputs_valid(unsigned long rd_addr,
					unsigned long dev_addr,
					unsigned long base,
					unsigned long top)
{
	return GRANULE_ALIGNED(rd_addr) && GRANULE_ALIGNED(dev_addr) &&
	       GRANULE_ALIGNED(base) && GRANULE_ALIGNED(top) && (base < top);
}

/*
 * Validate the RD and VDEV PAs and the half-open IPA range [base, top) for
 * the architectural-device map stub. No mappings are created yet.
 * Return the input or tracking error in res->x[0], or RMI_SUCCESS with a
 * placeholder top IPA in res->x[1]. Acquire fine granules in global lock
 * order and release all locks before returning.
 */
/* cppcheck-suppress misra-c2012-8.7 */
void smc_rtt_arch_dev_map(unsigned long rd_addr, unsigned long dev_addr,
			  unsigned long base, unsigned long top,
			  struct smc_result *res)
{
	struct granule *g_rd;
	struct granule *g_dev;
	unsigned long ret;

	if (!arch_dev_range_inputs_valid(rd_addr, dev_addr, base, top)) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	ret = tr_find_lock_two_fine_granules(rd_addr, GRANULE_STATE_RD, &g_rd,
					   dev_addr, GRANULE_STATE_VDEV, &g_dev);
	if (ret != RMI_SUCCESS) {
		res->x[0] = ret;
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

/*
 * Validate the RD and VDEV PAs and the half-open IPA range [base, top) for
 * the architectural-device unmap stub. No mappings are removed yet.
 * Return the input or tracking error in res->x[0], or RMI_SUCCESS with a
 * placeholder top IPA in res->x[1]. Acquire fine granules in global lock
 * order and release all locks before returning.
 */
/* cppcheck-suppress misra-c2012-8.7 */
void smc_rtt_arch_dev_unmap(unsigned long rd_addr, unsigned long dev_addr,
			    unsigned long base, unsigned long top,
			    struct smc_result *res)
{
	struct granule *g_rd;
	struct granule *g_dev;
	unsigned long ret;

	if (!arch_dev_range_inputs_valid(rd_addr, dev_addr, base, top)) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	ret = tr_find_lock_two_fine_granules(rd_addr, GRANULE_STATE_RD, &g_rd,
					   dev_addr, GRANULE_STATE_VDEV, &g_dev);
	if (ret != RMI_SUCCESS) {
		res->x[0] = ret;
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
