/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch_features.h>
#include <assert.h>
#include <buffer.h>
#include <glob_data.h>
#include <granule_sro.h>
#include <memory.h>
#include <smc-handler.h>
#include <smc-rmi.h>
#include <smc.h>
#include <status.h>
#include <stdbool.h>
#include <tracking_region.h>

/*
 * Validate a Host range and start delegation at its active tracking size.
 * Both addresses must be Granule aligned and define a non-empty range. @res
 * receives the RMI status and progress address, or an SRO handle when the
 * operation must resume. The caller must hold no Granule lock.
 */
void smc_granule_range_delegate(unsigned long addr,
				unsigned long end_addr,
				struct smc_result *res)
{
	res->x[0] = RMI_ERROR_INPUT;
	res->x[1] = addr;

	if (!ALIGNED(addr, GRANULE_SIZE) ||
	    !ALIGNED(end_addr, GRANULE_SIZE) ||
	    (end_addr <= addr)) {
		return;
	}

	granule_delegate_start(addr, end_addr, res);
}

/*
 * Validate a Host range and begin undelegating a fine run or coarse unit.
 * Both addresses must be Granule aligned and define a non-empty range. @res
 * receives the RMI status and committed range boundary, or an SRO handle when
 * sanitization or EL3 progress must resume. The caller must hold no Granule lock.
 */
void smc_granule_range_undelegate(unsigned long addr,
				  unsigned long end_addr,
				  struct smc_result *res)
{
	res->x[0] = RMI_ERROR_INPUT;
	res->x[1] = addr;

	if (!ALIGNED(addr, GRANULE_SIZE) ||
	    !ALIGNED(end_addr, GRANULE_SIZE) ||
	    (end_addr <= addr)) {
		return;
	}

	granule_undelegate_start(addr, end_addr, res);
}

/* The implementation currently supports only the 4 KiB RMI Granule size. */
#define RMI_GRANULE_SIZE		RMI_GRANULE_SIZE_4KB

/* Decode the tracking-region size for a 4 KiB RMI Granule. */
static bool rmi_tracking_region_size_decode(unsigned long encoded,
					    unsigned long *size)
{
	assert(size != NULL);

	switch (encoded) {
	case RMI_GRAN_4KB_TRACKING_REGION_SIZE_2MB:
		*size = TRACKING_REGION_MIN_SIZE;
		return true;
	case RMI_GRAN_4KB_TRACKING_REGION_SIZE_1GB:
		*size = TRACKING_REGION_MAX_SIZE;
		return true;
	default:
		return false;
	}
}

/* Encode the configured size for the Beta 3 RmiRmmConfig structure. */
static unsigned long rmi_tracking_region_size_encode(unsigned long size)
{
	if (size == TRACKING_REGION_MIN_SIZE) {
		return RMI_GRAN_4KB_TRACKING_REGION_SIZE_2MB;
	}

	assert(size == TRACKING_REGION_MAX_SIZE);
	return RMI_GRAN_4KB_TRACKING_REGION_SIZE_1GB;
}

/*
 * Query the longest prefix of [@base, @top) with one memory category and
 * tracking state. Return the RMI status and, on success, category, state and
 * prefix end in @res. The tracking-info helper serializes each region query.
 * @base and @top must be Granule-aligned and define a non-empty range.
 * The exclusive @top may equal the size of the PA space.
 */
void smc_granule_tracking_get(unsigned long base,
			      unsigned long top,
			      struct smc_result *res)
{
	unsigned int pasz = arch_feat_get_pa_width();
	unsigned long pa_size = 1UL << pasz;
	unsigned long category;
	unsigned long cursor;
	unsigned long region_top;
	enum tr_state state;

	res->x[0] = RMI_ERROR_INPUT;

	if ((base > pa_size) || (top > pa_size) || (base >= top) ||
	    !GRANULE_ALIGNED(base) || !GRANULE_ALIGNED(top)) {
		return;
	}

	if (!tracking_region_get_info(base, top, &category, &state,
				      &region_top)) {
		return;
	}

	cursor = region_top;
	while (cursor < top) {
		unsigned long next_category;
		unsigned long next_top;
		enum tr_state next_state;

		if (!tracking_region_get_info(cursor, top, &next_category,
					      &next_state, &next_top) ||
		    (next_category != category) || (next_state != state)) {
			break;
		}
		cursor = next_top;
	}

	res->x[0] = RMI_SUCCESS;
	res->x[1] = category;
	res->x[2] = (unsigned long)state;
	res->x[3] = cursor;
}

void smc_granule_tracking_set(unsigned long addr,
			      unsigned long category,
			      unsigned long state,
			      struct smc_result *res)
{
	unsigned int pasz = arch_feat_get_pa_width();
	unsigned long max_pa = ((1UL << pasz) - 1UL);
	unsigned long region_size = tracking_region_get_size();

	res->x[0] = RMI_ERROR_INPUT;

	if ((addr > max_pa) ||
	    ((addr & (region_size - 1UL)) != 0UL)) {
		return;
	}

	/* TODO: Intermediate tracking needs to be implemented later */
	if ((state == RMI_TRACKING_RESERVED) ||
	    (state == RMI_TRACKING_INTERMEDIATE) ||
	    (state > RMI_TRACKING_INTERMEDIATE)) {
		return;
	}

#ifdef RMM_ALLOC_TRACKING_DATA
	res->x[0] = tracking_region_set_tracking(addr, category, state);
#else
	tracking_region_set_sro(addr, category, state, res);
#endif
}

/*
 * Configure Granule tracking from the RmiRmmConfig structure at @config_ptr.
 * The structure must start at an aligned Non-secure granule and contain
 * supported Granule and tracking-region sizes. An INIT-to-INTERMEDIATE claim
 * serializes index rebuilding with configuration and activation on other PEs;
 * INIT is restored before return. @res receives the RMI command status.
 */
void smc_rmm_config_set(unsigned long config_ptr, struct smc_result *res)
{
	struct rmi_rmm_config cfg = { 0 };
	unsigned long tracking_region_size;
	bool transitioned;
	int ret;

	if ((config_ptr == 0UL) || !ALIGNED(config_ptr, SZ_4K)) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	if (!ns_buffer_read_addr(SLOT_NS, config_ptr, 0U,
				 sizeof(cfg), &cfg)) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	if ((cfg.rmi_granule_size != RMI_GRANULE_SIZE) ||
	    !rmi_tracking_region_size_decode(cfg.tracking_region_size,
					     &tracking_region_size)) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	/* Serialize index rebuilding with other configuration and activation calls. */
	if (!glob_data_transition_rmm_state(RMM_STATE_INIT,
					   RMM_STATE_INTERMEDIATE)) {
		res->x[0] = RMI_ERROR_GLOBAL;
		return;
	}

	ret = tracking_region_configure(tracking_region_size);
	transitioned = glob_data_transition_rmm_state(RMM_STATE_INTERMEDIATE,
						      RMM_STATE_INIT);
	assert(transitioned);
	(void)transitioned;
	if (ret != 0) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	res->x[0] = RMI_SUCCESS;
}

/*
 * Return the supported Granule size and configured tracking-region size at
 * @config_ptr. The output structure must start at an aligned Non-secure
 * granule. Read the configured size under the global layout lock and release
 * it before writing the output. @res receives the RMI command status.
 */
void smc_rmm_config_get(unsigned long config_ptr, struct smc_result *res)
{
	struct rmi_rmm_config cfg = { 0 };

	if ((config_ptr == 0UL) || !ALIGNED(config_ptr, SZ_4K)) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	cfg.rmi_granule_size = RMI_GRANULE_SIZE;
	cfg.tracking_region_size = rmi_tracking_region_size_encode(
					tracking_region_get_rmm_config_size());

	if (!ns_buffer_write_addr(SLOT_NS, config_ptr, 0U,
				  sizeof(cfg), &cfg)) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	res->x[0] = RMI_SUCCESS;
}

/* FIXME: This should come from FIRME ABI */
#define RMM_L0GPTSZ	SZ_1G

static bool gpt_addr_is_valid(unsigned long addr)
{
	unsigned int pasz = arch_feat_get_pa_width();
	unsigned long max_pa = ((1UL << pasz) - 1UL);

	return (addr <= max_pa) && ALIGNED(addr, RMM_L0GPTSZ);
}

void smc_gpt_l1_create(unsigned long addr, struct smc_result *res)
{
	if (!gpt_addr_is_valid(addr)) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	/*
	 * TODO: Check that the PAR has a host-created L1GPT.
	 */
	/*
	 * FIXME:  We have statically created L1 GPTs, thus return RMI_ERROR_GLOBAL.
	 * For Dynamic GPT, we need the SRO and request memory
	 * from the Host, once we have walked the GPT and if a table is
	 * really required.
	 */
	/* The existing L1 table is referenced by the L0 entry for @addr. */
	res->x[0] = RMI_ERROR_GLOBAL;
}

void smc_gpt_l1_destroy(unsigned long addr, struct smc_result *res)
{
	if (!gpt_addr_is_valid(addr)) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	/*
	 * TODO: Check that the PAR has a host-created L1GPT.
	 * TODO: Check that all entries in the L1GPT have the same GPI.
	 * To be implemented: destroy the L1GPT using the SRO reclaim flow.
	 */
	res->x[0] = RMI_ERROR_GLOBAL;
}

/*
 * Report whether the GPT L0 range at @base covers platform-managed memory.
 * @base and @top must describe a non-empty, L0-aligned range within the PA
 * width. On success, @res identifies the next L0 boundary and whether that
 * range is platform or reserved memory.
 */
void smc_gpt_info(unsigned long base, unsigned long top,  struct smc_result *res)
{
	unsigned int pasz = arch_feat_get_pa_width();
	unsigned long max_pa = ((1UL << pasz) - 1UL);
	unsigned long category;
	unsigned long region_top;
	enum tr_state state;

	if (!ALIGNED(base, RMM_L0GPTSZ) || !ALIGNED(top, RMM_L0GPTSZ) ||
	    (base >= max_pa) || (top > max_pa) || (top <= base)) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	res->x[1] = base + RMM_L0GPTSZ;

	if (!tracking_region_get_info(base, res->x[1], &category, &state,
				      &region_top)) {
		res->x[0] = RMI_ERROR_INPUT;
		return;
	}

	res->x[0] = RMI_SUCCESS;

	/* All device and DRAM memory is statically covered for now. */
	if (category != RMI_MEM_CATEGORY_NONE) {
		res->x[2] = RMI_GPT_PAR_PLAT;
	} else {
		res->x[2] = RMI_GPT_PAR_RESERVED;
	}
}
