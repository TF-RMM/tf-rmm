/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <assert.h>
#include <debug.h>
#include <glob_data.h>
#include <mapped_va_arch.h>
#include <rmm_el3_ifc.h>
#include <smc-rmi.h>
#include <smmuv3.h>
#include <spinlock.h>
#include <sro_context.h>
#include <tracking_region.h>
#include <xlat_low_va.h>

static struct glob_data *glob;
static spinlock_t rmm_state_lock;

uintptr_t glob_data_get_smmu_driv_hdl_va(size_t *alloc_size)
{
	if (glob == NULL) {
		ERROR("Global data not initialized\n");
		return 0UL;
	}

	if (alloc_size != NULL) {
		*alloc_size = glob->smmu_driv_hdl_sz;
	}

	return MAPPED_VA_ARCH(glob->smmu_driv_hdl_va, glob->smmu_driv_hdl_pa);
}

uintptr_t glob_data_get_vmids_va(size_t *alloc_size)
{
	if (glob == NULL) {
		ERROR("Global data not initialized\n");
		return 0UL;
	}

	if (alloc_size != NULL) {
		*alloc_size = VMID_ARRAY_LONG_SIZE * sizeof(unsigned long);
	}

	return (uintptr_t)glob->vmid_bitmap;
}

uintptr_t glob_data_get_mec_state_va(size_t *alloc_size)
{
	if (glob == NULL) {
		ERROR("Global data not initialized\n");
		return 0UL;
	}

	if (alloc_size != NULL) {
		*alloc_size = sizeof(struct mec_state_s);
	}
	return (uintptr_t)&glob->mec_state;
}

uintptr_t glob_data_get_tracking_region_data_va(size_t *alloc_size)
{
	if (glob == NULL) {
		ERROR("Global data not initialized\n");
		return 0UL;
	}

	if (alloc_size != NULL) {
		*alloc_size = glob->tracking_region_data_sz;
	}

	return MAPPED_VA_ARCH(glob->tracking_region_data_va,
			      glob->tracking_region_data_pa);
}

/*
 * Return a synchronized snapshot of the global RMM lifecycle state. The
 * state-transition lock is held only for the read and is not retained by the
 * caller.
 */
enum rmm_state glob_data_get_rmm_state(void)
{
	enum rmm_state state;

	if (glob == NULL) {
		ERROR("Global data not initialized\n");
		return RMM_STATE_INIT;
	}

	spinlock_acquire(&rmm_state_lock);
	state = glob->rmm_state;
	spinlock_release(&rmm_state_lock);

	return state;
}

/*
 * Atomically change the global RMM state when its current value is @expected.
 * The state-transition lock serializes lifecycle claims but is released before
 * the caller performs the work protected by the claimed state. Return true
 * when the transition is committed, or false on a state mismatch or when
 * global data has not been initialized.
 */
bool glob_data_transition_rmm_state(enum rmm_state expected,
				    enum rmm_state new_state)
{
	bool transitioned = false;

	if (glob == NULL) {
		ERROR("Global data not initialized\n");
		return false;
	}

	spinlock_acquire(&rmm_state_lock);
	if (glob->rmm_state == expected) {
		glob->rmm_state = new_state;
		transitioned = true;
	}
	spinlock_release(&rmm_state_lock);

	return transitioned;
}

uintptr_t glob_data_get_sro_ctx_va(size_t *alloc_size)
{
	if (glob == NULL) {
		ERROR("Global data not initialized\n");
		return 0UL;
	}

	if (alloc_size != NULL) {
		*alloc_size = glob->sro_ctxs_sz;
	}

	return MAPPED_VA_ARCH(glob->sro_ctxs_va, glob->sro_ctxs_pa);

}

unsigned long glob_data_get_fw_img_sequence(void)
{
	if (glob == NULL) {
		ERROR("Global data not initialized\n");
		return 0UL;
	}

	return glob->fw_img_sequence;
}

uintptr_t glob_data_init(struct glob_data *gl)
{
	int ret;
	uintptr_t buf_pa, va;
	struct glob_data *new_gl;
	struct smmu_list *plat_smmu_list;

	if (glob != NULL) {
		return glob->glob_data_pa;
	}

	if (gl != NULL) {
		INFO("Reusing global data already allocated by previous RMM\n");
		/* NOLINTNEXTLINE(google-readability-casting) */
		glob = (struct glob_data *)MAPPED_VA_ARCH(xlat_low_va_get_dyn_va_base(), gl);

		assert(glob->glob_data_pa == (uintptr_t)gl);
		if (glob->version != GLOBDATA_VERSION) {
			ERROR("Incompatible global data version: %lu\n",
			      glob->version);
			glob = NULL;
			return 0UL;
		}

		/*
		 * Copy Low VA information since some static VA regions
		 * are different between RMM instances.
		 */
		glob->low_va_info = *(xlat_get_low_va_info());

		/* Flush in case any CPUs access this with MMU off */
		flush_dcache_range((uintptr_t)&glob->low_va_info,
			sizeof(struct xlat_low_va_info));

		/* Increment firmware activation sequence */
		glob->fw_img_sequence++;

		return (uintptr_t)gl;
	}

	/* Allocate memory and VA for glob_data */
	ret = rmm_el3_ifc_reserve_memory(GLOB_DATA_MAX_SIZE, 0, GRANULE_SIZE, &buf_pa);
	if (ret != 0) {
		ERROR("Failed to reserve memory for glob_data\n");
		return 0UL;
	}

	va = xlat_low_va_map(GLOB_DATA_MAX_SIZE, MT_RW_DATA | MT_REALM, buf_pa, true);
	if (va == 0U) {
		ERROR("Failed to allocate VA for glob_data\n");
		return 0UL;
	}

	assert(va == xlat_low_va_get_dyn_va_base());

	/* Initialize the glob_data */
	new_gl = (struct glob_data *)MAPPED_VA_ARCH(va, buf_pa);
	new_gl->version = GLOBDATA_VERSION;
	/* Copy Low VA information */
	new_gl->low_va_info = *(xlat_get_low_va_info());

	/* Initialize RMM state */
	new_gl->rmm_state = RMM_STATE_INIT;

	new_gl->glob_data_pa = buf_pa;
	new_gl->glob_data_va = va;
	new_gl->glob_data_size = GLOB_DATA_MAX_SIZE;

	/* Allocate struct tracking_region_data, which persists across LFA. */
	new_gl->tracking_region_data_sz = TRACKING_REGION_DATA_SIZE;
	ret = rmm_el3_ifc_reserve_memory(new_gl->tracking_region_data_sz, 0,
					 GRANULE_SIZE,
					 &new_gl->tracking_region_data_pa);
	if (ret != 0) {
		ERROR("Failed to reserve memory for struct tracking_region_data\n");
		return 0UL;
	}

	new_gl->tracking_region_data_va = xlat_low_va_map(
					new_gl->tracking_region_data_sz,
					MT_RW_DATA | MT_REALM,
					new_gl->tracking_region_data_pa, true);
	if (new_gl->tracking_region_data_va == 0U) {
		ERROR("Failed to map struct tracking_region_data\n");
		return 0UL;
	}

	/* Set up SMMU layout */
	ret = rmm_el3_ifc_get_cached_smmu_list_pa(&plat_smmu_list);
	if (ret == 0) {
		new_gl->smmu_driv_hdl_va = smmuv3_driver_setup(
						plat_smmu_list,
						&new_gl->smmu_driv_hdl_pa,
						&new_gl->smmu_driv_hdl_sz);
		if (new_gl->smmu_driv_hdl_va == 0UL) {
			ERROR("Failed to set up SMMU driver\n");
			return 0UL;
		}
	} else {
		INFO("No SMMU list available\n");
	}

	/*
	 * Allocate space to store the sro_ctx_pool header followed by
	 * the array of sro_context entries.
	 */
	new_gl->sro_ctxs_sz = SRO_CTX_POOL_SIZE;
	new_gl->sro_ctxs_sz = round_up(new_gl->sro_ctxs_sz, GRANULE_SIZE);
	ret = rmm_el3_ifc_reserve_memory(new_gl->sro_ctxs_sz, 0,
					 GRANULE_SIZE,
					 &new_gl->sro_ctxs_pa);
	if (ret != 0) {
		ERROR("Failed to reserve memory for SRO contexts\n");
		return 0UL;
	}

	new_gl->sro_ctxs_va = xlat_low_va_map(new_gl->sro_ctxs_sz,
					      MT_RW_DATA | MT_REALM,
					      new_gl->sro_ctxs_pa,
					      true);
	if (new_gl->sro_ctxs_va == 0U) {
		ERROR("Failed to allocate VA for SRO contexts\n");
		return 0UL;
	}

	/* Initialize the firmware image sequence at 1 for the first image */
	new_gl->fw_img_sequence = 1UL;

	glob = new_gl;

	/* Flush global data itself as it may be accessed in next RMM with MMU off */
	flush_dcache_range((uintptr_t)new_gl, sizeof(struct glob_data));

	return new_gl->glob_data_pa;
}
