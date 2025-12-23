/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <assert.h>
#include <debug.h>
#include <glob_data.h>
#include <granule_types.h>
#include <mapped_va_arch.h>
#include <rmm_el3_ifc.h>
#include <smmuv3.h>
#include <xlat_low_va.h>

static struct glob_data *glob;

uintptr_t glob_data_get_granules_va(size_t *alloc_size)
{
	if (glob == NULL) {
		ERROR("Global data not initialized\n");
		return 0UL;
	}

	if (alloc_size != NULL) {
		*alloc_size = glob->granules_size;
	}

	return MAPPED_VA_ARCH(glob->granules_va, glob->granules_pa);
}

uintptr_t glob_data_get_dev_granules_va(size_t *alloc_size)
{
	if (glob == NULL) {
		ERROR("Global data not initialized\n");
		return 0UL;
	}

	if (alloc_size != NULL) {
		*alloc_size = glob->dev_granules_size;
	}

	return MAPPED_VA_ARCH(glob->dev_granules_va, glob->dev_granules_pa);
}

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

uintptr_t glob_data_init(struct glob_data *gl,
		unsigned long max_gr, unsigned long max_dev_gr)
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

		/*
		 * Copy Low VA information since some static VA regions
		 * are different between RMM instances.
		 */
		glob->low_va_info = *(xlat_get_low_va_info());

		/* Flush in case any CPUs access this with MMU off */
		flush_dcache_range((uintptr_t)&glob->low_va_info,
			sizeof(struct xlat_low_va_info));

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

	new_gl->glob_data_pa = buf_pa;
	new_gl->glob_data_va = va;
	new_gl->glob_data_size = GLOB_DATA_MAX_SIZE;

	/* Allocate VA for granules array */
	new_gl->granules_size = round_up(sizeof(struct granule) * max_gr, GRANULE_SIZE);
	ret = rmm_el3_ifc_reserve_memory(new_gl->granules_size, 0,
					 GRANULE_SIZE,
					 &new_gl->granules_pa);
	if (ret != 0) {
		ERROR("Failed to reserve memory for granules array\n");
		return 0UL;
	}

	new_gl->granules_va = xlat_low_va_map(new_gl->granules_size,
					      MT_RW_DATA | MT_REALM,
					      new_gl->granules_pa,
					      true);
	if (new_gl->granules_va == 0U) {
		ERROR("Failed to allocate VA for granules array\n");
		return 0UL;
	}

	/* Allocate VA for dev_granules array */
	if (max_dev_gr != 0UL) {
		new_gl->dev_granules_size =
			round_up(sizeof(struct dev_granule) * max_dev_gr,
				 GRANULE_SIZE);
		ret = rmm_el3_ifc_reserve_memory(new_gl->dev_granules_size,
						 0, GRANULE_SIZE,
						 &new_gl->dev_granules_pa);
		if (ret != 0) {
			ERROR("Failed to reserve memory for dev_granules array\n");
			return 0UL;
		}

		new_gl->dev_granules_va =
			xlat_low_va_map(new_gl->dev_granules_size,
					MT_RW_DATA | MT_REALM,
					new_gl->dev_granules_pa, true);
		if (new_gl->dev_granules_va == 0U) {
			ERROR("Failed to allocate VA for dev_granules array\n");
			return 0UL;
		}
	}

	/* Set up SMMU layout */
	ret = rmm_el3_ifc_get_cached_smmu_list_pa(&plat_smmu_list);
	if (ret == 0) {
		new_gl->smmu_driv_hdl_va = smmuv3_driver_setup(plat_smmu_list,
				&new_gl->smmu_driv_hdl_pa,
				&new_gl->smmu_driv_hdl_sz);

		if (new_gl->smmu_driv_hdl_va == 0UL) {
			ERROR("Failed to set up SMMU driver\n");
			return 0UL;
		}
	} else {
		INFO("No SMMU list available\n");
	}

	glob = new_gl;

	/* Flush global data itself as it may be accessed in next RMM with MMU off */
	flush_dcache_range((uintptr_t)new_gl, sizeof(struct glob_data));

	return new_gl->glob_data_pa;
}
