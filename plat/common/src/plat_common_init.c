/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef CBMC

#include <app_header.h>
#include <cpuid.h>
#include <debug.h>
#include <errno.h>
#include <gic.h>
#include <glob_data.h>
#include <pcpu_data.h>
#include <plat_common.h>
#include <xlat_low_va.h>

/*
 * Platform common cold boot setup for RMM.
 *
 * This function should only be invoked once during cold boot
 * and is expected to setup architecture and platform components
 * common for all PEs executing RMM. The low VA xlat tables
 * and GIC driver are initialized by this function.
 */
int plat_cmn_setup(struct xlat_mmap_region *plat_regions,
		   unsigned int nregions)
{
	int ret;
	struct xlat_low_va_info *va_info = NULL;
	struct glob_data *glob_data_ptr = NULL;

	if ((nregions != 0U) && (plat_regions == NULL)) {
		return -EINVAL;
	}

	glob_data_ptr = (struct glob_data *)pcpu_get_glob_data_pa();
	if (glob_data_ptr != NULL) {
		va_info = &glob_data_ptr->low_va_info;
	}

	/* Initialize the low VA region for RMM */
	ret = xlat_low_va_setup(plat_regions, nregions, app_get_rmm_start(),
						va_info);
	if (ret != 0) {
		ERROR("%s: Failed to setup Low VA xlat tables (%i)\n",
			__func__, ret);
		return ret;
	}

	/* Read supported GIC virtualization features and init GIC variables */
	gic_get_virt_features();

	return 0;
}

/*
 * Local PE common platform setup for RMM.
 *
 * This function will only be invoked during
 * warm boot and is expected to setup architecture and platform
 * components local to a PE executing RMM.
 */
int plat_cmn_warmboot_setup(void)
{
	int ret;

	ret = xlat_low_va_mmu_cfg();
	if (ret != 0) {
		ERROR("%s: Failed to configure MMU (%i)\n",
			__func__, ret);
		return ret;
	}

	/*
	 * Map the current CPU's already allocated per-CPU region into the fixed
	 * high-VA layout.
	 */
	ret = pcpu_high_va_setup();
	if (ret != 0) {
		ERROR("%s: Failed to setup high VA for CPU[%u]\n",
			__func__, my_cpuid());
		return ret;
	}

	VERBOSE("xlat tables configured for CPU[%u]\n", my_cpuid());
	return 0;
}

#endif /* CBMC */
