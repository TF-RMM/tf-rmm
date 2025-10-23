/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch_features.h>
#include <arm_memory.h>
#include <arm_root_complex.h>
#include <debug.h>
#include <pl011.h>
#include <plat_common.h>
#include <platform_api.h>
#include <rmm_el3_ifc.h>
#include <sizes.h>
#include <smmuv3.h>
#include <string.h>
#include <xlat_low_va.h>

#define ARM_RMM_UART	MAP_REGION_FLAT(			\
				0UL,				\
				SZ_4K,				\
				(MT_DEVICE | MT_RW | MT_REALM))

/*
 * Local platform setup for RMM.
 *
 * This function will only be invoked during
 * warm boot and is expected to setup architecture and platform
 * components local to a PE executing RMM.
 */
/* coverity[misra_c_2012_rule_8_7_violation:SUPPRESS] */
void plat_warmboot_setup(uint64_t x0, uint64_t x1, uint64_t x2, uint64_t x3)
{
	/* Avoid MISRA C:2012-2.7 warnings */
	(void)x0;
	(void)x1;
	(void)x2;
	(void)x3;

	if (plat_cmn_warmboot_setup() != 0) {
		panic();
	}
}

static void setup_root_complex_list(void)
{
	int ret;
	struct root_complex_list *rc_list;

	/* Get RC list from boot manifest (from version 0.5) */
	ret = rmm_el3_ifc_get_root_complex_list_pa(&rc_list);
	if (ret == E_RMM_BOOT_MANIFEST_VERSION_NOT_SUPPORTED) {
		return;
	}

	/*
	 * Setup Root Complex only RMM_V1_1=1, this makes RMM boot to continue if
	 * manifest do not have Root Complex details.
	 */
#ifdef RMM_V1_1
	if ((ret != E_RMM_BOOT_SUCCESS) || (rc_list == NULL) ||
	    (rc_list->num_root_complex == 0UL))  {
		/*
		 * TODO: Report failure to el3 for now.
		 * The ideal behavior should be, if this rmm-el3_ifc returns
		 * failure or there are no RPs in the system described, then
		 * there will no error at this point. When PDEV_CREATE is
		 * called, then it will fail at that point since validation of
		 * the info will fail(since RMM does not have any info to
		 * validate against).
		 */
		ERROR("Invalid: Root Complex list\n");
		rmm_el3_ifc_report_fail_to_el3(ret);
	}

	arm_set_root_complex_list(rc_list);
#endif
}

/*
 * Global platform setup for RMM.
 *
 * This function will only be invoked once during cold boot
 * and is expected to setup architecture and platform components
 * common for all PEs executing RMM. The translation tables should
 * be initialized by this function.
 */
/* coverity[misra_c_2012_rule_8_7_violation:SUPPRESS] */
void plat_setup(uint64_t x0, uint64_t x1, uint64_t x2, uint64_t x3, uint64_t x4)
{
	struct memory_info *plat_memory_info;
	struct console_list *csl_list;
	struct console_info *console_ptr;
	struct smmu_list *plat_smmu_list;
	struct smmu_info *plat_smmus;
	struct xlat_mmap_region *smmu_region;
	const enum dev_coh_type type[] = {DEV_MEM_COHERENT, DEV_MEM_NON_COHERENT};
	unsigned int num_smmus;
	int ret;

	/*
	 * TBD Initialize UART for early log.
	 * Map SMMUv3.
	 */
	/* coverity[misra_c_2012_rule_9_3_violation:SUPPRESS] */
	/* cppcheck-suppress misra-c2012-9.3 */
	struct xlat_mmap_region plat_regions[(RMM_MAX_SMMUS * 2U) + 1U] = {
		ARM_RMM_UART
	};

	/* Initialize the RMM-EL3 interface*/
	ret = rmm_el3_ifc_init(x0, x1, x2, x3, xlat_low_va_shared_buf_va());
	if (ret != E_RMM_BOOT_SUCCESS) {
		rmm_el3_ifc_report_fail_to_el3(ret);
	}

	/* Initialize console first */
	ret = rmm_el3_ifc_get_console_list_pa(&csl_list);
	if (ret != 0) {
		rmm_el3_ifc_report_fail_to_el3(ret);
	}

	/* If console_info is present, we need it to be pl011 */
	if (csl_list->num_consoles != 0UL) {
		uintptr_t uart_base;
		unsigned int uart_clk, uart_baud;

		console_ptr = &csl_list->consoles[0];

		if (strncmp(console_ptr->name, "pl011", sizeof("pl011")) != 0) {
			rmm_el3_ifc_report_fail_to_el3(E_RMM_BOOT_UNKNOWN_ERROR);
		}

		uart_base = console_ptr->base;
		uart_clk = (unsigned int)console_ptr->clk_in_hz;
		uart_baud = (unsigned int)console_ptr->baud_rate;

		/* RMM currently only supports one console */
		ret = pl011_init(uart_base, uart_clk, uart_baud);
		if (ret != 0) {
			rmm_el3_ifc_report_fail_to_el3(E_RMM_BOOT_UNKNOWN_ERROR);
		}

		plat_regions[0].base_pa = uart_base;
		plat_regions[0].base_va = uart_base;
	}

	/* Validate SMMUv3 list */
	ret = rmm_el3_ifc_get_smmu_list_pa(&plat_smmu_list);
	if (ret != 0) {
		/* If smmu_info is not set, skip SMMUv3 setup */
		plat_smmus = NULL;
		num_smmus = 0U;
	} else {
		plat_smmus = plat_smmu_list->smmus;
		num_smmus = (unsigned int)plat_smmu_list->num_smmus;
		smmu_region = &plat_regions[1];
	}

	/* If smmu_info is present, map SMMUv3 */
	for (unsigned int i = 0U; i < num_smmus; i++) {
		uintptr_t smmu_base = plat_smmus->smmu_base;
		uintptr_t smmu_r_base = plat_smmus->smmu_r_base;

		/* SMMU registers, Page 0 */
		smmu_region->base_pa = smmu_base;
		smmu_region->base_va = smmu_base;
		smmu_region->size = SZ_64K;
		smmu_region->attr = (MT_DEVICE | MT_RW | MT_NS);
		smmu_region->granularity = REGION_DEFAULT_GRANULARITY;

		smmu_region++;

		/* Realm registers, Pages 0, 1 */
		smmu_region->base_pa = smmu_r_base;
		smmu_region->base_va = smmu_r_base;
		smmu_region->size = 2U * SZ_64K;
		smmu_region->attr = (MT_DEVICE | MT_RW | MT_REALM);
		smmu_region->granularity = REGION_DEFAULT_GRANULARITY;

		smmu_region++;
		plat_smmus++;
	}

	/*
	 * Carry on with the rest of the system setup.
	 * The number of added regions is 2 * num_smmus + 1:
	 * - 2 regions per each SMMUv3: smmu_base and smmu_r_base;
	 * - 1 UART region.
	 */
	ret = plat_cmn_setup(plat_regions, (num_smmus * 2U) + 1U, x4);
	if (ret != 0) {
		ERROR("%s (%u): Failed to setup the platform (%i)\n",
			__func__, __LINE__, ret);
		rmm_el3_ifc_report_fail_to_el3(E_RMM_BOOT_UNKNOWN_ERROR);
	}

	/*
	 * Validate DRAM data and get pointer
	 * to the platform DRAM info structure
	 */
	ret = rmm_el3_ifc_get_dram_data_validated_pa(
					PLAT_ARM_MAX_MEM_BANKS,
					&plat_memory_info);
	if (ret != E_RMM_BOOT_SUCCESS) {
		ERROR("DRAM data error\n");
		rmm_el3_ifc_report_fail_to_el3(ret);
	}

	/* Set up Arm DRAM layout */
	arm_set_dram_layout(plat_memory_info);

	/* cppcheck-suppress misra-c2012-14.2 */
	for (unsigned int i = 0U; i < ARRAY_SIZE(type); i++) {
		/*
		 * Validate device address ranges data and get pointer
		 * to the platform device address ranges info structure
		 */
		ret = rmm_el3_ifc_get_dev_range_validated_pa(
						PLAT_ARM_MAX_MEM_BANKS,
						&plat_memory_info,
						type[i]);
		if (ret == E_RMM_BOOT_MANIFEST_VERSION_NOT_SUPPORTED) {
			break;
		}

		if (ret != E_RMM_BOOT_SUCCESS) {
			ERROR("Device address ranges data error\n");
			rmm_el3_ifc_report_fail_to_el3(ret);
		}

		if (plat_memory_info != NULL) {
			/* Set up Arm device address ranges layout */
			arm_set_dev_layout(plat_memory_info, type[i]);
		}
	}

	setup_root_complex_list();

	if (num_smmus != 0U) {
		/* Set up Arm SMMUv3 layout */
		setup_smmuv3_layout(plat_smmu_list);
	}

	plat_warmboot_setup(x0, x1, x2, x3);
}
