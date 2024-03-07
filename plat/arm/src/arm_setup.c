/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch_features.h>
#include <arm_dram.h>
#include <debug.h>
#include <pl011.h>
#include <plat_common.h>
#include <platform_api.h>
#include <rmm_el3_ifc.h>
#include <sizes.h>
#include <string.h>
#include <xlat_tables.h>

#define ARM_RMM_UART	MAP_REGION_FLAT(			\
				0,			\
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

/*
 * Global platform setup for RMM.
 *
 * This function will only be invoked once during cold boot
 * and is expected to setup architecture and platform components
 * common for all PEs executing RMM. The translation tables should
 * be initialized by this function.
 */
/* coverity[misra_c_2012_rule_8_7_violation:SUPPRESS] */
void plat_setup(uint64_t x0, uint64_t x1, uint64_t x2, uint64_t x3)
{
	int ret;
	struct ns_dram_info *plat_dram;
	struct console_list *csl_list;
	struct console_info *console_ptr;

	/* TBD Initialize UART for early log */
	struct xlat_mmap_region plat_regions[] = {
		ARM_RMM_UART,
		{0}
	};

	/* Initialize the RMM-EL3 interface*/
	ret = plat_cmn_init_el3_ifc(x0, x1, x2, x3);
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

	/* Carry on with the rest of the system setup */
	ret = plat_cmn_setup(plat_regions, 1U);
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
					PLAT_ARM_MAX_DRAM_BANKS,
					&plat_dram);
	if (ret != E_RMM_BOOT_SUCCESS) {
		ERROR("DRAM data error\n");
		rmm_el3_ifc_report_fail_to_el3(ret);
	}

	/* Set up Arm DRAM layout */
	arm_set_dram_layout(plat_dram);

	plat_warmboot_setup(x0, x1, x2, x3);
}
