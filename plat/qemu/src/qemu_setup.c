/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <debug.h>
#include <pl011.h>
#include <plat_common.h>
#include <qemu_dram.h>
#include <qemu_private.h>
#include <rmm_el3_ifc.h>
#include <sizes.h>
#include <xlat_tables.h>

#define MAP_QEMU_UART \
	MAP_REGION_FLAT(RMM_UART_ADDR, SZ_4K, MT_DEVICE | MT_RW | MT_REALM)

/*
 * Local platform setup for RMM.
 *
 * This function will only be invoked during
 * warm boot and is expected to setup architecture and platform
 * components local to a PE executing RMM.
 */
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
void plat_setup(uint64_t x0, uint64_t x1, uint64_t x2, uint64_t x3)
{
	int ret;
	struct ns_dram_info *plat_dram;

	struct xlat_mmap_region plat_regions[] = {
		MAP_QEMU_UART,
		{0}
	};

	uart_init(RMM_UART_ADDR, QEMU_UART_CLK_IN_HZ, QEMU_UART_BAUDRATE);

	/* Carry on with the rest of the system setup */
	ret = plat_cmn_setup(x0, x1, x2, x3, plat_regions, 1U);
	if (ret != 0) {
		ERROR("%s (%u): Failed to setup the platform (%i)\n",
		      __func__, __LINE__, ret);
		panic();
	}

	/*
	 * Validate DRAM data and get pointer
	 * to the platform DRAM info structure
	 */
	ret = rmm_el3_ifc_get_dram_data_validated_pa(
					MAX_DRAM_NUM_BANKS,
					&plat_dram);
	if (ret != E_RMM_BOOT_SUCCESS) {
		ERROR("DRAM data error\n");
		rmm_el3_ifc_report_fail_to_el3(ret);
	}

	qemu_set_dram_layout(plat_dram);

	plat_warmboot_setup(x0, x1, x2, x3);
}
