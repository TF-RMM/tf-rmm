/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <debug.h>
#include <host_console.h>
#include <host_utils.h>
#include <host_utils_pci.h>
#include <plat_common.h>
#include <plat_compat_mem.h>
#include <platform_api.h>
#include <rmm_el3_ifc.h>
#include <stdint.h>
#include <utils_def.h>

/* Number of translation tables for the RMM Low VA static region */
#define HOST_XLAT_TABLES_LOW_VA		6

#define HOST_RESERVE_MEM_SIZE		\
	RESERVE_MEM_SIZE(HOST_NR_GRANULES, HOST_NR_NCOH_GRANULES, HOST_XLAT_TABLES_LOW_VA)

/*
 * Space to model the RMM reserved mem, used to emulate EL3 memory allocation.
 */
static unsigned char rmm_reserve_memory[HOST_RESERVE_MEM_SIZE] __aligned(GRANULE_SIZE);
static struct plat_memory_bank host_dram_banks[1];
static struct plat_memory_bank host_dev_ncoh_banks[1];
static struct plat_memory_bank host_dev_coh_banks[1];

/* Define the EL3-RMM interface compatibility callbacks */
static struct rmm_el3_compat_callbacks callbacks = {
	.reserve_mem_cb = plat_compat_reserve_memory,
};

/*
 * Local platform setup for RMM.
 *
 * This function will only be invoked during
 * warm boot and is expected to setup architecture and platform
 * components local to a PE executing RMM.
 */
void plat_warmboot_setup(uint64_t x0, uint64_t x1,
			 uint64_t x2, uint64_t x3)
{
	/* Avoid MISRA C:2102-2.7 warnings */
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
void plat_setup(uint64_t x0, uint64_t x1,
		uint64_t x2, uint64_t x3,
		uint64_t x4 __unused)
{
	(void)host_csl_init();

	/* Initialize the RMM-EL3 interface*/
	if (rmm_el3_ifc_init(x0, x1, x2, x3, x3) != 0) {
		panic();
	}

	/* Initialize the compatibility memory reservation layer */
	plat_cmn_compat_reserve_mem_init(&callbacks,
				rmm_reserve_memory,
				sizeof(rmm_reserve_memory));

	/* Carry on with the rest of the system setup */
	if (plat_cmn_setup(NULL, 0) != 0) {
		panic();
	}

	plat_warmboot_setup(x0, x1, x2, x3);
}

/* Return the static host platform memory bank array for the RMI @category. */
const struct plat_memory_bank *plat_get_mem_banks(
					unsigned long category,
					unsigned long *num_banks)
{
	struct plat_memory_bank *banks;

	if (num_banks == NULL) {
		return NULL;
	}

	switch (category) {
	case RMI_MEM_CATEGORY_CONVENTIONAL:
		banks = host_dram_banks;
		banks[0].base = host_util_get_granule_base();
		banks[0].size = HOST_DRAM_SIZE;
		*num_banks = 1UL;
		break;
	case RMI_MEM_CATEGORY_DEV_NCOH:
		banks = host_dev_ncoh_banks;
		banks[0].base = host_util_get_dev_granule_base();
		banks[0].size = HOST_NCOH_DEV_SIZE;
		*num_banks = 1UL;
		break;
	case RMI_MEM_CATEGORY_DEV_COH:
		banks = host_dev_coh_banks;
		*num_banks = 0UL;
		break;
	default:
		return NULL;
	}

	return banks;
}
