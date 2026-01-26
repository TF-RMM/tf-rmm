/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <assert.h>
#include <debug.h>
#include <host_console.h>
#include <host_utils.h>
#include <host_utils_pci.h>
#include <plat_common.h>
#include <plat_compat_mem.h>
#include <rmm_el3_ifc.h>
#include <smc.h>
#include <stdint.h>
#include <xlat_tables.h>

/* Number of translation tables for the RMM Low VA static region */
#define HOST_XLAT_TABLES_LOW_VA		6

#define HOST_RESERVE_MEM_SIZE		\
	RESERVE_MEM_SIZE(HOST_NR_GRANULES, HOST_NR_NCOH_GRANULES, HOST_XLAT_TABLES_LOW_VA)

/*
 * Space to model the RMM reserved mem, used to emulate EL3 memory allocation.
 */
static unsigned char rmm_reserve_memory[HOST_RESERVE_MEM_SIZE] __aligned(GRANULE_SIZE);

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
		uint64_t x4)
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
	if (plat_cmn_setup(NULL, 0, x4) != 0) {
		panic();
	}

	plat_warmboot_setup(x0, x1, x2, x3);
}

unsigned long plat_granule_addr_to_idx(unsigned long addr)
{
	if (!(GRANULE_ALIGNED(addr) &&
		(addr < (host_util_get_granule_base() + HOST_DRAM_SIZE)) &&
		(addr >= host_util_get_granule_base()))) {
		return UINT64_MAX;
	}

	return (addr - host_util_get_granule_base()) / GRANULE_SIZE;
}

unsigned long plat_granule_idx_to_addr(unsigned long idx)
{
	assert(idx < HOST_NR_GRANULES);
	return host_util_get_granule_base() + (idx * GRANULE_SIZE);
}

unsigned long plat_get_num_granules(void)
{
	return HOST_NR_GRANULES;
}

unsigned long plat_dev_granule_addr_to_idx(unsigned long addr, enum dev_coh_type *type)
{
	if (!(GRANULE_ALIGNED(addr) &&
		(addr < (host_util_get_dev_granule_base() + HOST_NCOH_DEV_SIZE)) &&
		(addr >= host_util_get_dev_granule_base()))) {
		return UINT64_MAX;
	}

	*type = DEV_MEM_NON_COHERENT;
	return (addr - host_util_get_dev_granule_base()) / GRANULE_SIZE;
}

unsigned long plat_dev_granule_idx_to_addr(unsigned long idx, enum dev_coh_type type)
{
	(void)type;

	/* No coherent device memory */
	assert(type == DEV_MEM_NON_COHERENT);
	assert(idx < HOST_NR_NCOH_GRANULES);
	return host_util_get_dev_granule_base() + (idx * GRANULE_SIZE);
}

unsigned long plat_get_num_dev_granules(enum dev_coh_type type)
{
	if (type == DEV_MEM_NON_COHERENT) {
		return HOST_NR_NCOH_GRANULES;
	}

	return UINT64_MAX;
}
