/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef CBMC
#define _GNU_SOURCE
#endif

#include <arch_helpers.h>
#ifndef CBMC
#include <assert.h>
#endif
#include <buffer.h>
#include <debug.h>
#include <gic.h>
#include <host_utils.h>
#include <rmm_el3_ifc.h>
#ifndef CBMC
#include <string.h>
#include <sys/mman.h>
#include <unistd.h>
#endif
#include <xlat_defs.h>

/*
 * Allocate memory to emulate physical memory to initialize the
 * granule library.
 *
 * CBMC builds use a plain static array.
 * All other host builds use memfd-backed MAP_SHARED regions, enabling
 * mmap aliasing for zero-copy slot buffers.
 */
#ifdef CBMC
unsigned char host_dram_buffer[HOST_DRAM_SIZE] __aligned(GRANULE_SIZE);
unsigned char host_dev_ncoh_buffer[HOST_NCOH_DEV_SIZE] __aligned(GRANULE_SIZE);
#else
static unsigned char *host_dram_buffer;
static unsigned char *host_dev_ncoh_buffer;
static int host_dram_memfd = -1;
static int host_dev_memfd = -1;

__attribute__((constructor))
static void host_util_init_memfd(void)
{
	int ret __attribute__((unused));

	host_dram_memfd = memfd_create("host_dram", MFD_CLOEXEC);
	assert(host_dram_memfd >= 0);
	ret = ftruncate(host_dram_memfd, (off_t)HOST_DRAM_SIZE);
	assert(ret == 0);
	host_dram_buffer = mmap(NULL, HOST_DRAM_SIZE, PROT_READ | PROT_WRITE,
				MAP_SHARED, host_dram_memfd, 0);
	assert(host_dram_buffer != MAP_FAILED);

	host_dev_memfd = memfd_create("host_dev", MFD_CLOEXEC);
	assert(host_dev_memfd >= 0);
	ret = ftruncate(host_dev_memfd, (off_t)HOST_NCOH_DEV_SIZE);
	assert(ret == 0);
	host_dev_ncoh_buffer = mmap(NULL, HOST_NCOH_DEV_SIZE,
				    PROT_READ | PROT_WRITE,
				    MAP_SHARED, host_dev_memfd, 0);
	assert(host_dev_ncoh_buffer != MAP_FAILED);
}

/*
 * Common slot buffer implementation using mmap aliasing.
 * Shared by host_build, host_fuzz, and host_test (as fallback).
 */
static unsigned char *host_slot_region;
static bool host_slot_active[(unsigned int)NR_CPU_SLOTS];

__attribute__((constructor))
static void host_slot_region_init(void)
{
	size_t slot_size = (size_t)NR_CPU_SLOTS * GRANULE_SIZE;

	host_slot_region = mmap(NULL, slot_size, PROT_NONE,
				MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
	assert(host_slot_region != MAP_FAILED);
}

unsigned int host_util_buf_to_slot(void *buf)
{
	uintptr_t offset = (uintptr_t)buf - (uintptr_t)host_slot_region;

	assert(offset < (uintptr_t)NR_CPU_SLOTS * GRANULE_SIZE);
	assert((offset % GRANULE_SIZE) == 0U);
	return (unsigned int)(offset / GRANULE_SIZE);
}

void *host_util_slot_map(unsigned int slot, unsigned long addr)
{
	unsigned long dram_base = (unsigned long)host_dram_buffer;
	unsigned long dev_base = (unsigned long)host_dev_ncoh_buffer;
	int fd;
	off_t file_offset;

	assert(slot < NR_CPU_SLOTS);

	if (addr >= dram_base && addr < dram_base + HOST_DRAM_SIZE) {
		fd = host_dram_memfd;
		file_offset = (off_t)(addr - dram_base);
	} else if (addr >= dev_base && addr < dev_base + HOST_NCOH_DEV_SIZE) {
		fd = host_dev_memfd;
		file_offset = (off_t)(addr - dev_base);
	} else {
		assert(false);
		return NULL;
	}

	unsigned char *slot_va = host_slot_region + (size_t)slot * GRANULE_SIZE;
	void *p __attribute__((unused));

	p = mmap(slot_va, GRANULE_SIZE, PROT_READ | PROT_WRITE,
		 MAP_FIXED | MAP_SHARED, fd, file_offset);
	assert(p == (void *)slot_va);

	host_slot_active[slot] = true;
	return (void *)slot_va;
}

void host_util_slot_unmap(void *buf)
{
	unsigned int slot = host_util_buf_to_slot(buf);

	assert(host_slot_active[slot]);
	host_slot_active[slot] = false;

	void *slot_va = host_slot_region + (size_t)slot * GRANULE_SIZE;
	void *p __attribute__((unused));

	p = mmap(slot_va, GRANULE_SIZE, PROT_NONE,
		 MAP_FIXED | MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
	assert(p == slot_va);
}

void host_util_slot_reset(void)
{
	size_t slot_size = (size_t)NR_CPU_SLOTS * GRANULE_SIZE;
	void *p __attribute__((unused));

	p = mmap(host_slot_region, slot_size, PROT_NONE,
		 MAP_FIXED | MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
	assert(p == (void *)host_slot_region);
	(void)memset(host_slot_active, 0, sizeof(host_slot_active));
}
#endif /* CBMC */

/*
 * Define and set the Boot Interface arguments.
 */
static unsigned char el3_rmm_shared_buffer[PAGE_SIZE] __aligned(PAGE_SIZE);

/*
 * Create a basic boot manifest.
 */
static struct rmm_core_manifest *boot_manifest =
			(struct rmm_core_manifest *)el3_rmm_shared_buffer;


unsigned long host_util_get_granule_base(void)
{
	return (unsigned long)host_dram_buffer;
}

unsigned long host_util_get_dev_granule_base(void)
{
	return (unsigned long)host_dev_ncoh_buffer;
}

unsigned char *host_util_get_el3_rmm_shared_buffer(void)
{
	return el3_rmm_shared_buffer;
}

void host_util_setup_sysreg_and_boot_manifest(void)
{
	int ret;

	/*
	 * Initialize ID_AA64DFR0_EL1 with PMUVer field to PMUv3p7.
	 * (ID_AA64DFR0_EL1.PMUVer, bits [11:8] set to 7).
	 * Also setup minimum allowed by architecture number of watchpoints
	 * (ID_AA64DFR0_EL1.WRPs, bits [15:12] set to 1)
	 * and breakpoints.
	 * (ID_AA64DFR0_EL1.BRPs, bits [23:20] set to 1)
	 */
	(void)host_util_set_default_sysreg_cb("id_aa64dfr0_el1",
			INPLACE(ID_AA64DFR0_EL1_PMUVer, 7UL) |
			INPLACE(ID_AA64DFR0_EL1_WRPs, 1UL) |
			INPLACE(ID_AA64DFR0_EL1_BRPs, 1UL));

	/*
	 * Initialize ID_AA64MMFR0_EL1 with a physical address
	 * range of 48 bits (PARange bits set to 0b0101) and
	 * support for 52bits PA size with 4KB granularity;
	 */
	(void)host_util_set_default_sysreg_cb("id_aa64mmfr0_el1",
				INPLACE(ID_AA64MMFR0_EL1_PARANGE, 5UL) |
				INPLACE(ID_AA64MMFR0_EL1_TGRAN4,
					ID_AA64MMFR0_EL1_TGRAN4_LPA2) |
				INPLACE(ID_AA64MMFR0_EL1_TGRAN4_2,
					ID_AA64MMFR0_EL1_TGRAN4_2_TGRAN4));

	/*
	 * Initialize ID_AA64MMFR3_EL1 for FEAT_MEC support
	 */
	(void)host_util_set_default_sysreg_cb("id_aa64mmfr3_el1",
				INPLACE(ID_AA64MMFR3_EL1_MEC, 1UL) |
				INPLACE(ID_AA64MMFR3_EL1_TCRX, 1UL) |
				INPLACE(ID_AA64MMFR3_EL1_SCTLRX, 1UL) |
				INPLACE(ID_AA64MMFR3_EL1_D128, 1UL));

	/* Initialize the maximum MECID width */
	(void)host_util_set_default_sysreg_cb("mecidr_el2",
				INPLACE(MECIDR_MECIDWIDTHM1, 0xFFFF));

	/*
	 * Initialize ICH_VTR_EL2 with 6 preemption bits.
	 * (PREbits is equal number of preemption bits minus one)
	 */
	(void)host_util_set_default_sysreg_cb("ich_vtr_el2",
			INPLACE(ICH_VTR_EL2_PRE_BITS, 5UL));

	/* SCTLR_EL2 is reset to zero */
	(void)host_util_set_default_sysreg_cb("sctlr_el2", 0UL);

	/* HCR_EL2 is reset to zero */
	(void)host_util_set_default_sysreg_cb("hcr_el2", 0UL);

	/* TPIDR_EL2 is reset to zero */
	(void)host_util_set_default_sysreg_cb("tpidr_el2", 0UL);

	/* ID_AA64ISAR0.RNDR is reset to 1 */
	(void)host_util_set_default_sysreg_cb("id_aa64isar0_el1",
				INPLACE(ID_AA64ISAR0_EL1_RNDR, 1UL));

	/* Enable FEAT_SYSREG128 */
	(void)host_util_set_default_sysreg_cb("id_aa64isar2_el1",
				(INPLACE(ID_AA64ISAR2_EL1_SYSREG128, 1UL) |
				 INPLACE(ID_AA64ISAR2_EL1_SYSINSTR128, 1UL)));

	/*
	 * Add callback to elr_el2 so that the realm entry point can be accessed
	 * by host_run_realm
	 */
	(void)host_util_set_default_sysreg_cb("elr_el2", 0UL);

	/*
	 * Add callback to esr_el2 so that the realm exceptions can be handled.
	 */
	(void)host_util_set_default_sysreg_cb("esr_el2", 0UL);

	/*
	 * Set number of event counters implemented to 31.
	 * (PMCR_EL0.N, bits [15:11] set to 31)
	 */
	(void)host_util_set_default_sysreg_cb("pmcr_el0",
			INPLACE(PMCR_EL0_N, 31UL));

	/*
	 * Set DCZID_EL0 register with DZP = 0 and
	 * BS = 0b101 as GRANULE_SIZE on CBMC platform is 7.
	 */
	(void)host_util_set_default_sysreg_cb("dczid_el0",
			INPLACE(DCZID_EL0_BS, 5UL));

	/* Set ISR_EL1 to 0 */
	(void)host_util_set_default_sysreg_cb("isr_el1", 0UL);

	/* Set MECID registers to 0 */
	(void)host_util_set_default_sysreg_cb("mecid_p0_el2", 0UL);
	(void)host_util_set_default_sysreg_cb("mecid_p1_el2", 0UL);
	(void)host_util_set_default_sysreg_cb("mecid_a0_el2", 0UL);
	(void)host_util_set_default_sysreg_cb("mecid_a1_el2", 0UL);
	(void)host_util_set_default_sysreg_cb("vmecid_p_el2", 0UL);
	(void)host_util_set_default_sysreg_cb("vmecid_a_el2", 0UL);

	/*
	 * Fake host runs the RMM code in an EL2 context. Set CurrentEL to EL2
	 * (bits [3:2] == 0b10).
	 */
	ret = host_util_set_default_sysreg_cb("CurrentEl",
					    INPLACE(CurrentEL_EL, 2UL));

	/*
	 * Only check the return value of the last callback setup, to detect
	 * if we are out of callback slots.
	 */
	if (ret != 0) {
		panic();
	}

	/* Initialize the boot manifest */
	boot_manifest->version = RMM_EL3_MANIFEST_MAKE_VERSION(
						RMM_EL3_MANIFEST_VERS_MAJOR,
						RMM_EL3_MANIFEST_VERS_MINOR);
	boot_manifest->plat_data = (uintptr_t)NULL;
}

int host_util_rec_run(unsigned long *rec_regs, unsigned long *rec_sp_el0)
{
	unsigned long pc = read_elr_el2();
	realm_entrypoint_t realm_ep = (void *)pc;

	write_esr_el2(0x0);
	return realm_ep(rec_regs, rec_sp_el0);
}

int host_util_rsi_helper(realm_entrypoint_t ep)
{
	/* Reduce the ep by 0x4 as RMM will advance_pc as part of handling RSI */
	write_elr_el2((u_register_t) ep - 0x4);
	write_esr_el2(ESR_EL2_EC_SMC);

	return ARM_EXCEPTION_SYNC_LEL;
}
