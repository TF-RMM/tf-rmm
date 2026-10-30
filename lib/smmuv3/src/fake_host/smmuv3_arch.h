/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef SMMUV3_ARCH_H
#define SMMUV3_ARCH_H

#include <errno.h>
#include <linux/memfd.h>
#include <smmuv3_priv.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/syscall.h>
#include <unistd.h>
#include <xlat_low_va.h>

/*
 * Architecture-specific memory mapping for the SMMUv3 driver (fake_host).
 *
 * On fake_host, PA is already a valid host address (register pages are
 * pre-initialized by the test harness). Return PA directly, optionally
 * clearing the memory.
 */
static inline uintptr_t smmuv3_arch_map(size_t size, uint64_t attr,
					uintptr_t pa, bool clear)
{
	(void)attr;

	if (pa == 0UL) {
		return 0UL;
	}

	if (clear) {
		(void)memset((void *)pa, 0, size);
	}

	return pa;
}

/*
 * Architecture-specific memory unmapping (fake_host).
 *
 * No-op: register pages mapped via smmuv3_arch_map are static buffers
 * owned by the test harness.
 */
static inline int smmuv3_arch_unmap(uintptr_t va, size_t size)
{
	(void)va;
	(void)size;
	return 0;
}

/*
 * Reserve VA space (fake_host).
 *
 * Uses xlat_low_va_reserve to allocate from the xlat dynamic VA pool
 * (so page table entries exist for xlat_low_va_get_contig_pa), then
 * backs the VA with mmap so it is dereferenceable on the host.
 */
static inline int smmuv3_arch_reserve(size_t size, uintptr_t *va)
{
	int ret = xlat_low_va_reserve(size, va);

	if (ret != 0) {
		return ret;
	}

	/* Back the xlat-pool VA with real memory (PROT_NONE = reserved) */
	if (mmap((void *)*va, size, PROT_NONE,
		 MAP_FIXED | MAP_ANONYMOUS | MAP_PRIVATE, -1, 0) == MAP_FAILED) {
		(void)xlat_low_va_unreserve(*va, size);
		*va = 0UL;
		return -ENOMEM;
	}

	return 0;
}

/*
 * Populate a reserved VA with a PA mapping (fake_host).
 *
 * Records PA in xlat page tables (for xlat_low_va_get_contig_pa) and
 * backs the VA with host memory.
 */
static inline int smmuv3_arch_populate(uintptr_t va, uintptr_t pa,
				       size_t size, uint64_t attr)
{
	int fd;
	int ret;

	/* Record PA in xlat page tables for later recovery */
	ret = xlat_low_va_populate(va, pa, size, attr);
	if (ret != 0) {
		return ret;
	}

	/* Set up backing for the reserved VA */
	fd = (int)syscall(SYS_memfd_create, "smmu", MFD_CLOEXEC);

	if (fd < 0) {
		(void)xlat_low_va_depopulate(va, size);
		return -ENOMEM;
	}

	if (ftruncate(fd, (off_t)size) != 0) {
		close(fd);
		(void)xlat_low_va_depopulate(va, size);
		return -ENOMEM;
	}

	/* Replace the PROT_NONE reservation at VA with shared backing */
	if (mmap((void *)va, size, PROT_NONE,
		 MAP_FIXED | MAP_SHARED, fd, 0) == MAP_FAILED) {
		close(fd);
		(void)xlat_low_va_depopulate(va, size);
		return -ENOMEM;
	}

	close(fd);
	return 0;
}

/*
 * Commit a populated VA region and zero the memory (fake_host).
 *
 * Makes xlat entries valid and enables mprotect(RW) on the VA.
 */
static inline int smmuv3_arch_commit_clear(uintptr_t va, size_t size)
{
	int ret = xlat_low_va_commit(va, size);

	if (ret != 0) {
		return ret;
	}

	if (mprotect((void *)va, size, PROT_READ | PROT_WRITE) != 0) {
		(void)xlat_low_va_decommit(va, size);
		return -ENOMEM;
	}
	(void)memset((void *)va, 0, size);
	return 0;
}

/*
 * Decommit a VA region (fake_host).
 *
 * Makes xlat entries invalid and revokes access via mprotect(PROT_NONE).
 * PA/attribute data is retained in xlat entries for later recovery.
 */
static inline int smmuv3_arch_decommit(uintptr_t va, size_t size)
{
	int ret = xlat_low_va_decommit(va, size);

	if (ret != 0) {
		return ret;
	}

	if (mprotect((void *)va, size, PROT_NONE) != 0) {
		return -ENOMEM;
	}
	return 0;
}

/*
 * Depopulate a VA region (fake_host).
 *
 * Clears PA/attribute data from xlat entries and restores anonymous
 * PROT_NONE backing. Returns VA to clean reserved state (same as after
 * smmuv3_arch_reserve).
 */
static inline int smmuv3_arch_depopulate(uintptr_t va, size_t size)
{
	int ret = xlat_low_va_depopulate(va, size);

	if (ret != 0) {
		return ret;
	}

	/* Restore anonymous PROT_NONE backing */
	if (mmap((void *)va, size, PROT_NONE,
		 MAP_FIXED | MAP_ANONYMOUS | MAP_PRIVATE, -1, 0) == MAP_FAILED) {
		return -ENOMEM;
	}
	return 0;
}

/*
 * Architecture-specific register write-and-ack (fake_host).
 *
 * On fake_host there is no hardware to acknowledge control register writes.
 * Simulate instant acknowledgment by writing the expected value directly
 * to the ACK register offset.
 */
static inline int smmuv3_arch_wait_for_ack(uintptr_t r_base, uint32_t ack_offset,
					   uint32_t mask, uint32_t expected)
{
	uint32_t *ack_reg = (uint32_t *)(r_base + ack_offset);

	*ack_reg = (*ack_reg & ~mask) | (expected & mask);
	return 0;
}

/*
 * Consume queued commands for @smmu in order, stopping before CMD_SYNC if
 * paused. Emulate MSI completion writes before advancing the consumer.
 * The caller serializes queue access and keeps its backing mapped.
 */
void smmuv3_arch_sync_cmdq(struct smmuv3_dev *smmu);

/*
 * Pause CMD_SYNC processing for one fake-host SMMU, or resume and drain its
 * queue when @pause is false. Later commands, including wake-up events, stay
 * queued behind the paused CMD_SYNC. Other SMMUs continue processing commands.
 * Keep the queue and MSI completion buffers alive until the device is
 * resumed or reset.
 * Return 0 on success, -EINVAL for NULL, or -ENOMEM if all pause slots are used.
 */
int smmuv3_arch_pause_cmd_sync(struct smmuv3_dev *smmu, bool pause);

/*
 * Reset a fake-host PSMMU and clear only its CMD_SYNC pause.
 * The test harness excludes concurrent users and keeps pending MSI
 * destinations alive until reset returns.
 */
void smmuv3_arch_psmmu_reset(struct smmuv3_dev *smmu);

#endif /* SMMUV3_ARCH_H */
