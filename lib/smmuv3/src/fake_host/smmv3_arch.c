/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <assert.h>
#include <errno.h>
#include <granule.h>
#include <memory.h>
#include <mmio.h>
#include <smmuv3_arch.h>
#include <smmuv3_priv.h>
#include <smmuv3_psmmu.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

static struct smmuv3_dev *paused_smmus[RMM_MAX_SMMUS];

/* Return whether CMD_SYNC processing is paused for @smmu. */
static bool cmd_sync_paused(const struct smmuv3_dev *smmu)
{
	for (unsigned int i = 0U; i < RMM_MAX_SMMUS; i++) {
		if (paused_smmus[i] == smmu) {
			return true;
		}
	}
	return false;
}

/*
 * Consume the mapped queue in FIFO order.
 * Leave a paused CMD_SYNC and every later command unconsumed, so polling
 * cannot bypass a deferred completion or its following wake-up event.
 */
void smmuv3_arch_sync_cmdq(struct smmuv3_dev *smmu)
{
	const uint128_t *cmdq;
	uint32_t entries, mask, prod, cons;

	assert(smmu != NULL);
	assert(smmu_va_is_committed(smmu->cmdq.q_base));
	cmdq = (const uint128_t *)smmu->cmdq.q_base;
	entries = U(1) << smmu->config.cmdq_log2size;
	mask = (entries << 1) - 1U;
	prod = read32(smmu->cmdq.prod_reg) & mask;
	cons = read32(smmu->cmdq.cons_reg) & mask;

	while (cons != prod) {
		uint128_t cmd = cmdq[cons & (entries - 1U)];
		uint64_t lo = (uint64_t)cmd;
		uint64_t hi = (uint64_t)(cmd >> MSIADDR_SHIFT);

		if (EXTRACT(CMD, lo) == CMD_SYNC) {
			if (cmd_sync_paused(smmu)) {
				return;
			}
			/* Host PAs are pointers; complete MSI before consuming CMD_SYNC. */
			if ((EXTRACT(CS, lo) == SIG_IRQ) && (hi != 0UL)) {
				SCA_WRITE32((uint32_t *)(uintptr_t)hi,
					    (uint32_t)(lo >> MSIDATA_SHIFT));
			}
		}
		cons = (cons + 1U) & mask;
		write32(cons, smmu->cmdq.cons_reg);
	}
}

/*
 * Set the per-device pause. Resuming drains queued completions before
 * returning; their buffers must still be alive.
 * Return 0, -EINVAL for NULL, or -ENOMEM when no pause slot is available.
 */
int smmuv3_arch_pause_cmd_sync(struct smmuv3_dev *smmu, bool pause)
{
	if (smmu == NULL) {
		return -EINVAL;
	}

	for (unsigned int i = 0U; i < RMM_MAX_SMMUS; i++) {
		if (paused_smmus[i] == smmu) {
			if (!pause) {
				paused_smmus[i] = NULL;
				smmuv3_arch_sync_cmdq(smmu);
			}
			return 0;
		}
	}
	if (!pause) {
		return 0;
	}
	for (unsigned int i = 0U; i < RMM_MAX_SMMUS; i++) {
		if (paused_smmus[i] == NULL) {
			paused_smmus[i] = smmu;
			return 0;
		}
	}
	return -ENOMEM;
}

/*
 * Architecture-specific PSMMU reset (fake_host).
 * The test harness excludes concurrent users; the published L1 entries own
 * their L2 tables until reset returns them to INTERNAL.
 * Clear this device's CMD_SYNC pause before shutdown drains its queue.
 * Pending MSI destinations must remain alive until reset returns.
 */
void smmuv3_arch_psmmu_reset(struct smmuv3_dev *smmu)
{
	assert(smmu != NULL);

	/* Allow shutdown to progress without changing other devices' pauses. */
	for (unsigned int i = 0U; i < RMM_MAX_SMMUS; i++) {
		if (paused_smmus[i] == smmu) {
			paused_smmus[i] = NULL;
			break;
		}
	}

	if (smmu->state == PSMMU_ACTIVE) {
		smmu_off(smmu);
	}

	/* Check L1 Stream Table refcount */
	if (smmu->l1_refcnt != 0U) {
		unsigned long num_l1_ents;

		assert(smmu_va_is_committed(smmu->strtab_base));

		/* Number of L2 Tables */
		num_l1_ents = 1UL << (smmu->strtab_sid_bits - SMMU_STRTAB_SPLIT);

		/*
		 * Force-cleanup any L2 Stream Tables that are still committed
		 * in the L2 pool.
		 */
		for (unsigned long l1_idx = 0UL; l1_idx < num_l1_ents; l1_idx++) {
			uintptr_t l2tab_pa, l2tab_va;
			struct granule *g_l2tab;
			unsigned short refcount;

			/* Check physical address of L2 Stream Table */
			if (smmu->strtab_base[l1_idx] == 0UL) {
				continue;
			}

			/* Get L2 Stream Table PA from L1 Table */
			l2tab_pa = smmu_l1std_l2tab_pa(smmu, l1_idx);

			/* Compute L2 Stream Table VA from the reserved pool */
			l2tab_va = smmu_l2tab_va(smmu, l1_idx);

			/* Decommit and depopulate L2 Stream Table */
			decommit_depopulate(l2tab_va, GRANULE_SIZE);

			g_l2tab = tr_addr_to_granule(l2tab_pa);
			granule_lock(g_l2tab, GRANULE_STATE_PSMMU_ST_L2);
			refcount = granule_refcount_read(g_l2tab);
			if (refcount != 0U) {
				granule_refcount_dec(g_l2tab, refcount);
			}
			granule_unlock_transition(g_l2tab, GRANULE_STATE_INTERNAL);

			/* Remove L1STD entry for L2 Stream Table */
			smmu->strtab_base[l1_idx] = 0UL;
			dsb(ish);

			/* Decrement L1 Stream Table refcount */
			if (--smmu->l1_refcnt == 0U) {
				break;
			}
		}
	}

	/*
	 * Force-cleanup any L1 Stream Table and queues that are still mapped.
	 */
	smmuv3_psmmu_unmap(smmu);

	/*
	 * Clear runtime state but preserve the reserved VA tags in
	 * strtab_base, cmdq.q_base, evtq.q_base set at boot.
	 * smmuv3_psmmu_unmap() has already re-tagged them as uncommitted.
	 */
	smmu->l1_st_pa = 0UL;
	smmu->cmdq_pa = 0UL;
	smmu->evtq_pa = 0UL;
	smmu->state = PSMMU_INACTIVE;
}
