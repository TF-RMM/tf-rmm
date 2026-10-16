/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <assert.h>
#include <errno.h>
#include <memory.h>
#include <mmio.h>
#include <smmuv3_arch.h>
#include <smmuv3_priv.h>
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
