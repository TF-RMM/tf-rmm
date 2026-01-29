/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors
 */

#include <assert.h>
#include <errno.h>
#include <s2tt.h>
#include <smmuv3.h>
#include <smmuv3_priv.h>

/* Acquire/release all SMMUs' locks */
static void spinlock_all(bool acquire)
{
	struct smmuv3_driv *driv = get_smmuv3_driver();

	assert(driv != NULL);

	for (unsigned long i = 0UL; i < driv->num_smmus; i++) {
		acquire ? spinlock_acquire(&driv->smmuv3_devs[i].lock) :
			  spinlock_release(&driv->smmuv3_devs[i].lock);
	}
}

/* Wait for completion of the last command on all SMMUs */
static int wait_cmdq_all(void)
{
	struct smmuv3_driv *driv = get_smmuv3_driver();

	assert(driv != NULL);

	for (unsigned long i = 0UL; i < driv->num_smmus; i++) {
		struct smmuv3_dev *smmu = &driv->smmuv3_devs[i];

		/* Check if SMMU participates in broadcast TLB maintenance */
		if ((smmu->config.features & FEAT_BTM) == 0U) {
			int ret = wait_cmdq_empty(smmu);

			if (ret != 0) {
				return ret;
			}
		}
	}

	return 0;
}

static int tlbi_ipa_single(struct smmuv3_dev *smmu,
			   unsigned int vmid,
			   unsigned long addr,
			   unsigned long size)
{
	int ret;

	assert((vmid < (U(1) << 8)) ||
		((smmu->config.features & FEAT_VMID16) != 0U));

	while (size != 0UL) {
		ret = prepare_send_command(smmu,
					   CMD_TLBI_S2_IPA,
					   vmid,
					   addr);
		if (ret != 0) {
			SMMU_ERROR(smmu, "Failed to send CMD_%s\n", "TLBI_S2_IPA");
			return ret;
		}

		size -= GRANULE_SIZE;
		addr += GRANULE_SIZE;
	}

	/*
	 * Sync and ...
	 * Caller will wait for completion
	 */
	ret = prepare_send_command(smmu, CMD_SYNC, 0UL, 0UL);
	if (ret != 0) {
		SMMU_ERROR(smmu, "Failed to send CMD_%s\n", "SYNC");
	}
	return ret;
}

static int tlbi_ipa(unsigned int vmid, unsigned long addr,
		    unsigned long size)
{
	int ret;
	struct smmuv3_driv *driv = get_smmuv3_driver();

	assert(driv != NULL);

	if (!ALIGNED(addr, size)) {
		return -EINVAL;
	}

	/* Broadcast TLB maintenance is supported on all SMMUs */
	if (get_smmu_broadcast_tlb()) {
		return 0;
	}

	/*
	 * Acquire all SMMUs' locks to ensure that concurrent operations,
	 * for example updating an STE, do not touch shared structures.
	 */
	spinlock_all(true);

	for (unsigned long i = 0UL; i < driv->num_smmus; i++) {
		struct smmuv3_dev *smmu = &driv->smmuv3_devs[i];

		/* Check if SMMU participates in broadcast TLB maintenance */
		if ((smmu->config.features & FEAT_BTM) == 0U) {
			ret = tlbi_ipa_single(smmu, vmid, addr, size);
			if (ret != 0) {
				spinlock_all(false);
				return ret;
			}
		}
	}

	/* Wait for completion on all SMMUs */
	ret = wait_cmdq_all();

	/* Release all SMMUs' locks */
	spinlock_all(false);
	return ret;
}

static int tlbi_single(struct smmuv3_dev *smmu)
{
	int ret;

	ret = prepare_send_command(smmu, CMD_TLBI_NSNH_ALL, 0UL, 0UL);
	if (ret != 0) {
		SMMU_ERROR(smmu, "Failed to send CMD_%s\n", "TLBI_NSNH_ALL");
		return ret;
	}

	/* Caller will wait for completion */
	ret = prepare_send_command(smmu, CMD_SYNC, 0UL, 0UL);
	if (ret != 0) {
		SMMU_ERROR(smmu, "Failed to send CMD_%s\n", "SYNC");
	}
	return ret;
}

int smmuv3_inv_page(unsigned int vmid, unsigned long addr)
{
	return tlbi_ipa(vmid, addr, GRANULE_SIZE);
}

int smmuv3_inv_block(unsigned int vmid, unsigned long addr)
{
	return tlbi_ipa(vmid, addr, GRANULE_SIZE);
}

int smmuv3_inv_pages_in_block(unsigned int vmid, unsigned long addr)
{
	return tlbi_ipa(vmid, addr, GRANULE_SIZE * S2TTES_PER_S2TT);
}

int smmuv3_inv(void)
{
	int ret;
	struct smmuv3_driv *driv = get_smmuv3_driver();

	assert(driv != NULL);

	/* Broadcast TLB maintenance is supported on all SMMUs */
	if (get_smmu_broadcast_tlb()) {
		return 0;
	}

	/*
	 * Acquire all SMMUs' locks to ensure that concurrent operations,
	 * for example updating an STE, do not touch shared structures.
	 */
	spinlock_all(true);

	for (unsigned long i = 0UL; i < driv->num_smmus; i++) {
		struct smmuv3_dev *smmu = &driv->smmuv3_devs[i];

		/* Check if SMMU participates in broadcast TLB maintenance */
		if ((smmu->config.features & FEAT_BTM) == 0U) {
			ret = tlbi_single(smmu);
			if (ret != 0) {
				spinlock_all(false);
				return ret;
			}
		}
	}

	/* Wait for completion on all SMMUs */
	ret = wait_cmdq_all();

	/* Release all SMMUs' locks */
	spinlock_all(false);
	return ret;
}

int smmuv3_inv_entries(unsigned long smmu_idx, unsigned int vmid)
{
	struct smmuv3_dev *smmu;
	int ret;

	smmu = get_by_index(smmu_idx, 0U);
	if (smmu == NULL) {
		return -EINVAL;
	}

	assert((vmid < (U(1) << 8)) ||
		((smmu->config.features & FEAT_VMID16) != 0U));

	/* Check if SMMU participates in broadcast TLB maintenance */
	if ((smmu->config.features & FEAT_BTM) != 0U) {
		return 0;
	}

	/*
	 * Acquire SMMU's lock to ensure that concurrent operations,
	 * for example updating an STE, do not touch shared structures.
	 */
	spinlock_acquire(&smmu->lock);

	ret = prepare_send_command(smmu, CMD_TLBI_S12_VMALL, vmid, 0UL);
	if (ret != 0) {
		SMMU_ERROR(smmu, "Failed to send CMD_%s\n", "TLBI_S12_VMALL");
		goto out_invalidate;
	}

	ret = prepare_send_command(smmu, CMD_SYNC, 0UL, 0UL);
	if (ret != 0) {
		SMMU_ERROR(smmu, "Failed to send CMD_%s\n", "SYNC");
		goto out_invalidate;
	}

	/* Wait for completion */
	ret = wait_cmdq_empty(smmu);

out_invalidate:
	spinlock_release(&smmu->lock);
	return ret;
}
