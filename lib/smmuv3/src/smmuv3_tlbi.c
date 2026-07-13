/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors
 */

#include <assert.h>
#include <errno.h>
#include <s2tt.h>
#include <smmuv3.h>
#include <smmuv3_priv.h>
#include <xlat_defs.h>

/* Acquire/release SMMUs' locks starting from SMMU[idx] */
static void spinlock_smmu(unsigned long idx, bool acquire)
{
	struct smmuv3_driv *driv = get_smmuv3_driver();

	assert(driv != NULL);

	for (unsigned long i = idx; i < driv->num_smmus; i++) {
		acquire ? spinlock_acquire(&driv->smmuv3_devs[i].lock) :
			  spinlock_release(&driv->smmuv3_devs[i].lock);
	}
}

/* Wait for completion of CMD_SYNC command on all SMMUs */
static int poll_cmd_sync_all(unsigned int *msi_addr)
{
	unsigned int retries = 0U;
	struct smmuv3_driv *driv = get_smmuv3_driver();
	unsigned long smmu_idx __unused;

	assert(driv != NULL);

	do {
		bool complete = true;

		for (unsigned long i = 0UL; i < driv->num_smmus; i++) {
			/* Check per-SMMU CMD_SYNC completion word */
			if (msi_addr[i] != 0U) {
				smmu_idx = i;
				complete = false;
			}
		}

		if (complete) {
			return 0;
		}

	} while (++retries < MAX_RETRIES);

	SMMU_ERROR(&driv->smmuv3_devs[smmu_idx], "CMD_SYNC timeout\n");

	return -ETIMEDOUT;
}

static int tlbi_ipa_single(struct smmuv3_dev *smmu, unsigned int vmid,
			   unsigned long addr, unsigned long num_grans,
			   long tgt_lvl, bool leaf, uintptr_t msi_addr_pa)
{
	unsigned long vmid_param0;
	unsigned long tg_ttl;
	unsigned int scale_max;
	int ret;

	assert((vmid < (U(1) << 8)) ||
		((smmu->config.features & FEAT_VMID16) != 0U));

	vmid_param0 = INPLACE(VMID, vmid);

	/*
	 * Support for range-based TLB invalidation and level hint
	 * is mandatory in implementation of SMMUv3.2 or later.
	 *
	 * Note. 4KB Translation Granule
	 */
	tg_ttl = INPLACE(TG, TG_4KB);

	/* Process leaf option */
	if (leaf) {
		tg_ttl |= LEAF_BIT;
	}

	/*
	 * Translation Table Level hint for levels 1-3.
	 *
	 * The SMMU CMD_TLBI_* operations do not have an TTL encoding to target
	 * level 0 block descriptors for the 4KB translation granule size.
	 */
	if (tgt_lvl > 0L) {
		tg_ttl |= INPLACE(TTL, (unsigned long)tgt_lvl);
	}

	/*
	 * TODO.
	 * Add support for 128-bit VMSAv9-128 descriptors programming TTL128_BIT.
	 */

	if ((smmu->config.features & FEAT_DS) != 0U) {
		/*
		 * SCALE field is 6 bits wide, bits [25:20].
		 * Values of this field that are greater than 39 are treated as 39.
		 */
		scale_max = 39U;
	} else {
		/* SCALE field is 5 bits wide, bits [24:20]. Bit 25 is RES0 */
		scale_max = 31U;
	}

	while (num_grans != 0UL) {
		unsigned long num, param0, covered;
		unsigned int scale;

		/* Bits [127:64] = Address[55:12] + TG + TTL + TTL128 + Leaf */
		unsigned long param1 = (addr & BIT_MASK_ULL(55U, 12U)) | tg_ttl;

		/*
		 * Compute SCALE and NUM for this iteration using the range
		 * invalidation formula:
		 *   Range = ((NUM + 1) * 2^SCALE) * GRANULE_SIZE
		 */
		covered = calc_tlbi_range(num_grans, scale_max, &scale, &num);

		assert(num != 0UL);
		assert(covered <= num_grans);

		/* Bits [63:0] = VMID + SCALE + NUM */
		param0 = vmid_param0 | INPLACE(SCALE, scale) | INPLACE(NUM, num - 1UL);

		ret = prepare_send_command(smmu, CMD_TLBI_S2_IPA, param0, param1);
		if (ret != 0) {
			SMMU_ERROR(smmu, "Failed to send CMD_%s\n", "TLBI_S2_IPA");
			return ret;
		}

		addr += (covered * GRANULE_SIZE);
		num_grans -= covered;
	}

	/*
	 * Sync and ...
	 * Caller will wait for completion.
	 */
	ret = prepare_send_cmd_sync(smmu, msi_addr_pa, 0U);
	if (ret != 0) {
		SMMU_ERROR(smmu, "Failed to send CMD_%s\n", "SYNC");
	}
	return ret;
}

static int tlbi_single(struct smmuv3_dev *smmu, uintptr_t msi_addr_pa)
{
	int ret;

	ret = prepare_send_command(smmu, CMD_TLBI_NSNH_ALL, 0UL, 0UL);
	if (ret != 0) {
		SMMU_ERROR(smmu, "Failed to send CMD_%s\n", "TLBI_NSNH_ALL");
		return ret;
	}

	/*
	 * Sync and ...
	 * Caller will wait for completion.
	 */
	ret = prepare_send_cmd_sync(smmu, msi_addr_pa, 0U);
	if (ret != 0) {
		SMMU_ERROR(smmu, "Failed to send CMD_%s\n", "SYNC");
	}
	return ret;
}

int smmuv3_inv(uintptr_t msi_addr_pa, unsigned int *msi_addr)
{
	struct smmuv3_driv *driv = get_smmuv3_driver();
	bool poll_sync = false;

	assert(driv != NULL);

	/* Broadcast TLB maintenance is supported on all SMMUs */
	if (get_smmu_broadcast_tlb()) {
		return 0;
	}

	/*
	 * Acquire all SMMU locks to ensure that concurrent operations,
	 * for example updating an STE, do not touch shared structures.
	 */
	spinlock_smmu(0UL, true);

	for (unsigned long i = 0UL; i < driv->num_smmus; i++) {
		struct smmuv3_dev *smmu = &driv->smmuv3_devs[i];

		/*
		 * Check that SMMU state is PSMMU_ACTIVE
		 * and it participates in broadcast TLB maintenance.
		 */
		if ((smmu->state == PSMMU_ACTIVE) &&
		   ((smmu->config.features & FEAT_BTM) == 0U)) {
			int ret;

			msi_addr[i] = U(-1);

			ret = tlbi_single(smmu,
					  msi_addr_pa + (i * sizeof(unsigned int)));
			if (ret != 0) {
				/* Release the remaining SMMU locks */
				spinlock_smmu(i, false);
				return ret;
			}
			poll_sync = true;
		}

		spinlock_release(&smmu->lock);
	}

	if (poll_sync) {
		/* Wait for completion on all SMMUs */
		return poll_cmd_sync_all(msi_addr);
	}
	return 0;
}

int smmuv3_inv_entries(unsigned int smmu_idx, unsigned int vmid,
			uintptr_t msi_addr_pa, unsigned int *msi_addr)
{
	struct smmuv3_dev *smmu;
	unsigned int retries = 0U;
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
	 * Acquire SMMU lock to ensure that concurrent operations,
	 * for example updating an STE, do not touch shared structures.
	 */
	spinlock_acquire(&smmu->lock);

	if (smmu->state != PSMMU_ACTIVE) {
		SMMU_ERROR(smmu, "PSMMU not active (state=%u)\n", smmu->state);
		spinlock_release(&smmu->lock);
		return -EINVAL;
	}

	ret = prepare_send_command(smmu, CMD_TLBI_S12_VMALL, vmid, 0UL);
	if (ret != 0) {
		SMMU_ERROR(smmu, "Failed to send CMD_%s\n", "TLBI_S12_VMALL");
		spinlock_release(&smmu->lock);
		return ret;
	}

	msi_addr[smmu_idx] = U(-1);

	ret = prepare_send_cmd_sync(smmu,
				    msi_addr_pa + (smmu_idx * sizeof(unsigned int)), 0U);
	if (ret != 0) {
		SMMU_ERROR(smmu, "Failed to send CMD_%s\n", "SYNC");
	}

	spinlock_release(&smmu->lock);

	/* Wait for completion of CMD_SYNC command on SMMU */
	do {
		/* Check per-SMMU CMD_SYNC completion word */
		if (msi_addr[smmu_idx] == 0U) {
			return 0;
		}

	} while (++retries < MAX_RETRIES);

	SMMU_ERROR(smmu, "CMD_SYNC timeout\n");

	return -ETIMEDOUT;
}

/* Invalidate @num_entrs TLB entries within a block region for @vmid */
int smmuv3_inv_at_level(unsigned int vmid, unsigned long addr, long level,
			unsigned long num_entrs, bool leaf,
			uintptr_t msi_addr_pa, unsigned int *msi_addr)
{
	struct smmuv3_driv *driv = get_smmuv3_driver();

	/* Calculate number of translation granules */
	unsigned long num_grans = num_entrs * (XLAT_BLOCK_SIZE(level) / GRANULE_SIZE);
	bool poll_sync = false;

	assert(driv != NULL);
	assert(ALIGNED(addr, XLAT_BLOCK_SIZE(level)));

	/* Broadcast TLB maintenance is supported on all SMMUs */
	if (get_smmu_broadcast_tlb()) {
		return 0;
	}

	/*
	 * Acquire all SMMU locks to ensure that concurrent operations,
	 * for example updating an STE, do not touch shared structures.
	 */
	spinlock_smmu(0UL, true);

	for (unsigned long i = 0UL; i < driv->num_smmus; i++) {
		struct smmuv3_dev *smmu = &driv->smmuv3_devs[i];

		/*
		 * Check that SMMU state is PSMMU_ACTIVE
		 * and it participates in broadcast TLB maintenance.
		 */
		if ((smmu->state == PSMMU_ACTIVE) &&
		   ((smmu->config.features & FEAT_BTM) == 0U)) {
			int ret;

			msi_addr[i] = U(-1);

			ret = tlbi_ipa_single(smmu, vmid, addr, num_grans, level, leaf,
						msi_addr_pa + (i * sizeof(unsigned int)));
			if (ret != 0) {
				/* Release the remaining SMMU locks */
				spinlock_smmu(i, false);
				return ret;
			}
			poll_sync = true;

		}
		spinlock_release(&smmu->lock);
	}

	if (poll_sync) {
		/* Wait for completion on all SMMUs */
		return poll_cmd_sync_all(msi_addr);
	}
	return 0;
}

/*
 * Invalidate @num_entrs S2 TLB entries with @addr IPA from the region tagged
 * with a VMID at leaf @level for each of @nvmids passed in @vmid_list.
 *
 * Call this function after:
 * 1a. A L2 table desc has been removed, where
 * 1b. Some S2TTEs in the table that the L2 table desc was pointed to were valid.
 * Note. This function is called with @addr aligned to the (@level - 1) boundary.
 */
int smmuv3_inv_at_level_per_vmids(unsigned int *vmid_list, unsigned int nvmids,
				  unsigned long addr, long level,
				  unsigned long num_entrs, bool leaf,
				  uintptr_t msi_addr_pa, unsigned int *msi_addr)
{
	struct smmuv3_driv *driv = get_smmuv3_driver();

	/* Calculate number of translation granules */
	unsigned long num_grans = num_entrs * (XLAT_BLOCK_SIZE(level) / GRANULE_SIZE);
	bool poll_sync = false;

	assert(driv != NULL);
	assert(vmid_list != NULL);
	assert(nvmids != 0U);
	assert(ALIGNED(addr, XLAT_BLOCK_SIZE(level)));

	/* Broadcast TLB maintenance is supported on all SMMUs */
	if (get_smmu_broadcast_tlb()) {
		return 0;
	}

	/*
	 * Acquire all SMMUs' locks to ensure that concurrent operations,
	 * for example updating an STE, do not touch shared structures.
	 */
	spinlock_smmu(0UL, true);

	for (unsigned long i = 0UL; i < driv->num_smmus; i++) {
		struct smmuv3_dev *smmu = &driv->smmuv3_devs[i];

		/*
		 * Check that SMMU state is PSMMU_ACTIVE
		 * and it participates in broadcast TLB maintenance.
		 */
		if ((smmu->state == PSMMU_ACTIVE) &&
		   ((smmu->config.features & FEAT_BTM) == 0U)) {
			for (unsigned int j = 0U; j < nvmids; j++) {
				int ret;

				msi_addr[i] = U(-1);

				ret = tlbi_ipa_single(smmu, vmid_list[j],
						      addr, num_grans, level, leaf,
						      msi_addr_pa + (i * sizeof(unsigned int)));
				if (ret != 0) {
					/* Release the remaining SMMU locks */
					spinlock_smmu(i, false);
					return ret;
				}
				poll_sync = true;
			}
		}
		spinlock_release(&smmu->lock);
	}

	if (poll_sync) {
		/* Wait for completion on all SMMUs */
		return poll_cmd_sync_all(msi_addr);
	}
	return 0;
}
