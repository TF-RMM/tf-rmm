/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors
 */

#include <arch_helpers.h>
#include <assert.h>
#include <errno.h>
#include <psmmuv3.h>
#include <rmm_el3_ifc.h>
#include <smc-rmi.h>
#include <smmuv3_priv.h>
#include <string.h>
#include <xlat_low_va.h>
#include <xlat_tables.h>

struct smmuv3_dev *psmmu_find(unsigned long psmmu_ptr)
{
	struct smmuv3_driv *driv = get_smmuv3_driver();

	assert(driv != NULL);

	for (unsigned long i = 0UL; i < driv->num_smmus; i++) {
		struct smmuv3_dev *smmu = &driv->smmuv3_devs[i];

		if (psmmu_ptr == smmu->ns_base_pa) {
			return smmu;
		}
	}

	return NULL;
}

/*
 * Note.
 * The current implementation does not support MSI, PRI, or ATS.
 * RMI_PSMMU_FLAGS_MSI is ignored. Setting RMI_PSMMU_FLAGS_PRI or
 * RMI_PSMMU_FLAGS_ATS results in an error.
 */
bool psmmu_validate_params(struct smmuv3_dev *smmu, struct psmmu_params *params)
{
	unsigned long flags = params->flags;

	assert(smmu != NULL);

	if (EXTRACT(RMI_PSMMU_FLAGS_PRI, flags) == RMI_FEATURE_TRUE) {
		return false;
	}

	if (EXTRACT(RMI_PSMMU_FLAGS_ATS, flags) == RMI_FEATURE_TRUE) {
		return false;
	}

	(void)memcpy(&smmu->params, params, sizeof(struct psmmu_params));

	return true;
}

int psmmu_activate(struct smmuv3_dev *smmu)
{
	int ret;

	assert(smmu != NULL);

	spinlock_acquire(&smmu->lock);

	/* Check PSMMU state */
	if (smmu->state != PSMMU_INACTIVE) {
		spinlock_release(&smmu->lock);
		return -EBUSY;
	}

	assert(smmu->l1std_cnt == 0U);

	ret = enable_smmu(smmu);
	spinlock_release(&smmu->lock);

	SMMU_DEBUG("PSMMU 0x%lx activate %d\n", smmu->ns_base_pa, ret);
	return ret;
}

int psmmu_deactivate(struct smmuv3_dev *smmu)
{
	int ret;

	assert(smmu != NULL);

	spinlock_acquire(&smmu->lock);

	/* Check PSMMU state and the number of L1 Stream Table Descriptors */
	if ((smmu->state != PSMMU_ACTIVE) || (smmu->l1std_cnt != 0U)) {
		spinlock_release(&smmu->lock);
		return -EBUSY;
	}

	ret = disable_smmu(smmu);
	spinlock_release(&smmu->lock);

	SMMU_DEBUG("PSMMU 0x%lx deactivate %d\n", smmu->ns_base_pa, ret);
	return ret;
}

bool psmmu_validate_sid(struct smmuv3_dev *smmu, unsigned long sid)
{
	assert(smmu != NULL);

	/*
	 * Validate that the SID is properly aligned
	 * and within the expected boundary.
	 */
	if (((sid & (STRTAB_L1_STE_MAX - 1UL)) != 0UL) ||
		(sid >= (1UL << smmu->config.streamid_bits))) {
		return false;
	}

	return true;
}

int psmmu_allocate_st_l2(struct smmuv3_dev *smmu, unsigned long sid)
{
	void *l2ptr_pa;
	unsigned long l1_idx;
	int ret;

	SMMU_DEBUG("%s(0x%lx)\n", __func__, sid);

	assert(smmu != NULL);

	/* L1STD index in L1 table */
	l1_idx = L1STD_IDX(sid);

	spinlock_acquire(&smmu->lock);

	/* Check PSMMU state */
	if (smmu->state != PSMMU_ACTIVE) {
		spinlock_release(&smmu->lock);
		return -EINVAL;
	}

	/*
	 * Note.
	 * L2 stream tables are not destroyed in the current implementation.
	 * TODO. Implement with Stateful RMI Operation.
	 *
	 * Check that the L2 stream table has not already been populated in L1STD.
	 * L1STD must be zero.
	 */
	if (smmu->strtab_base[l1_idx] != 0UL) {
		SMMU_ERROR(smmu, "STRTAB L2 for SID 0x%lx is already created\n",
				sid);
		spinlock_release(&smmu->lock);
		return -EINVAL;
	}

	l2ptr_pa = &smmu->l2strtab_base_pa[l1_idx];

	/* Write L1STD */
	smmu->strtab_base[l1_idx] =
		COMPOSE(STRTAB_L1_DESC_SPAN, (SMMU_STRTAB_SPLIT + 1U)) |
		((uintptr_t)l2ptr_pa & MASK(STRTAB_L1_DESC_L2PTR));
	dsb(ish);

	/* Increment number of L1 Stream Table Descriptors */
	smmu->l1std_cnt++;

	/* Invalidate configuration structure */
	ret = inval_cached_ste(smmu, sid, false);
	spinlock_release(&smmu->lock);

	/* coverity[null_field:SUPPRESS] */
	SMMU_DEBUG("L1STD[%lu] 0x%lx for SID 0x%lx: L2 table VA 0x%lx PA 0x%lx\n",
		   l1_idx, smmu->strtab_base[l1_idx], sid,
		   (uintptr_t)&smmu->l2strtab_base[l1_idx],
		   (uintptr_t)&smmu->l2strtab_base_pa[l1_idx]);
	return ret;
}

int psmmu_release_st_l2(struct smmuv3_dev *smmu, unsigned long sid)
{
	unsigned long l1_idx;
	unsigned short ste_cnt;
	int ret = 0;

	SMMU_DEBUG("%s(0x%lx)\n", __func__, sid);

	assert(smmu != NULL);

	/* L1STD index in L1 table */
	l1_idx = L1STD_IDX(sid);

	spinlock_acquire(&smmu->lock);

	/* Check PSMMU state */
	if (smmu->state != PSMMU_ACTIVE) {
		spinlock_release(&smmu->lock);
		return -EINVAL;
	}

	/*
	 * Check that L2 table was created.
	 * L1STD must be non-zero.
	 */
	if (smmu->strtab_base[l1_idx] == 0UL) {
		spinlock_release(&smmu->lock);
		SMMU_ERROR(smmu, "STRTAB L2 for SID 0x%lx not found\n", sid);
		return -EINVAL;
	}

	/* Check number of allocated STEs */
	ste_cnt = smmu->l2ste_cnt[l1_idx];
	if (ste_cnt != 0U) {
		spinlock_release(&smmu->lock);
		SMMU_ERROR(smmu, "STRTAB L2 for SID 0x%lx has %u STEs\n",
				sid, ste_cnt);
		return -EINVAL;
	}

	/* Remove L1STD entry for L2 */
	smmu->strtab_base[l1_idx] = 0UL;
	dsb(ish);

	/* Decrement number of L1 Stream Table Descriptors */
	smmu->l1std_cnt--;

	/* Invalidate configuration structure */
	ret = inval_cached_ste(smmu, sid, false);

	spinlock_release(&smmu->lock);

	/* coverity[null_field:SUPPRESS] */
	SMMU_DEBUG("L1STD[%lu] 0x%lx for SID 0x%lx: L2 table VA 0x%lx PA 0x%lx\n",
		   l1_idx, smmu->strtab_base[l1_idx], sid,
		   (uintptr_t)&smmu->l2strtab_base[l1_idx],
		   (uintptr_t)&smmu->l2strtab_base_pa[l1_idx]);
	return ret;
}
