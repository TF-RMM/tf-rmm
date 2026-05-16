/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors
 */

#include <arch_helpers.h>
#include <assert.h>
#include <errno.h>
#include <memory.h>
#include <smmuv3_psmmu.h>
#include <rmm_el3_ifc.h>
#include <smc-rmi.h>
#include <smmuv3_arch.h>
#include <smmuv3_priv.h>
#include <string.h>
#include <xlat_tables.h>

struct smmuv3_dev *smmuv3_psmmu_find(unsigned long psmmu_ptr)
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
bool smmuv3_psmmu_validate_params(struct smmuv3_dev *smmu, struct psmmu_params *params)
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

void smmuv3_psmmu_set_active(struct smmuv3_dev *smmu)
{
	assert(smmu != NULL);
	spinlock_acquire(&smmu->lock);

	assert(smmu->state == PSMMU_BUSY);

	smmu->state = PSMMU_ACTIVE;
	spinlock_release(&smmu->lock);
}

/*
 * Set the PSMMU state to PSMMU_INACTIVE.
 *
 * This function is called by the RMI_PSMMU_ACTIVATE
 * or RMI_PSMMU_DEACTIVATE command upon failure when
 * the expected PSMMU state is PSMMU_BUSY.
 */
void smmuv3_psmmu_set_inactive(struct smmuv3_dev *smmu)
{
	assert(smmu != NULL);
	spinlock_acquire(&smmu->lock);

	assert(smmu->state == PSMMU_BUSY);

	smmu->state = PSMMU_INACTIVE;
	spinlock_release(&smmu->lock);
}

/*
 * Set the PSMMU state to PSMMU_BUSY.
 *
 * This function is called by the RMI_PSMMU_ACTIVATE command
 * when the expected PSMMU state is PSMMU_INACTIVE, or by
 * RMI_PSMMU_DEACTIVATE when the PSMMU state is PSMMU_INACTIVE.
 */
bool smmuv3_psmmu_set_busy(struct smmuv3_dev *smmu, unsigned int state)
{
	bool ret;

	assert(smmu != NULL);
	spinlock_acquire(&smmu->lock);

	ret = (smmu->state == state);
	if (ret) {
		smmu->state = PSMMU_BUSY;
	}

	spinlock_release(&smmu->lock);
	return ret;
}

size_t smmuv3_psmmu_strtab_size(struct smmuv3_dev *smmu)
{
	return smmu->strtab_size;
}

int smmuv3_psmmu_activate(struct smmuv3_dev *smmu)
{
	int ret;

	assert(smmu != NULL);
	assert(smmu->state == PSMMU_BUSY);
	assert(smmu->l1_refcnt == 0U);

	ret = smmu_on(smmu);
	if (ret != 0) {
		SMMU_ERROR(smmu, "Failed to switch %s\n", "on");
		return ret;
	}

	smmuv3_psmmu_set_active(smmu);

	SMMU_DEBUG("PSMMU 0x%lx activated\n", smmu->ns_base_pa);
	return 0;
}

void smmuv3_psmmu_unmap(struct smmuv3_dev *smmu)
{
	int ret;

	assert(smmu != NULL);

	/* Unmap Event queue */
	if (smmu->evtq.q_base != 0UL) {
		ret = smmuv3_arch_unmap(smmu->evtq.q_base, GRANULE_SIZE);
		if (ret != 0) {
			SMMU_ERROR(smmu, "Failed to unmap %s 0x%lx\n",
					"EVTQ", smmu->evtq.q_base);
		}
		smmu->evtq.q_base = 0UL;
	}

	/* Unmap Command queue */
	if (smmu->cmdq.q_base != 0UL) {
		ret = smmuv3_arch_unmap(smmu->cmdq.q_base, GRANULE_SIZE);
		if (ret != 0) {
			SMMU_ERROR(smmu, "Failed to unmap %s 0x%lx\n",
					"CMDQ", smmu->cmdq.q_base);
		}
		smmu->cmdq.q_base = 0UL;
	}

	/* Unmap array of L2 Stream Table descriptors */
	if (smmu->l2strtab != NULL) {
		ret = smmuv3_arch_unmap((uintptr_t)smmu->l2strtab, smmu->strtab_size);
		if (ret != 0) {
			SMMU_ERROR(smmu, "Failed to unmap %s 0x%lx\n",
					"L2 Desc array", (uintptr_t)smmu->l2strtab);
		}
		smmu->l2strtab = NULL;
	}

	/* Unmap L1 Stream Table */
	if (smmu->strtab_base != NULL) {
		ret = smmuv3_arch_unmap((uintptr_t)smmu->strtab_base, smmu->strtab_size);
		if (ret != 0) {
			SMMU_ERROR(smmu, "Failed to unmap %s 0x%lx\n",
					"L1 StrTab", (uintptr_t)smmu->strtab_base);
		}
		smmu->strtab_base = NULL;
	}
}

int smmuv3_psmmu_deactivate(struct smmuv3_dev *smmu)
{
	assert(smmu != NULL);

	/* Check the L1 Stream Table refcount */
	if (smmu->l1_refcnt != 0U) {
		SMMU_ERROR(smmu, "Cannot deactivate PSMMU with non-zero L1 refcount\n");
		return -EBUSY;
	}

	/*
	 * Best-effort deactivation: log errors but continue through
	 * all steps to fully tear down the SMMU.
	 */

	smmu_off(smmu);

	/* Unmap allocated memory */
	smmuv3_psmmu_unmap(smmu);

	SMMU_DEBUG("PSMMU 0x%lx deactivated\n", smmu->ns_base_pa);
	return 0;
}

void smmuv3_psmmu_reset(struct smmuv3_dev *smmu)
{
	assert(smmu != NULL);

	smmu->cmdq.q_base = 0UL;
	smmu->evtq.q_base = 0UL;
	smmu->l1_st_pa = 0UL;
	smmu->l2_ds_pa = 0UL;
	smmu->cmdq_pa = 0UL;
	smmu->evtq_pa = 0UL;
	smmu->strtab_base = NULL;
	smmu->l2strtab = NULL;
	smmu->l1_refcnt = 0U;
	smmu->state = PSMMU_INACTIVE;
}

bool smmuv3_psmmu_validate_sid(struct smmuv3_dev *smmu, unsigned long sid)
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

/*
 * Validate a L2 Stream Table entry.
 * Must be called with smmu->lock held.
 *
 * When l2tab_pa is NULL, validates that the entry is free (for create).
 * When l2tab_pa is non-NULL, validates that the entry exists with zero
 * allocated STEs and extracts its physical address (for destroy).
 */
static int validate_st_l2(struct smmuv3_dev *smmu, unsigned long l1_idx,
			  unsigned long sid, uintptr_t *l2tab_pa)
{
	/* Check PSMMU state */
	if (smmu->state != PSMMU_ACTIVE) {
		return -EINVAL;
	}

	if (l2tab_pa == NULL) {
		/*
		 * Verify that the L2 Stream Table has not already been
		 * populated in L1STD.
		 * L1STD must be zero.
		 */
		if (smmu->strtab_base[l1_idx] != 0UL) {
			SMMU_ERROR(smmu, "STRTAB L2 for SID 0x%lx is already created\n",
					sid);
			return -EINVAL;
		}
	} else {
		/*
		 * Verify that the L2 table was populated in L1STD.
		 * L1STD must be non-zero.
		 */
		if (smmu->strtab_base[l1_idx] == 0UL) {
			SMMU_ERROR(smmu, "STRTAB L2 for SID 0x%lx not found\n", sid);
			return -EINVAL;
		}

		/* Verify that the number of allocated STEs is zero */
		if ((smmu->l2strtab[l1_idx] & MASK(L2DESC_STE_CNT)) != 0UL) {
			SMMU_ERROR(smmu, "STRTAB L2 for SID 0x%lx has %lu STEs\n",
				sid, smmu->l2strtab[l1_idx] & MASK(L2DESC_STE_CNT));
			return -EINVAL;
		}

		/* Extract physical address of L2 Stream Table */
		*l2tab_pa = smmu->strtab_base[l1_idx] & MASK(STRTAB_L1_DESC_L2PTR);
	}

	return 0;
}

void smmuv3_psmmu_get_donated(struct smmuv3_dev *smmu, uintptr_t *range_base,
				unsigned long *range_size)
{
	unsigned long l1_grans;

	assert(smmu != NULL);

	/* Number of granules in L1 Stream Table */
	l1_grans = smmu->strtab_size / GRANULE_SIZE;

	range_base[(unsigned int)PSMMU_MEM_RANGE_L1_ST] = smmu->l1_st_pa;
	range_size[(unsigned int)PSMMU_MEM_RANGE_L1_ST] = l1_grans;

	range_base[(unsigned int)PSMMU_MEM_RANGE_L2_DS] = smmu->l2_ds_pa;
	range_size[(unsigned int)PSMMU_MEM_RANGE_L2_DS] = l1_grans;

	range_base[(unsigned int)PSMMU_MEM_RANGE_CMDQ] = smmu->cmdq_pa;
	range_size[(unsigned int)PSMMU_MEM_RANGE_CMDQ] = 1UL;

	range_base[(unsigned int)PSMMU_MEM_RANGE_EVTQ] = smmu->evtq_pa;
	range_size[(unsigned int)PSMMU_MEM_RANGE_EVTQ] = 1UL;
}

int smmuv3_psmmu_register_st_l1(struct smmuv3_dev *smmu, uintptr_t l1_st_pa,
				uintptr_t l2_ds_pa)
{
	uintptr_t granules_pa[2];
	uintptr_t granules_va[2];
	size_t size;

	assert(smmu != NULL);

	/* Size of L1 Stream Table */
	size = smmu->strtab_size;

	/* Physical address of L1 Stream Table */
	granules_pa[0] = l1_st_pa;

	/* Physical address of L2 Stream Table descriptors */
	granules_pa[1] = l2_ds_pa;

	for (unsigned int i = 0U; i < 2U; i++) {
		assert(ALIGNED(granules_pa[i], size));

		granules_va[i] = smmuv3_arch_map(size, MT_RW_DATA | MT_REALM,
						granules_pa[i], true);
		if (granules_va[i] == 0UL) {
			SMMU_ERROR(smmu, "Failed to map 0x%lx\n", granules_pa[i]);
			/* Unmap any previously mapped granule */
			for (unsigned int j = 0U; j < i; j++) {
				(void)smmuv3_arch_unmap(granules_va[j], size);
			}
			return -ENOMEM;
		}
	}

	/* Store base PAs for reclaim during deactivation */
	smmu->l1_st_pa = l1_st_pa;
	smmu->l2_ds_pa = l2_ds_pa;

	/* Virtual address of L1 Stream Table */
	smmu->strtab_base = (uint64_t *)granules_va[0];

	configure_strtab(smmu, granules_pa[0]);

	/* Virtual address of L2 Stream Table descriptors array */
	smmu->l2strtab = (uintptr_t *)granules_va[1];

	SMMU_DEBUG("%s: PA 0x%lx VA 0x%lx size 0x%lx\n", "L1 StrTab",
			granules_pa[0], (uintptr_t)smmu->strtab_base, size);
	SMMU_DEBUG("%s: PA 0x%lx VA 0x%lx size 0x%lx\n", "L2 Descrs",
			granules_pa[1], (uintptr_t)smmu->l2strtab, size);
	return 0;
}

int smmuv3_psmmu_register_st_l2(struct smmuv3_dev *smmu, unsigned long sid,
				uintptr_t l2tab_pa)
{
	unsigned long l1_idx;
	uintptr_t l2tab_va;
	int ret;

	assert(smmu != NULL);

	/* L1STD index in L1 table */
	l1_idx = L1STD_IDX(sid);

	spinlock_acquire(&smmu->lock);

	ret = validate_st_l2(smmu, l1_idx, sid, NULL);
	if (ret != 0) {
		spinlock_release(&smmu->lock);
		return ret;
	}

	/* Map L2 Stream Table */
	l2tab_va = smmuv3_arch_map(GRANULE_SIZE, MT_RW_DATA | MT_REALM, l2tab_pa, true);
	if (l2tab_va == 0UL) {
		spinlock_release(&smmu->lock);
		SMMU_ERROR(smmu, "Failed to map L2 Stream Table 0x%lx\n", l2tab_pa);
		return -ENOMEM;
	}

	SMMU_DEBUG("smmu->strtab_base[%lu] 0x%lx @0x%lx\n",
			l1_idx, smmu->strtab_base[l1_idx],
			(uintptr_t)&smmu->strtab_base[l1_idx]);

	/* Write L1STD */
	smmu->strtab_base[l1_idx] =
		COMPOSE(STRTAB_L1_DESC_SPAN, (SMMU_STRTAB_SPLIT + 1U)) |
		(l2tab_pa & MASK(STRTAB_L1_DESC_L2PTR));
	dsb(ish);

	/* Invalidate configuration structure */
	ret = inval_cached_ste(smmu, sid, false);
	if (ret != 0) {
		/* Clear L1STD */
		smmu->strtab_base[l1_idx] = 0UL;
		dsb(ish);

		spinlock_release(&smmu->lock);

		/* Unmap L2 Stream Table */
		(void)smmuv3_arch_unmap(l2tab_va, GRANULE_SIZE);
		return ret;
	}

	/* Increment L1 Stream Table refcount */
	smmu->l1_refcnt++;

	/*
	 * Store L2 virtual address in L2 Stream Table descriptor.
	 * The number of allocated STEs = 0.
	 */
	smmu->l2strtab[l1_idx] = l2tab_va;

	spinlock_release(&smmu->lock);

	/* coverity[null_field:SUPPRESS] */
	SMMU_DEBUG("L1STD[%lu] 0x%lx for SID 0x%lx: L2 table VA 0x%lx PA 0x%lx\n",
		   l1_idx, smmu->strtab_base[l1_idx], sid,
		   smmu->l2strtab[l1_idx], l2tab_pa);
	return ret;
}

int smmuv3_psmmu_release_st_l2(struct smmuv3_dev *smmu, unsigned long sid,
				uintptr_t *l2tab_pa)
{
	unsigned long l1_idx;
	uintptr_t l2tab_va;
	int ret;

	assert(smmu != NULL);
	assert(l2tab_pa != NULL);

	/* L1STD index in L1 table */
	l1_idx = L1STD_IDX(sid);

	spinlock_acquire(&smmu->lock);

	ret = validate_st_l2(smmu, l1_idx, sid, l2tab_pa);
	if (ret != 0) {
		spinlock_release(&smmu->lock);
		return ret;
	}

	/* Get virtual address of L2 Stream Table */
	l2tab_va = smmu->l2strtab[l1_idx];

	/* Remove L1STD entry for L2 */
	smmu->strtab_base[l1_idx] = 0UL;
	dsb(ish);

	/* Decrement L1 Stream Table refcount */
	assert(smmu->l1_refcnt != 0U);
	smmu->l1_refcnt--;

	/* Unmap L2 Stream Table */
	ret = smmuv3_arch_unmap(l2tab_va, GRANULE_SIZE);
	if (ret != 0) {
		spinlock_release(&smmu->lock);
		SMMU_ERROR(smmu, "Failed to unmap %s 0x%lx\n",
				"L2 Stream Table", l2tab_va);
		return ret;
	}

	/* Remove L2 Stream Table descriptor */
	smmu->l2strtab[l1_idx] = 0UL;

	/* Invalidate configuration structure */
	ret = inval_cached_ste(smmu, sid, false);

	spinlock_release(&smmu->lock);

	/* coverity[null_field:SUPPRESS] */
	SMMU_DEBUG("L1STD[%lu] 0x%lx for SID 0x%lx\n",
		   l1_idx, smmu->strtab_base[l1_idx], sid);
	return ret;
}

int smmuv3_psmmu_register_queues(struct smmuv3_dev *smmu, uintptr_t cmdq_pa,
				 uintptr_t evtq_pa)
{
	uintptr_t granules_pa[2];
	uintptr_t granules_va[2];

	assert(smmu != NULL);

	/* Physical address of Command queue */
	granules_pa[0] = cmdq_pa;

	/* Physical address of Event queue */
	granules_pa[1] = evtq_pa;

	for (unsigned int i = 0U; i < 2U; i++) {
		granules_va[i] = smmuv3_arch_map(GRANULE_SIZE, MT_RW_DATA | MT_REALM,
						granules_pa[i], true);
		if (granules_va[i] == 0UL) {
			SMMU_ERROR(smmu, "Failed to map 0x%lx\n", granules_pa[i]);
			/* Unmap any previously mapped granule */
			for (unsigned int j = 0U; j < i; j++) {
				(void)smmuv3_arch_unmap(granules_va[j],
							GRANULE_SIZE);
			}
			return -ENOMEM;
		}
	}

	/* Store base PAs for reclaim during deactivation */
	smmu->cmdq_pa = cmdq_pa;
	smmu->evtq_pa = evtq_pa;

	smmu->cmdq.q_base = granules_va[0];
	configure_queue(smmu, CMDQ, granules_pa[0]);

	smmu->evtq.q_base = granules_va[1];
	configure_queue(smmu, EVTQ, granules_pa[1]);

	SMMU_DEBUG("%s: PA 0x%lx VA 0x%lx\n", "CMDQ",
			granules_pa[0], smmu->cmdq.q_base);
	SMMU_DEBUG("%s: PA 0x%lx VA 0x%lx\n", "EVTQ",
			granules_pa[1], smmu->evtq.q_base);
	return 0;
}

