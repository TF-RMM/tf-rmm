/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors
 */

#include <arch_helpers.h>
#include <assert.h>
#include <errno.h>
#include <memory.h>
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

/*
 * Set the PSMMU state to PSMMU_INACTIVE.
 *
 * This function is called by the RMI_PSMMU_ACTIVATE
 * or RMI_PSMMU_DEACTIVATE command upon failure when
 * the expected PSMMU state is PSMMU_BUSY.
 */
void psmmu_set_inactive(struct smmuv3_dev *smmu)
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
bool psmmu_set_busy(struct smmuv3_dev *smmu, unsigned int state)
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

size_t psmmu_strtab_size(struct smmuv3_dev *smmu)
{
	return smmu->strtab_size;
}

int psmmu_activate(struct smmuv3_dev *smmu)
{
	int ret;

	assert(smmu != NULL);
	assert(smmu->state == PSMMU_BUSY);
	assert(smmu->l1std_cnt == 0U);

	ret = smmu_on(smmu);
	if (ret != 0) {
		SMMU_ERROR(smmu, "Failed to switch %s\n", "on");
		return ret;
	}

	smmu->state = PSMMU_ACTIVE;

	SMMU_DEBUG("PSMMU 0x%lx activated\n", smmu->ns_base_pa);
	return 0;
}

int psmmu_deactivate(struct smmuv3_dev *smmu)
{
	int ret;

	assert(smmu != NULL);

	/* Check the number of L2 Stream Table descriptors */
	if (smmu->l1std_cnt != 0U) {
		return -EBUSY;
	}

	ret = smmu_off(smmu);
	if (ret != 0) {
		SMMU_ERROR(smmu, "Failed to switch off\n");
		return ret;
	}

	/* Unmap Command queue */
	ret = xlat_low_va_unmap(smmu->cmdq.q_base, GRANULE_SIZE);
	if (ret != 0) {
		SMMU_ERROR(smmu, "Failed to unmap %s 0x%lx\n",
				"CMDQ", smmu->cmdq.q_base);
		return ret;
	}

	smmu->cmdq.q_base = 0UL;

	/* Unmap Event queue */
	ret = xlat_low_va_unmap(smmu->evtq.q_base, GRANULE_SIZE);
	if (ret != 0) {
		SMMU_ERROR(smmu, "Failed to unmap %s 0x%lx\n",
				"EVTQ", smmu->evtq.q_base);
		return ret;
	}

	smmu->evtq.q_base = 0UL;

	/* Unmap array of L2 Stream Table descriptors */
	ret = xlat_low_va_unmap((uintptr_t)smmu->l2strtab, smmu->strtab_size);
	if (ret != 0) {
		SMMU_ERROR(smmu, "Failed to unmap %s 0x%lx\n",
				"L2 Descrs", (uintptr_t)smmu->l2strtab);
		return ret;
	}

	smmu->l2strtab = NULL;

	/* Unmap L1 Stream Table */
	ret = xlat_low_va_unmap((uintptr_t)smmu->strtab_base, smmu->strtab_size);
	if (ret != 0) {
		SMMU_ERROR(smmu, "Failed to unmap %s 0x%lx\n",
				"L1 Table", (uintptr_t)smmu->strtab_base);
		return ret;
	}

	smmu->strtab_base = NULL;

	SMMU_DEBUG("PSMMU 0x%lx deactivated\n", smmu->ns_base_pa);
	return 0;
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

int psmmu_validate_st_l2(struct smmuv3_dev *smmu, unsigned long sid, uintptr_t *l2tab_pa)
{
	unsigned long l1_idx;
	int ret = 0;

	assert(smmu != NULL);

	/* L1STD index in L1 table */
	l1_idx = L1STD_IDX(sid);

	spinlock_acquire(&smmu->lock);

	/* Check PSMMU state */
	if (smmu->state != PSMMU_ACTIVE) {
		ret = -EINVAL;
		goto err_out;
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
			ret = -EINVAL;
			goto err_out;
		}
	} else {
		/*
		 * Verify that the L2 table was populated in L1STD.
		 * L1STD must be non-zero.
		 */
		if (smmu->strtab_base[l1_idx] == 0UL) {
			SMMU_ERROR(smmu, "STRTAB L2 for SID 0x%lx not found\n", sid);
			ret = -EINVAL;
			goto err_out;
		}

		/* Verify that the number of allocated STEs is zero */
		if ((smmu->l2strtab[l1_idx] & MASK(L2DESC_STE_CNT)) != 0UL) {
			SMMU_ERROR(smmu, "STRTAB L2 for SID 0x%lx has %lu STEs\n",
				sid, smmu->l2strtab[l1_idx] & MASK(L2DESC_STE_CNT));
			ret = -EINVAL;
			goto err_out;
		}

		/* Get physical address of L2 Stream Table */
		*l2tab_pa = smmu->strtab_base[l1_idx] & MASK(STRTAB_L1_DESC_L2PTR);
	}

err_out:
	spinlock_release(&smmu->lock);
	return ret;
}

unsigned long psmmu_get_donated(struct smmuv3_dev *smmu, uintptr_t *donated_pa)
{
	unsigned long num_granules;

	assert(smmu != NULL);

	num_granules = (2UL * (smmu->strtab_size / GRANULE_SIZE)) + 2UL;

	/* Copy physical addresses of donated granules to SRO context */
	(void)memcpy(donated_pa, smmu->donated_pa, num_granules * sizeof(uintptr_t));

	return num_granules;
}

int psmmu_register_st_l1(struct smmuv3_dev *smmu, uintptr_t *donated_pa)
{
	uintptr_t granules_pa[2];
	uintptr_t granules_va[2];
	unsigned long l1tab_gran;
	size_t size;

	assert(smmu != NULL);

	/* Copy physical addresses of donated granules from SRO context */
	(void)memcpy(smmu->donated_pa, donated_pa, sizeof(smmu->donated_pa));

	/* Size of L1 Stream Table */
	size = smmu->strtab_size;

	/* Number of granules */
	l1tab_gran = smmu->strtab_size / GRANULE_SIZE;

	/* Physical address of L1 Stream Table */
	granules_pa[0] = smmu->donated_pa[L1_ST_IDX];

	/* Physical address of  L2 Stream Table descriptors */
	granules_pa[1] = smmu->donated_pa[L2_DS_IDX(l1tab_gran)];

	for (unsigned int i = 0U; i < 2U; i++) {
		assert(ALIGNED(granules_pa[i], size));

		granules_va[i] = xlat_low_va_map(size, MT_RW_DATA | MT_REALM,
						granules_pa[i], true);
		if (granules_va[i] == 0UL) {
			SMMU_ERROR(smmu, "Failed to map 0x%lx\n", granules_pa[i]);
			return -ENOMEM;
		}
	}

	/* Virtual address of L1 Stream Table */
	smmu->strtab_base = (uint64_t *)granules_va[0];

	configure_strtab(smmu, granules_pa[0]);

	/* Virtual address of L2 Stream Table descriptors */
	smmu->l2strtab = (uintptr_t *)granules_va[1];

	SMMU_DEBUG("%s: PA 0x%lx VA 0x%lx size 0x%lx\n", "L1 StrTab",
			granules_pa[0], (uintptr_t)smmu->strtab_base, size);
	SMMU_DEBUG("%s: PA 0x%lx VA 0x%lx size 0x%lx\n", "L2 Descrs",
			granules_pa[1], (uintptr_t)smmu->l2strtab, size);
	return 0;
}

int psmmu_register_st_l2(struct smmuv3_dev *smmu, unsigned long sid,
			 uintptr_t l2tab_pa)
{
	unsigned long l1_idx;
	uintptr_t l2tab_va;
	int ret;

	assert(smmu != NULL);

	/* L1STD index in L1 table */
	l1_idx = L1STD_IDX(sid);

	spinlock_acquire(&smmu->lock);

	/* Map L2 Stream Table */
	l2tab_va = xlat_low_va_map(GRANULE_SIZE, MT_RW_DATA | MT_REALM, l2tab_pa, true);
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
		(void)xlat_low_va_unmap(l2tab_va, GRANULE_SIZE);
		return ret;
	}

	/* Increment number of L2 Stream Table descriptors */
	smmu->l1std_cnt++;

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

int psmmu_release_st_l2(struct smmuv3_dev *smmu, unsigned long sid)
{
	unsigned long l1_idx;
	uintptr_t l2tab_va;
	int ret;

	assert(smmu != NULL);

	/* L1STD index in L1 table */
	l1_idx = L1STD_IDX(sid);

	spinlock_acquire(&smmu->lock);

	/* Verify that the number of allocated STEs is 0 */
	assert((smmu->l2strtab[l1_idx] & MASK(L2DESC_STE_CNT)) == 0UL);

	/* Get virtual address of L2 Stream Table */
	l2tab_va = smmu->l2strtab[l1_idx];

	/* Remove L1STD entry for L2 */
	smmu->strtab_base[l1_idx] = 0UL;
	dsb(ish);

	/* Decrement number of L2 Stream Table descriptors */
	assert(smmu->l1std_cnt != 0U);
	smmu->l1std_cnt--;

	/* Unmap L2 Stream Table */
	ret = xlat_low_va_unmap(l2tab_va, GRANULE_SIZE);
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

int psmmu_register_queues(struct smmuv3_dev *smmu)
{
	uintptr_t granules_pa[2];
	uintptr_t granules_va[2];
	unsigned long l1tab_gran;

	assert(smmu != NULL);

	/* Number of L1 Stream Table granules */
	l1tab_gran = smmu->strtab_size / GRANULE_SIZE;

	/* Physical address of Command queue */
	granules_pa[0] = smmu->donated_pa[CMDQ_IDX(l1tab_gran)];

	/* Physical address of Event queue */
	granules_pa[1] = smmu->donated_pa[EVTQ_IDX(l1tab_gran)];

	for (unsigned int i = 0U; i < 2U; i++) {
		granules_va[i] = xlat_low_va_map(GRANULE_SIZE, MT_RW_DATA | MT_REALM,
						granules_pa[i], true);
		if (granules_va[i] == 0UL) {
			SMMU_ERROR(smmu, "Failed to map 0x%lx\n", granules_pa[i]);
			return -ENOMEM;
		}
	}

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

