/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors
 */

#include <arch_helpers.h>
#include <assert.h>
#include <errno.h>
#include <granule.h>
#include <memory.h>
#include <rmm_el3_ifc.h>
#include <smc-rmi.h>
#include <smmuv3_arch.h>
#include <smmuv3_priv.h>
#include <smmuv3_psmmu.h>
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
	int ret __unused;
	uintptr_t va;

	assert(smmu != NULL);

	/* Decommit and depopulate Event queue */
	if (smmu_va_is_committed(smmu->evtq.q_base)) {
		va = smmu->evtq.q_base;
		ret = smmuv3_arch_decommit(va, GRANULE_SIZE);
		assert(ret == 0);
		ret = smmuv3_arch_depopulate(va, GRANULE_SIZE);
		assert(ret == 0);
		smmu->evtq.q_base = smmu_va_mark_reserved(va);
	}

	/* Decommit and depopulate Command queue */
	if (smmu_va_is_committed(smmu->cmdq.q_base)) {
		va = smmu->cmdq.q_base;
		ret = smmuv3_arch_decommit(va, GRANULE_SIZE);
		assert(ret == 0);
		ret = smmuv3_arch_depopulate(va, GRANULE_SIZE);
		assert(ret == 0);
		smmu->cmdq.q_base = smmu_va_mark_reserved(va);
	}

	/* Decommit and depopulate L1 Stream Table */
	if (smmu_va_is_committed(smmu->strtab_base)) {
		va = (uintptr_t)smmu->strtab_base;
		ret = smmuv3_arch_decommit(va, smmu->strtab_size);
		assert(ret == 0);
		ret = smmuv3_arch_depopulate(va, smmu->strtab_size);
		assert(ret == 0);
		smmu->strtab_base = (uint64_t *)smmu_va_mark_reserved(va);
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
	unsigned long l1_ents;
	struct granule *g_l2tab;
	uintptr_t va;
	uintptr_t l2tab_pa;
	unsigned short refcount;
	int ret __unused;

	assert(smmu != NULL);

	if (smmu->state == PSMMU_ACTIVE) {
		smmu_off(smmu);
	}

	/*
	 * Force-cleanup any L2 Stream Tables that are still committed in the
	 * L2 pool.
	 */
	if (smmu_va_is_committed(smmu->strtab_base)) {
		l1_ents = smmu->strtab_size / STRTAB_L1_DESC_SIZE;

		for (unsigned long i = 0UL; i < l1_ents; i++) {
			if (smmu->strtab_base[i] == 0UL) {
				continue;
			}

			l2tab_pa = smmu_l1std_l2tab_pa(smmu, i);
			va = smmu_l2tab_va(smmu, i);

			ret = smmuv3_arch_decommit(va, GRANULE_SIZE);
			assert(ret == 0);
			ret = smmuv3_arch_depopulate(va, GRANULE_SIZE);
			assert(ret == 0);

			g_l2tab = find_lock_granule(l2tab_pa,
						    GRANULE_STATE_PSMMU_ST_L2);
			if (g_l2tab != NULL) {
				refcount = granule_refcount_read(g_l2tab);
				if (refcount != 0U) {
					granule_refcount_dec(g_l2tab, refcount);
				}
				granule_unlock_transition(g_l2tab, GRANULE_STATE_INTERNAL);
			}

			smmu->strtab_base[i] = 0UL;
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
 * configured STEs and extracts its physical address (for destroy).
 */
static int validate_st_l2(struct smmuv3_dev *smmu, unsigned long l1_idx,
			  unsigned long sid, uintptr_t *l2tab_pa)
{
	struct granule *g_l2tab;
	uintptr_t pa;
	unsigned short refcount;

	/* Check PSMMU state */
	if (smmu->state != PSMMU_ACTIVE) {
		return -EINVAL;
	}

	assert(smmu_va_is_committed(smmu->strtab_base));

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

		pa = smmu_l1std_l2tab_pa(smmu, l1_idx);
		g_l2tab = find_lock_granule(pa, GRANULE_STATE_PSMMU_ST_L2);
		assert(g_l2tab != NULL);

		refcount = granule_refcount_read(g_l2tab);
		granule_unlock(g_l2tab);

		/* Verify that the number of configured STEs is zero */
		if (refcount != 0U) {
			SMMU_ERROR(smmu, "STRTAB L2 for SID 0x%lx has %lu STEs\n",
				sid, (unsigned long)refcount);
			return -EINVAL;
		}

		/* Extract physical address of L2 Stream Table */
		*l2tab_pa = pa;
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

	range_base[(unsigned int)PSMMU_MEM_RANGE_CMDQ] = smmu->cmdq_pa;
	range_size[(unsigned int)PSMMU_MEM_RANGE_CMDQ] = 1UL;

	range_base[(unsigned int)PSMMU_MEM_RANGE_EVTQ] = smmu->evtq_pa;
	range_size[(unsigned int)PSMMU_MEM_RANGE_EVTQ] = 1UL;
}

int smmuv3_psmmu_register_st_l1(struct smmuv3_dev *smmu, uintptr_t l1_st_pa)
{
	uintptr_t l1_va;
	size_t size;
	int ret __unused;

	assert(smmu != NULL);

	/* Size of L1 Stream Table */
	size = smmu->strtab_size;

	/* Pre-reserved VA from boot (clear tag to get actual VA) */
	l1_va = smmu_va_get_reserved(smmu->strtab_base);

	assert(ALIGNED(l1_st_pa, size));

	ret = smmuv3_arch_populate(l1_va, l1_st_pa, size, MT_RW_DATA | MT_REALM);
	if (ret != 0) {
		return -ENOMEM;
	}

	ret = smmuv3_arch_commit_clear(l1_va, size);
	if (ret != 0) {
		ret = smmuv3_arch_depopulate(l1_va, size);
		assert(ret == 0);
		return -ENOMEM;
	}

	/* Store base PA for reclaim during deactivation */
	smmu->l1_st_pa = l1_st_pa;

	/* Clear the tag: store VA (bit 0 clear) */
	smmu->strtab_base = (uint64_t *)l1_va;

	configure_strtab(smmu, l1_st_pa);

	SMMU_DEBUG("%s: PA 0x%lx VA 0x%lx size 0x%lx\n", "L1 StrTab",
			l1_st_pa, (uintptr_t)smmu->strtab_base, size);
	return 0;
}

int smmuv3_psmmu_register_st_l2(struct smmuv3_dev *smmu, unsigned long sid,
				uintptr_t l2tab_pa)
{
	unsigned long l1_idx;
	struct granule *g_l2tab;
	uintptr_t l2tab_va;
	int ret __unused;

	assert(smmu != NULL);

	/* L1STD index in L1 table */
	l1_idx = L1STD_IDX(sid);

	spinlock_acquire(&smmu->lock);

	ret = validate_st_l2(smmu, l1_idx, sid, NULL);
	if (ret != 0) {
		spinlock_release(&smmu->lock);
		return ret;
	}

	/* Compute L2 table VA from the reserved pool */
	l2tab_va = smmu_l2tab_va(smmu, l1_idx);

	/* Populate and commit the reserved VA with the L2 table PA */
	ret = smmuv3_arch_populate(l2tab_va, l2tab_pa, GRANULE_SIZE,
				   MT_RW_DATA | MT_REALM);
	if (ret != 0) {
		spinlock_release(&smmu->lock);
		return -ENOMEM;
	}

	ret = smmuv3_arch_commit_clear(l2tab_va, GRANULE_SIZE);
	if (ret != 0) {
		ret = smmuv3_arch_depopulate(l2tab_va, GRANULE_SIZE);
		assert(ret == 0);
		spinlock_release(&smmu->lock);
		return -ENOMEM;
	}

	g_l2tab = find_lock_granule(l2tab_pa, GRANULE_STATE_INTERNAL);
	if (g_l2tab == NULL) {
		ret = smmuv3_arch_decommit(l2tab_va, GRANULE_SIZE);
		assert(ret == 0);
		ret = smmuv3_arch_depopulate(l2tab_va, GRANULE_SIZE);
		assert(ret == 0);
		spinlock_release(&smmu->lock);
		SMMU_ERROR(smmu, "Failed to lock L2 Stream Table granule 0x%lx\n",
				l2tab_pa);
		return -EINVAL;
	}
	granule_unlock_transition(g_l2tab, GRANULE_STATE_PSMMU_ST_L2);

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
		int cleanup_ret __unused;

		/* Clear L1STD */
		smmu->strtab_base[l1_idx] = 0UL;
		dsb(ish);

		g_l2tab = find_lock_granule(l2tab_pa, GRANULE_STATE_PSMMU_ST_L2);
		assert(g_l2tab != NULL);
		granule_unlock_transition(g_l2tab, GRANULE_STATE_INTERNAL);

		/* Decommit and depopulate L2 Stream Table */
		cleanup_ret = smmuv3_arch_decommit(l2tab_va, GRANULE_SIZE);
		assert(cleanup_ret == 0);
		cleanup_ret = smmuv3_arch_depopulate(l2tab_va, GRANULE_SIZE);
		assert(cleanup_ret == 0);
		spinlock_release(&smmu->lock);
		return ret;
	}

	/* Increment L1 Stream Table refcount */
	smmu->l1_refcnt++;

	spinlock_release(&smmu->lock);

	/* coverity[null_field:SUPPRESS] */
	SMMU_DEBUG("L1STD[%lu] 0x%lx for SID 0x%lx: L2 table VA 0x%lx PA 0x%lx\n",
		   l1_idx, smmu->strtab_base[l1_idx], sid,
		   l2tab_va, l2tab_pa);
	return ret;
}

int smmuv3_psmmu_release_st_l2(struct smmuv3_dev *smmu, unsigned long sid,
				uintptr_t *l2tab_pa)
{
	unsigned long l1_idx;
	struct granule *g_l2tab;
	uintptr_t l2tab_va;
	int ret __unused;

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

	/* Compute L2 table VA from the reserved pool */
	l2tab_va = smmu_l2tab_va(smmu, l1_idx);

	/* Remove L1STD entry for L2 */
	smmu->strtab_base[l1_idx] = 0UL;
	dsb(ish);

	/* Decrement L1 Stream Table refcount */
	assert(smmu->l1_refcnt != 0U);
	smmu->l1_refcnt--;

	/* Decommit and depopulate L2 Stream Table */
	ret = smmuv3_arch_decommit(l2tab_va, GRANULE_SIZE);
	assert(ret == 0);

	ret = smmuv3_arch_depopulate(l2tab_va, GRANULE_SIZE);
	assert(ret == 0);

	/* Invalidate configuration structure */
	ret = inval_cached_ste(smmu, sid, false);

	g_l2tab = find_lock_granule(*l2tab_pa, GRANULE_STATE_PSMMU_ST_L2);
	assert(g_l2tab != NULL);
	assert(granule_refcount_read(g_l2tab) == 0U);
	granule_unlock_transition(g_l2tab, GRANULE_STATE_INTERNAL);

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
	int ret __unused;

	assert(smmu != NULL);

	/* Physical address of Command queue */
	granules_pa[0] = cmdq_pa;

	/* Physical address of Event queue */
	granules_pa[1] = evtq_pa;

	/* Pre-reserved VAs from boot (clear tag to get actual VA) */
	granules_va[0] = smmu_va_get_reserved(smmu->cmdq.q_base);
	granules_va[1] = smmu_va_get_reserved(smmu->evtq.q_base);

	for (unsigned int i = 0U; i < 2U; i++) {
		ret = smmuv3_arch_populate(granules_va[i], granules_pa[i],
					   GRANULE_SIZE, MT_RW_DATA | MT_REALM);
		if (ret != 0) {
			/* Undo previously committed entries */
			for (unsigned int j = 0U; j < i; j++) {
				ret = smmuv3_arch_decommit(granules_va[j],
							GRANULE_SIZE);
				assert(ret == 0);
				ret = smmuv3_arch_depopulate(granules_va[j],
							GRANULE_SIZE);
				assert(ret == 0);
			}
			return -ENOMEM;
		}

		ret = smmuv3_arch_commit_clear(granules_va[i], GRANULE_SIZE);
		if (ret != 0) {
			/* Current entry is populated only - depopulate */
			ret = smmuv3_arch_depopulate(granules_va[i],
						GRANULE_SIZE);
			assert(ret == 0);

			/* Previous entries are committed - decommit + depopulate */
			for (unsigned int j = 0U; j < i; j++) {
				ret = smmuv3_arch_decommit(granules_va[j],
							GRANULE_SIZE);
				assert(ret == 0);
				ret = smmuv3_arch_depopulate(granules_va[j],
							GRANULE_SIZE);
				assert(ret == 0);
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
