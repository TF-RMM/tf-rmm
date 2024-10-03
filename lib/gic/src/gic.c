/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch_helpers.h>
#include <assert.h>
#include <debug.h>
#include <gic.h>
#include <smc-rmi.h>
#include <stdbool.h>
#include <string.h>

/* The macros below fall through to case (n - 1) */
#define READ_ICH_LR_EL2(n)	{				\
	case (n):						\
	gicstate->ich_lr_el2[n] = read_ich_lr##n##_el2();	\
	}

#define WRITE_ICH_LR_EL2(n)	{				\
	case (n):						\
	write_ich_lr##n##_el2(gicstate->ich_lr_el2[n]);		\
	}

#define READ_ICH_APR_EL2(n)	{				\
	case (n):						\
	gicstate->ich_ap0r_el2[n] = read_ich_ap0r##n##_el2();	\
	gicstate->ich_ap1r_el2[n] = read_ich_ap1r##n##_el2();	\
	}

#define WRITE_ICH_APR_EL2(n)	{				\
	case (n):						\
	write_ich_ap0r##n##_el2(gicstate->ich_ap0r_el2[n]);	\
	write_ich_ap1r##n##_el2(gicstate->ich_ap1r_el2[n]);	\
	}

/* GIC virtualization features */
struct gic_virt_feature_s {

	/* Number of implemented List registers, minus 1 */
	unsigned int nr_lrs;

	/*
	 * Number of Interrupt Controller Hyp Active
	 * Priorities Group 0/1 Registers [0..3]
	 */
	unsigned int nr_aprs;

	/* RES0 bits in the Priority field in the LRs */
	unsigned long pri_res0_mask;

	/* Max virtual interrupt identifier */
	unsigned long max_vintid;

	/* Support for extended INTID */
	bool ext_range;
};

static struct gic_virt_feature_s gic_virt_feature;

/*
 * Read supported GIC virtualization features
 * and set configuration variables.
 */
void gic_get_virt_features(void)
{
	/* Interrupt Controller VGIC Type Register */
	unsigned long vtr = read_ich_vtr_el2();

	unsigned long nr_pre_bits;
	unsigned long nr_pri_bits;

	/* Number of implemented List registers, minus 1 */
	gic_virt_feature.nr_lrs =
			(unsigned int)EXTRACT(ICH_VTR_EL2_LIST_REGS, vtr);

	assert(gic_virt_feature.nr_lrs < ICH_MAX_LRS);

	/* Number of virtual preemption bits implemented */
	nr_pre_bits = EXTRACT(ICH_VTR_EL2_PRE_BITS, vtr) + 1U;

	/*
	 * Implementation must implement at least 32 levels
	 * of virtual priority (5 priority bits)
	 */
	assert(nr_pre_bits >= 5UL);

	/*
	 * Number of Interrupt Controller Hyp Active Priorities
	 * Group 0/1 Registers [0..3], minus 1
	 */
	gic_virt_feature.nr_aprs =
			(unsigned int)((1UL << (nr_pre_bits - 5UL)) - 1UL);
	/*
	 * Get max virtual interrupt identifier
	 * Number of virtual interrupt identifier bits supported:
	 * 0b000 : 16 bits
	 * 0b001 : 24 bits
	 */
	gic_virt_feature.max_vintid =
				(EXTRACT(ICH_VTR_EL2_ID_BITS, vtr) == 0UL) ?
				((UL(1) << 16U) - 1UL) : ((UL(1) << 24U) - 1UL);

	/* Number of virtual priority bits implemented */
	nr_pri_bits = EXTRACT(ICH_VTR_EL2_PRI_BITS, vtr) + 1UL;

	/* RES0 bits in the Priority field in the LRs */
	gic_virt_feature.pri_res0_mask =
			(1UL << (ICH_LR_PRIORITY_WIDTH - nr_pri_bits)) - 1UL;

	/* Support for extended INTID */
	gic_virt_feature.ext_range = (read_icc_ctrl_el1() &
					ICC_CTLR_EL1_EXT_RANGE_BIT) != 0UL;
	VERBOSE("GIC with%s ExtRange:\n",
		gic_virt_feature.ext_range ? "" : "out");
	VERBOSE(" nr_lrs=%u nr_aprs=%u max_vintid=%lu\n",
		gic_virt_feature.nr_lrs, gic_virt_feature.nr_aprs,
		gic_virt_feature.max_vintid);
	VERBOSE(" nr_pri_bits=%lu pri_res0_mask=0x%lx\n",
		nr_pri_bits, gic_virt_feature.pri_res0_mask);
}

void gic_cpu_state_init(struct gic_cpu_state *gicstate)
{
	(void)memset(gicstate, 0, sizeof(*gicstate));
	gicstate->ich_hcr_el2 =
		ICH_HCR_EL2_EN_BIT |	/* Enable virtual CPU interface */
		ICH_HCR_EL2_VSGIEEOICOUNT_BIT | /* Virtual SGIs not supported */
		ICH_HCR_EL2_DVIM_BIT;	/* Direct-injection not supported */
}

void gic_copy_state_from_rec_entry(struct gic_cpu_state *gicstate,
			    struct rmi_rec_enter *rec_enter)
{
	unsigned int i;

	/* Copy List Registers */
	for (i = 0U; i <= gic_virt_feature.nr_lrs; i++) {
		gicstate->ich_lr_el2[i] = rec_enter->gicv3_lrs[i];
	}

	/* Get bits from NS hypervisor */
	gicstate->ich_hcr_el2 &= ~ICH_HCR_EL2_NS_MASK;
	gicstate->ich_hcr_el2 |= rec_enter->gicv3_hcr & ICH_HCR_EL2_NS_MASK;
}

void gic_copy_state_to_rec_exit(struct gic_cpu_state *gicstate,
			  struct rmi_rec_exit *rec_exit)
{
	unsigned int i;

	/* Copy List Registers */
	for (i = 0U; i <= gic_virt_feature.nr_lrs; i++) {
		rec_exit->gicv3_lrs[i] = gicstate->ich_lr_el2[i];
	}

	rec_exit->gicv3_misr = gicstate->ich_misr_el2;
	rec_exit->gicv3_vmcr = gicstate->ich_vmcr_el2;
	rec_exit->gicv3_hcr = gicstate->ich_hcr_el2 &
		(ICH_HCR_EL2_EOI_COUNT_MASK | ICH_HCR_EL2_NS_MASK);
}

static bool is_valid_vintid(unsigned long intid)
{
	/* Check for INTID [0..1019] and [8192..] */
	if (((intid) <= MAX_SPI_ID) ||
	   (((intid) >= MIN_LPI_ID) && ((intid) <= gic_virt_feature.max_vintid))) {
		return true;
	}

	/*
	 * If extended INTID range sopported, check for
	 * Extended PPI [1056..1119] and Extended SPI [4096..5119]
	 */
	return (gic_virt_feature.ext_range ?
		((((intid) >= MIN_EPPI_ID) && ((intid) <= MAX_EPPI_ID)) ||
		 (((intid) >= MIN_ESPI_ID) && ((intid) <= MAX_ESPI_ID))) :
		false);
}

bool gic_validate_state(struct rmi_rec_enter *rec_enter)
{
	unsigned int i, j;
	unsigned long hcr = rec_enter->gicv3_hcr;

	/* Validate rec_entry.gicv3_hcr MBZ bits */
	if ((hcr & ~ICH_HCR_EL2_NS_MASK) != 0UL) {
		return false;
	}

	for (i = 0U; i <= gic_virt_feature.nr_lrs; i++) {
		unsigned long lr = rec_enter->gicv3_lrs[i];
		unsigned long intid = EXTRACT(ICH_LR_VINTID, lr);

		if ((lr & ICH_LR_STATE_MASK) == ICH_LR_STATE_INVALID) {
			continue;
		}

		/* The RMM Specification imposes the constraint that HW == '0' */
		if (((lr & ICH_LR_HW_BIT) != 0UL) ||
		    /* Check RES0 bits in the Priority field */
		   ((EXTRACT(ICH_LR_PRIORITY, lr) &
			gic_virt_feature.pri_res0_mask) != 0UL) ||
		    /* Only the EOI bit in the pINTID is allowed to be set */
		   ((lr & ICH_LR_PINTID_MASK & ~ICH_LR_EOI_BIT) != 0UL) ||
		    /* Check if vINTID is in the valid range */
		   !is_valid_vintid(intid)) {
			return false;
		}

		/*
		 * Behavior is UNPREDICTABLE if two or more List Registers
		 * specify the same vINTID.
		 */
		for (j = i + 1U; j <= gic_virt_feature.nr_lrs; j++) {
			unsigned long _lr = rec_enter->gicv3_lrs[j];
			unsigned long _intid = EXTRACT(ICH_LR_VINTID, _lr);

			if ((_lr & ICH_LR_STATE_MASK) == ICH_LR_STATE_INVALID) {
				continue;
			}

			if (intid == _intid) {
				return false;
			}
		}
	}

	return true;
}

/* Save ICH_LR<n>_EL2 registers [n...0] */
static void read_lrs(struct gic_cpu_state *gicstate)
{
	switch (gic_virt_feature.nr_lrs) {
	READ_ICH_LR_EL2(15);
	READ_ICH_LR_EL2(14);
	READ_ICH_LR_EL2(13);
	READ_ICH_LR_EL2(12);
	READ_ICH_LR_EL2(11);
	READ_ICH_LR_EL2(10);
	READ_ICH_LR_EL2(9);
	READ_ICH_LR_EL2(8);
	READ_ICH_LR_EL2(7);
	READ_ICH_LR_EL2(6);
	READ_ICH_LR_EL2(5);
	READ_ICH_LR_EL2(4);
	READ_ICH_LR_EL2(3);
	READ_ICH_LR_EL2(2);
	READ_ICH_LR_EL2(1);
	FALLTHROUGH;
	default:
	READ_ICH_LR_EL2(0);
	}
}

/* Restore ICH_LR<n>_EL2 registers [n...0] */
static void write_lrs(struct gic_cpu_state *gicstate)
{
	switch (gic_virt_feature.nr_lrs) {
	WRITE_ICH_LR_EL2(15);
	WRITE_ICH_LR_EL2(14);
	WRITE_ICH_LR_EL2(13);
	WRITE_ICH_LR_EL2(12);
	WRITE_ICH_LR_EL2(11);
	WRITE_ICH_LR_EL2(10);
	WRITE_ICH_LR_EL2(9);
	WRITE_ICH_LR_EL2(8);
	WRITE_ICH_LR_EL2(7);
	WRITE_ICH_LR_EL2(6);
	WRITE_ICH_LR_EL2(5);
	WRITE_ICH_LR_EL2(4);
	WRITE_ICH_LR_EL2(3);
	WRITE_ICH_LR_EL2(2);
	WRITE_ICH_LR_EL2(1);
	FALLTHROUGH;
	default:
	WRITE_ICH_LR_EL2(0);
	}
}

/* Save ICH_AP0R<n>_EL2 and ICH_AP1R<n>_EL2 registers [n...0] */
static void read_aprs(struct gic_cpu_state *gicstate)
{
	switch (gic_virt_feature.nr_aprs) {
	READ_ICH_APR_EL2(3);
	READ_ICH_APR_EL2(2);
	READ_ICH_APR_EL2(1);
	FALLTHROUGH;
	default:
	READ_ICH_APR_EL2(0);
	}
}

/* Restore ICH_AP0R<n>_EL2 and ICH_AP1R<n>_EL2 registers [n...0] */
static void write_aprs(struct gic_cpu_state *gicstate)
{
	switch (gic_virt_feature.nr_aprs) {
	WRITE_ICH_APR_EL2(3);
	WRITE_ICH_APR_EL2(2);
	WRITE_ICH_APR_EL2(1);
	FALLTHROUGH;
	default:
	WRITE_ICH_APR_EL2(0);
	}
}

void gic_restore_state(struct gic_cpu_state *gicstate)
{
	write_aprs(gicstate);
	write_lrs(gicstate);

	write_ich_vmcr_el2(gicstate->ich_vmcr_el2);
	write_ich_hcr_el2(gicstate->ich_hcr_el2);
}

void gic_save_state(struct gic_cpu_state *gicstate)
{
	read_aprs(gicstate);
	read_lrs(gicstate);

	/* Save the status, including MISR */
	gicstate->ich_vmcr_el2 = read_ich_vmcr_el2();
	gicstate->ich_hcr_el2 = read_ich_hcr_el2();
	gicstate->ich_misr_el2 = read_ich_misr_el2();

	/* On REC exit, set ICH_HCR_EL2.En == '0' */
	write_ich_hcr_el2(gicstate->ich_hcr_el2 & ~ICH_HCR_EL2_EN_BIT);
}

/* Return number of List registers discovered, minus 1 */
unsigned int gic_vgic_get_num_lrs(void)
{
	return gic_virt_feature.nr_lrs;
}
