/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef GIC_H
#define GIC_H

#include <arch_helpers.h>
#include <stdbool.h>
#include <utils_def.h>

/* The number of implemented List registers, minus one */
#define ICH_VTR_EL2_LIST_REGS_SHIFT	UL(0)
#define ICH_VTR_EL2_LIST_REGS_WIDTH	UL(5)

/* The number of virtual interrupt identifier bits supported */
#define ICH_VTR_EL2_ID_BITS_SHIFT	UL(23)
#define ICH_VTR_EL2_ID_BITS_WIDTH	UL(3)

/* The number of virtual preemption bits implemented, minus one */
#define ICH_VTR_EL2_PRE_BITS_SHIFT	UL(26)
#define ICH_VTR_EL2_PRE_BITS_WIDTH	UL(3)

/* The number of virtual priority bits implemented, minus one */
#define ICH_VTR_EL2_PRI_BITS_SHIFT	UL(29)
#define ICH_VTR_EL2_PRI_BITS_WIDTH	UL(3)

/* Global enable bit for the virtual CPU interface */
#define ICH_HCR_EL2_EN_BIT		(UL(1) << 0)

/* Underflow Interrupt Enable */
#define ICH_HCR_EL2_UIE_BIT		(UL(1) << 1)

/* List Register Entry Not Present Interrupt Enable */
#define ICH_HCR_EL2_LRENPIE_BIT		(UL(1) << 2)

/* No Pending Interrupt Enable */
#define ICH_HCR_EL2_NPIE_BIT		(UL(1) << 3)

/* VM Group 0 Enabled Interrupt Enable */
#define ICH_HCR_EL2_VGRP0EIE_BIT	(UL(1) << 4)

/* VM Group 0 Disabled Interrupt Enable */
#define ICH_HCR_EL2_VGRP0DIE_BIT	(UL(1) << 5)

/* VM Group 1 Enabled Interrupt Enable */
#define ICH_HCR_EL2_VGRP1EIE_BIT	(UL(1) << 6)

/* VM Group 1 Disabled Interrupt Enable */
#define ICH_HCR_EL2_VGRP1DIE_BIT	(UL(1) << 7)

/*
 * When FEAT_GICv4p1 is implemented:
 * Controls whether deactivation of virtual SGIs
 * can increment ICH_HCR_EL2.EOIcount
 */
#define ICH_HCR_EL2_VSGIEEOICOUNT_BIT	(UL(1) << 8)

/*
 * Trap all EL1 accesses to System registers
 * that are common to Group 0 and Group 1 to EL2
 */
#define ICH_HCR_EL2_TC_BIT		(UL(1) << 10)

/*
 * Trap all EL1 accesses to ICC_* and ICV_* System registers
 * for Group 0 interrupts to EL2
 */
#define ICH_HCR_EL2_TALL0_BIT		(UL(1) << 11)

/*
 * Trap all EL1 accesses to ICC_* and ICV_* System registers
 * for Group 1 interrupts to EL2
 */
#define ICH_HCR_EL2_TALL1_BIT		(UL(1) << 12)

/* Trap all locally generated SEIs */
#define ICH_HCR_EL2_TSEI_BIT		(UL(1) << 13)

/*
 * When FEAT_GICv3_TDIR is implemented:
 * Trap EL1 writes to ICC_DIR_EL1 and ICV_DIR_EL1
 */
#define ICH_HCR_EL2_TDIR_BIT		(UL(1) << 14)

/*
 * When ICH_VTR_EL2.DVIM == 1:
 * Directly-injected Virtual Interrupt Mask
 */
#define ICH_HCR_EL2_DVIM_BIT		(UL(1) << 15)

#define ICH_HCR_EL2_EOI_COUNT_SHIFT	UL(27)
#define ICH_HCR_EL2_EOI_COUNT_WIDTH	UL(5)
#define ICH_HCR_EL2_EOI_COUNT_MASK	MASK(ICH_HCR_EL2_EOI_COUNT)

/* Virtual INTID of the interrupt */
#define ICH_LR_VINTID_SHIFT		UL(0)
#define ICH_LR_VINTID_WIDTH		UL(32)
#define ICH_LR_VINTID_MASK		MASK(ICH_LR_VINTID)

/*
 * Physical INTID, for hardware interrupts
 * When ICH_LR<n>_EL2.HW is 0 (there is no corresponding physical interrupt),
 * this field has the following meaning:
 *	Bits[44:42] : RES0.
 *	Bit[41] : EOI. If this bit is 1, then when the interrupt identified by
 *		vINTID is deactivated, a maintenance interrupt is asserted.
 *	Bits[40:32] : RES0
 */
#define ICH_LR_PINTID_SHIFT		UL(32)
#define ICH_LR_PINTID_WIDTH		UL(13)
#define ICH_LR_PINTID_MASK		MASK(ICH_LR_PINTID)

#define ICH_LR_EOI_BIT			(UL(1) << 41)

/* The priority of this interrupt */
#define ICH_LR_PRIORITY_SHIFT		UL(48)
#define ICH_LR_PRIORITY_WIDTH		UL(8)
#define ICH_LR_PRIORITY_MASK		MASK(ICH_LR_PRIORITY)

/* The group for this virtual interrupt */
#define ICH_LR_GROUP_BIT		(UL(1) << 60)

/*
 * Indicates whether this virtual interrupt
 * maps directly to a hardware interrupt
 */
#define ICH_LR_HW_BIT			(UL(1) << 61)

/*
 * The state of the interrupt:
 * 0b00	Invalid (Inactive)
 * 0b01	Pending
 * 0b10	Active
 * 0b11	Pending and active
 */
#define ICH_LR_STATE_SHIFT		UL(62)
#define ICH_LR_STATE_WIDTH		UL(2)
#define ICH_LR_STATE_MASK		MASK(ICH_LR_STATE)

#define ICH_LR_STATE_INVALID		INPLACE(ICH_LR_STATE, UL(0))
#define ICH_LR_STATE_PENDING		INPLACE(ICH_LR_STATE, UL(1))
#define ICH_LR_STATE_ACTIVE		INPLACE(ICH_LR_STATE, UL(2))
#define ICH_LR_STATE_PENDING_ACTIVE	INPLACE(ICH_LR_STATE, UL(3))

/*
 * Maximum number of Interrupt Controller
 * Hyp Active Priorities Group 0/1 Registers [0..3]
 */
#define ICH_MAX_APRS		4U

/* Maximum number of Interrupt Controller List Registers */
#define ICH_MAX_LRS		16U

/* Mask for bits identifying maintenance interrupt that have fired. */
#define ICH_MISR_EL2_SHIFT	UL(0)
#define ICH_MISR_EL2_WIDTH	UL(8)
#define ICH_MISR_EL2_MASK	MASK(ICH_MISR_EL2)

struct gic_cpu_state {
	/* Interrupt Controller Hyp Active Priorities Group 0 Registers */
	unsigned long ich_ap0r_el2[ICH_MAX_APRS];
	/* Interrupt Controller Hyp Active Priorities Group 1 Registers */
	unsigned long ich_ap1r_el2[ICH_MAX_APRS];
	/* GICv3 Virtual Machine Control Register */
	unsigned long ich_vmcr_el2;		/* PlaneRun in/out */
	/* Interrupt Controller Hyp Control Register */
	unsigned long ich_hcr_el2;		/* PlaneRun in/out */

	/* GICv3 List Registers */
	unsigned long ich_lr_el2[ICH_MAX_LRS];	/* PlaneRun in/out */
	/* GICv3 Maintenance Interrupt State Register */
	unsigned long ich_misr_el2;		/* PlaneRun out */
};

struct rmi_rec_enter;
struct rmi_rec_exit;

void gic_get_virt_features(void);
unsigned int gic_vgic_get_num_lrs(void);

void gic_copy_state_to_plane_exit(struct gic_cpu_state *gicstate,
	unsigned long *gicv3_lrs,
	unsigned long *gicv3_hcr,
	unsigned long *gicv3_misr,
	unsigned long *gicv3_vmcr);

/*
 * Validate the GICv3 List Registers supplied by the Host.
 *
 * For every active (non-invalid) entry in @gicv3_lrs the following
 * constraints are checked:
 *   - HW == '0': the RMM Specification forbids hardware-backed virtual
 *     interrupts.
 *   - No two active entries may carry the same vINTID: having duplicate
 *     vINTIDs across List Registers produces UNPREDICTABLE behaviour.
 *
 * Returns true if all constraints are satisfied, false otherwise.
 */
bool gic_validate_lrs(unsigned long *gicv3_lrs);

/*
 * Validate the GICv3 List Registers supplied by the Host, as read from the
 * hardware registers.
 */
bool gic_validate_vgic(void);

bool gic_is_any_interrupt_pending(void);
void gic_restore_state(struct gic_cpu_state *gicstate);
void gic_save_state(struct gic_cpu_state *gicstate);
void gic_disable_virtual_cpuif(void);

/*
 * Initialise the vGIC state for a Plane entry.
 *
 * Copies @gicv3_lrs and @gicv3_hcr into @gicstate
 * then unconditionally sets the
 * VSGIEEOICOUNT and DVIM bits in ICH_HCR_EL2 to disable virtual SGI
 * end-of-interrupt counting and direct-injection of virtual interrupts,
 * before writing the resulting state to the hardware registers.
 */
void gic_init_vgic_state(struct gic_cpu_state *gicstate,
			unsigned long *gicv3_lrs,
			unsigned long gicv3_hcr);

static inline unsigned long gic_get_ich_vtr(void)
{
	return read_ich_vtr_el2();
}

#endif /* GIC_H */
