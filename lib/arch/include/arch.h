/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef ARCH_H
#define ARCH_H

#include <utils_def.h>

/* Cache line size */
#define CACHE_WRITEBACK_GRANULE	UL(64)

/* Timer interrupt IDs defined by the Server Base System Architecture */
#define EL1_VIRT_TIMER_PPI	UL(27)
#define EL1_PHYS_TIMER_PPI	UL(30)

/* Counter-timer Physical Offset register */
#define CNTPOFF_EL2		S3_4_C14_C0_6

/* MPAM0 Register */
#define MPAM0_EL1		S3_0_C10_C5_1

/* Interrupt Controller registers */
#define ICC_HPPIR1_EL1		S3_0_C12_C12_2
#define ICC_SRE_EL2		S3_4_C12_C9_5

/* Interrupt Controller Control Register */
#define	ICC_CTLR_EL1		S3_0_C12_C12_4

#define ICC_CTLR_EL1_EXT_RANGE_SHIFT	UL(19)
#define ICC_CTLR_EL1_EXT_RANGE_BIT	INPLACE(ICC_CTLR_EL1_EXT_RANGE, UL(1))

/* Virtual GIC registers */
#define ICH_AP0R0_EL2		S3_4_C12_C8_0
#define ICH_AP0R1_EL2		S3_4_C12_C8_1
#define ICH_AP0R2_EL2		S3_4_C12_C8_2
#define ICH_AP0R3_EL2		S3_4_C12_C8_3
#define ICH_AP1R0_EL2		S3_4_C12_C9_0
#define ICH_AP1R1_EL2		S3_4_C12_C9_1
#define ICH_AP1R2_EL2		S3_4_C12_C9_2
#define ICH_AP1R3_EL2		S3_4_C12_C9_3

#define ICH_LR0_EL2		S3_4_C12_C12_0
#define ICH_LR1_EL2		S3_4_C12_C12_1
#define ICH_LR2_EL2		S3_4_C12_C12_2
#define ICH_LR3_EL2		S3_4_C12_C12_3
#define ICH_LR4_EL2		S3_4_C12_C12_4
#define ICH_LR5_EL2		S3_4_C12_C12_5
#define ICH_LR6_EL2		S3_4_C12_C12_6
#define ICH_LR7_EL2		S3_4_C12_C12_7
#define ICH_LR8_EL2		S3_4_C12_C13_0
#define ICH_LR9_EL2		S3_4_C12_C13_1
#define ICH_LR10_EL2		S3_4_C12_C13_2
#define ICH_LR11_EL2		S3_4_C12_C13_3
#define ICH_LR12_EL2		S3_4_C12_C13_4
#define ICH_LR13_EL2		S3_4_C12_C13_5
#define ICH_LR14_EL2		S3_4_C12_C13_6
#define ICH_LR15_EL2		S3_4_C12_C13_7

#define ICH_HCR_EL2		S3_4_C12_C11_0
#define ICH_VTR_EL2		S3_4_C12_C11_1
#define ICH_MISR_EL2		S3_4_C12_C11_2
#define ICH_VMCR_EL2		S3_4_C12_C11_7

/* RNDR definition */
#define RNDR			S3_3_C2_C4_0

/* CLIDR definitions */
#define LOC_SHIFT		U(24)
#define CTYPE_SHIFT(n)		U(3 * ((n) - 1))
#define CLIDR_FIELD_WIDTH	U(3)

/* CSSELR definitions */
#define LEVEL_SHIFT		U(1)

/* Data cache set/way op type defines */
#define DCISW			U(0x0)
#define DCCISW			U(0x1)
#define DCCSW			U(0x2)

#define TCR_EL2_T0SZ_SHIFT	UL(0)
#define TCR_EL2_T0SZ_WIDTH	UL(6)
#define TCR_EL2_T0SZ_MASK	MASK(TCR_EL2_T0SZ)

#define TCR_EL2_T1SZ_SHIFT	UL(16)
#define TCR_EL2_T1SZ_WIDTH	UL(6)
#define TCR_EL2_T1SZ_MASK	MASK(TCR_EL2_T0SZ)

#define TCR_EL2_EPD0_SHIFT	UL(7)
#define TCR_EL2_EPD0_WIDTH	UL(1)
#define TCR_EL2_EPD0_BIT	INPLACE(TCR_EL2_EPD0, UL(1))

#define TCR_EL2_IRGN0_SHIFT	UL(8)
#define TCR_EL2_IRGN0_WIDTH	UL(2)
#define TCR_EL2_IRGN0_WBWA	INPLACE(TCR_EL2_IRGN0, UL(1))

#define TCR_EL2_ORGN0_SHIFT	UL(10)
#define TCR_EL2_ORGN0_WIDTH	UL(2)
#define TCR_EL2_ORGN0_WBWA	INPLACE(TCR_EL2_ORGN0, UL(1))

#define TCR_EL2_IRGN1_SHIFT	UL(24)
#define TCR_EL2_IRGN1_WIDTH	UL(2)
#define TCR_EL2_IRGN1_WBWA	INPLACE(TCR_EL2_IRGN1, UL(1))

#define TCR_EL2_ORGN1_SHIFT	UL(26)
#define TCR_EL2_ORGN1_WIDTH	UL(2)
#define TCR_EL2_ORGN1_WBWA	INPLACE(TCR_EL2_ORGN1, UL(1))

#define TCR_EL2_SH0_SHIFT	UL(12)
#define TCR_EL2_SH0_WIDTH	UL(2)
#define TCR_EL2_SH0_IS		INPLACE(TCR_EL2_SH0, UL(3))

#define TCR_EL2_SH1_SHIFT	UL(28)
#define TCR_EL2_SH1_WIDTH	UL(2)
#define TCR_EL2_SH1_IS		INPLACE(TCR_EL2_SH1, UL(3))

#define TCR_EL2_TG0_SHIFT	UL(14)
#define TCR_EL2_TG0_WIDTH	UL(2)
#define TCR_EL2_TG0_4K		INPLACE(TCR_EL2_TG0, UL(0))

#define TCR_EL2_TG1_SHIFT	UL(30)
#define TCR_EL2_TG1_WIDTH	UL(2)
#define TCR_EL2_TG1_4K		INPLACE(TCR_EL2_TG1, UL(0))

#define TCR_EL2_IPS_SHIFT	UL(32)
#define TCR_EL2_IPS_WIDTH	UL(3)
#define TCR_PS_BITS_4GB		INPLACE(TCR_EL2_IPS, UL(0))
#define TCR_PS_BITS_64GB	INPLACE(TCR_EL2_IPS, UL(1))
#define TCR_PS_BITS_1TB		INPLACE(TCR_EL2_IPS, UL(2))
#define TCR_PS_BITS_4TB		INPLACE(TCR_EL2_IPS, UL(3))
#define TCR_PS_BITS_16TB	INPLACE(TCR_EL2_IPS, UL(4))
#define TCR_PS_BITS_256TB	INPLACE(TCR_EL2_IPS, UL(5))

#define ADDR_MASK_48_TO_63	ULL(0xFFFF000000000000)
#define ADDR_MASK_44_TO_47	ULL(0x0000F00000000000)
#define ADDR_MASK_42_TO_43	ULL(0x00000C0000000000)
#define ADDR_MASK_40_TO_41	ULL(0x0000030000000000)
#define ADDR_MASK_36_TO_39	ULL(0x000000F000000000)
#define ADDR_MASK_32_TO_35	ULL(0x0000000F00000000)

#define TCR_EL2_AS		(UL(1) << 36)
#define TCR_EL2_HPD0		(UL(1) << 41)
#define TCR_EL2_HPD1		(UL(1) << 42)
#define TCR_EL2_E0PD1		(UL(1) << 56)	/* TODO: ARMv8.5-E0PD, otherwise RES0 */

#define TCR_TxSZ_MIN		UL(16)
#define TCR_TxSZ_MAX		UL(39)
#define TCR_TxSZ_MAX_TTST	UL(48)

/* HCR definitions */
#define HCR_FWB		(UL(1) << 46)
#define HCR_TEA		(UL(1) << 37)
#define HCR_API		(UL(1) << 41)
#define HCR_APK		(UL(1) << 40)
#define HCR_TERR	(UL(1) << 36)
#define HCR_TLOR	(UL(1) << 35)
#define HCR_E2H		(UL(1) << 34)
#define HCR_RW		(UL(1) << 31)
#define HCR_TGE		(UL(1) << 27)
#define HCR_TSW		(UL(1) << 22)
#define HCR_TACR	(UL(1) << 21)
#define HCR_TIDCP	(UL(1) << 20)
#define HCR_TSC		(UL(1) << 19)
#define HCR_TID3	(UL(1) << 18)
#define HCR_TWE		(UL(1) << 14)
#define HCR_TWI		(UL(1) << 13)
#define HCR_VSE		(UL(1) << 8)

#define HCR_BSU_SHIFT	10
#define HCR_BSU_WIDTH	2
#define HCR_BSU_IS	INPLACE(HCR_BSU, 1) /* Barriers are promoted to IS */

#define HCR_FB		(UL(1) << 9)
#define HCR_VI		(UL(1) << 7)
#define HCR_AMO		(UL(1) << 5)
#define HCR_IMO		(UL(1) << 4)
#define HCR_FMO		(UL(1) << 3)
#define HCR_PTW		(UL(1) << 2)
#define HCR_SWIO	(UL(1) << 1)
#define HCR_VM		(UL(1) << 0)

/* TODO verify that all the traps are enabled */
#define HCR_FLAGS (HCR_FWB | HCR_E2H | HCR_RW | HCR_TSC | HCR_AMO | \
	HCR_BSU_IS | HCR_IMO | HCR_FMO | HCR_PTW | HCR_SWIO | HCR_VM | \
	HCR_TID3 | HCR_TEA)

#define HCR_EL2_INIT		(HCR_TGE | HCR_E2H | HCR_TEA)

#define MAIR_ELx_ATTR0_SHIFT	0
#define MAIR_ELx_ATTR0_WIDTH	8
#define MAIR_ELx_ATTR0_MASK	MASK(MAIR_ELx_ATTR0)

/*******************************************************************************
 * Definitions of MAIR encodings for device and normal memory
 ******************************************************************************/
/*
 * MAIR encodings for device memory attributes.
 */
#define MAIR_DEV_NGNRNE		UL(0x0) /* Device nGnRnE */
#define MAIR_DEV_NGNRNE_IDX	0x1

#define MAIR_DEV_NGNRE		UL(0x4)

#define MAIR_NIOWBNTRW		0xff
#define MAIR_NIOWBNTRW_IDX	0x0

/*
 * MAIR encodings for normal memory attributes.
 *
 * Cache Policy
 *  WT:	 Write Through
 *  WB:	 Write Back
 *  NC:	 Non-Cacheable
 *
 * Transient Hint
 *  NTR: Non-Transient
 *  TR:	 Transient
 *
 * Allocation Policy
 *  RA:	 Read Allocate
 *  WA:	 Write Allocate
 *  RWA: Read and Write Allocate
 *  NA:	 No Allocation
 */
#define MAIR_NORM_WT_TR_WA	UL(0x1)
#define MAIR_NORM_WT_TR_RA	UL(0x2)
#define MAIR_NORM_WT_TR_RWA	UL(0x3)
#define MAIR_NORM_NC		UL(0x4)
#define MAIR_NORM_WB_TR_WA	UL(0x5)
#define MAIR_NORM_WB_TR_RA	UL(0x6)
#define MAIR_NORM_WB_TR_RWA	UL(0x7)
#define MAIR_NORM_WT_NTR_NA	UL(0x8)
#define MAIR_NORM_WT_NTR_WA	UL(0x9)
#define MAIR_NORM_WT_NTR_RA	UL(0xa)
#define MAIR_NORM_WT_NTR_RWA	UL(0xb)
#define MAIR_NORM_WB_NTR_NA	UL(0xc)
#define MAIR_NORM_WB_NTR_WA	UL(0xd)
#define MAIR_NORM_WB_NTR_RA	UL(0xe)
#define MAIR_NORM_WB_NTR_RWA	UL(0xf)

#define MAIR_NORM_OUTER_SHIFT	U(4)

#define MAKE_MAIR_NORMAL_MEMORY(inner, outer)	\
		((inner) | ((outer) << MAIR_NORM_OUTER_SHIFT))

#define MAKE_MAIR_NORMAL_MEMORY_IO(_mair) \
		MAKE_MAIR_NORMAL_MEMORY(_mair, _mair)

/*
 * TTBR Definitions
 */
#define TTBR_CNP_BIT		UL(0x1)

#define TTBRx_EL2_CnP_SHIFT	0
#define TTBRx_EL2_CnP_WIDTH	1

#define TTBRx_EL2_BADDR_SHIFT	1
#define TTBRx_EL2_BADDR_WIDTH	47

#define TTBRx_EL2_ASID_SHIFT	48
#define TTBRx_EL2_ASID_WIDTH	16

/*
 * VTTBR Definitions
 */
#define VTTBR_EL2_VMID_SHIFT	48
#define VTTBR_EL2_VMID_WIDTH	16

/*
 * ESR Definitions
 */
#define ESR_EL2_EC_SHIFT	26
#define ESR_EL2_EC_WIDTH	6
#define ESR_EL2_EC_MASK		MASK(ESR_EL2_EC)

#define ESR_EL2_IL_SHIFT	25
#define ESR_EL2_IL_WIDTH	1
#define ESR_EL2_IL_MASK		MASK(ESR_EL2_IL)

#define ESR_EL2_ISS_SHIFT	0
#define ESR_EL2_ISS_WIDTH	25
#define ESR_EL2_ISS_MASK	MASK(ESR_EL2_ISS)

#define ESR_EL2_EC_UNKNOWN	INPLACE(ESR_EL2_EC, 0)
#define ESR_EL2_EC_WFX		INPLACE(ESR_EL2_EC, 1)
#define ESR_EL2_EC_FPU		INPLACE(ESR_EL2_EC, 7)
#define ESR_EL2_EC_SVC		INPLACE(ESR_EL2_EC, 21)
#define ESR_EL2_EC_HVC		INPLACE(ESR_EL2_EC, 22)
#define ESR_EL2_EC_SMC		INPLACE(ESR_EL2_EC, 23)
#define ESR_EL2_EC_SYSREG	INPLACE(ESR_EL2_EC, 24)
#define ESR_EL2_EC_SVE		INPLACE(ESR_EL2_EC, 25)
#define ESR_EL2_EC_INST_ABORT		INPLACE(ESR_EL2_EC, 32)
#define ESR_EL2_EC_INST_ABORT_SEL	INPLACE(ESR_EL2_EC, 33)
#define ESR_EL2_EC_DATA_ABORT		INPLACE(ESR_EL2_EC, 36)
#define ESR_EL2_EC_DATA_ABORT_SEL	INPLACE(ESR_EL2_EC, 37)
#define ESR_EL2_EC_SERROR		INPLACE(ESR_EL2_EC, 47)

/* Data/Instruction Abort ESR fields */
#define ESR_EL2_ABORT_ISV_BIT		(1UL << 24)

#define ESR_EL2_ABORT_SAS_SHIFT		22
#define ESR_EL2_ABORT_SAS_WIDTH		2
#define ESR_EL2_ABORT_SAS_MASK		MASK(ESR_EL2_ABORT_SAS)

#define ESR_EL2_ABORT_SAS_BYTE_VAL	0
#define ESR_EL2_ABORT_SAS_HWORD_VAL	1
#define ESR_EL2_ABORT_SAS_WORD_VAL	2
#define ESR_EL2_ABORT_SAS_DWORD_VAL	3

#define ESR_EL2_ABORT_SSE_BIT		(1UL << 21)

#define ESR_EL2_ABORT_SRT_SHIFT		16
#define ESR_EL2_ABORT_SRT_WIDTH		5
#define ESR_EL2_ABORT_SRT_MASK		MASK(ESR_EL2_ABORT_SRT)

#define ESR_EL2_ABORT_SET_SHIFT		11
#define ESR_EL2_ABORT_SET_WIDTH		2
#define ESR_EL2_ABORT_SET_MASK		MASK(ESR_EL2_ABORT_SET)
#define ESR_EL2_ABORT_SET_UER		INPLACE(ESR_EL2_ABORT_SET, 0)
#define ESR_EL2_ABORT_SET_UC		INPLACE(ESR_EL2_ABORT_SET, 2)
#define ESR_EL2_ABORT_SET_UEO		INPLACE(ESR_EL2_ABORT_SET, 3)

#define ESR_EL2_ABORT_SF_BIT		(1UL << 15)
#define ESR_EL2_ABORT_FNV_BIT		(1UL << 10)
#define ESR_EL2_ABORT_EA_BIT		(1UL << 9)
#define ESR_EL2_ABORT_S1PTW_BIT		(1UL << 7)
#define ESR_EL2_ABORT_WNR_BIT		(1UL << 6)
#define ESR_EL2_ABORT_FSC_SHIFT		0
#define ESR_EL2_ABORT_FSC_WIDTH		6
#define ESR_EL2_ABORT_FSC_MASK		MASK(ESR_EL2_ABORT_FSC)

#define ESR_EL2_ABORT_FSC_TRANSLATION_FAULT	0x04
#define ESR_EL2_ABORT_FSC_PERMISSION_FAULT	0x0c
#define ESR_EL2_ABORT_FSC_TRANSLATION_FAULT_L0	0x04
#define ESR_EL2_ABORT_FSC_SEA			0x10
#define ESR_EL2_ABORT_FSC_SEA_TTW_START		0x13
#define ESR_EL2_ABORT_FSC_SEA_TTW_END		0x17
#define ESR_EL2_ABORT_FSC_GPF			0x28
#define ESR_EL2_ABORT_FSC_LEVEL_SHIFT		0
#define ESR_EL2_ABORT_FSC_LEVEL_WIDTH		2
#define ESR_EL2_ABORT_FSC_LEVEL_MASK		MASK(ESR_EL2_ABORT_FSC_LEVEL)

/* The ESR fields that are reported to the host on Instr./Data Synchronous Abort */
#define ESR_NONEMULATED_ABORT_MASK     ( \
		ESR_EL2_EC_MASK        | \
		ESR_EL2_ABORT_SET_MASK | \
		ESR_EL2_ABORT_FNV_BIT  | \
		ESR_EL2_ABORT_EA_BIT   | \
		ESR_EL2_ABORT_FSC_MASK)

#define ESR_EMULATED_ABORT_MASK            ( \
		ESR_NONEMULATED_ABORT_MASK | \
		ESR_EL2_ABORT_ISV_BIT      | \
		ESR_EL2_ABORT_SAS_MASK     | \
		ESR_EL2_ABORT_SF_BIT       | \
		ESR_EL2_ABORT_WNR_BIT)

#define ESR_EL2_SERROR_DFSC_SHIFT	0
#define ESR_EL2_SERROR_DFSC_WIDTH	6
#define ESR_EL2_SERROR_DFSC_MASK	MASK(ESR_EL2_SERROR_DFSC)
#define ESR_EL2_SERROR_DFSC_UNCAT	INPLACE(ESR_EL2_SERROR_DFSC, 0)
#define ESR_EL2_SERROR_DFSC_ASYNC	INPLACE(ESR_EL2_SERROR_DFSC, 1)

#define ESR_EL2_SERROR_EA_BIT		(1UL << 9)

#define ESR_EL2_SERROR_AET_SHIFT	10
#define ESR_EL2_SERROR_AET_WIDTH	3
#define ESR_EL2_SERROR_AET_MASK		MASK(ESR_EL2_SERROR_AET)
#define ESR_EL2_SERROR_AET_UC		INPLACE(ESR_EL2_SERROR_AET, 0)
#define ESR_EL2_SERROR_AET_UEU		INPLACE(ESR_EL2_SERROR_AET, 1)
#define ESR_EL2_SERROR_AET_UEO		INPLACE(ESR_EL2_SERROR_AET, 2)
#define ESR_EL2_SERROR_AET_UER		INPLACE(ESR_EL2_SERROR_AET, 3)
#define ESR_EL2_SERROR_AET_CE		INPLACE(ESR_EL2_SERROR_AET, 6)

#define ESR_EL2_SERROR_IESB_BIT		(1UL << 13)
#define ESR_EL2_SERROR_IDS_BIT		(1UL << 24)

/* The ESR fields that are reported to the host on SError */
#define ESR_SERROR_MASK			( \
		ESR_EL2_SERROR_IDS_BIT  | \
		ESR_EL2_SERROR_AET_MASK | \
		ESR_EL2_SERROR_EA_BIT   | \
		ESR_EL2_SERROR_DFSC_MASK)

#define ESR_EL2_SYSREG_TRAP_OP0_SHIFT	20
#define ESR_EL2_SYSREG_TRAP_OP0_WIDTH	2
#define ESR_EL2_SYSREG_TRAP_OP0_MASK	MASK(ESR_EL2_SYSREG_TRAP_OP0)

#define ESR_EL2_SYSREG_TRAP_OP2_SHIFT	17
#define ESR_EL2_SYSREG_TRAP_OP2_WIDTH	3
#define ESR_EL2_SYSREG_TRAP_OP2_MASK	MASK(ESR_EL2_SYSREG_TRAP_OP2)

#define ESR_EL2_SYSREG_TRAP_OP1_SHIFT	14
#define ESR_EL2_SYSREG_TRAP_OP1_WIDTH	3
#define ESR_EL2_SYSREG_TRAP_OP1_MASK	MASK(ESR_EL2_SYSREG_TRAP_OP1)

#define ESR_EL2_SYSREG_TRAP_CRN_SHIFT	10
#define ESR_EL2_SYSREG_TRAP_CRN_WIDTH	4
#define ESR_EL2_SYSREG_TRAP_CRN_MASK	MASK(ESR_EL2_SYSREG_TRAP_CRN)

#define ESR_EL2_SYSREG_TRAP_RT_SHIFT	5
#define ESR_EL2_SYSREG_TRAP_RT_WIDTH	5
#define ESR_EL2_SYSREG_TRAP_RT_MASK	MASK(ESR_EL2_SYSREG_TRAP_RT)

#define ESR_EL2_SYSREG_TRAP_CRM_SHIFT	1
#define ESR_EL2_SYSREG_TRAP_CRM_WIDTH	4
#define ESR_EL2_SYSREG_TRAP_CRM_MASK	MASK(ESR_EL2_SYSREG_TRAP_CRM)

/* WFx ESR fields */
#define ESR_EL2_WFx_TI_BIT		(1UL << 0)

/* xVC ESR fields */
#define ESR_EL2_xVC_IMM_SHIFT		0
#define ESR_EL2_xVC_IMM_WIDTH		16
#define ESR_EL2_xVC_IMM_MASK		MASK(ESR_EL2_xVC_IMM)

/* ID_AA64DFR0_EL1 definitions */
#define ID_AA64DFR0_EL1_HPMN0_SHIFT		UL(60)
#define ID_AA64DFR0_EL1_HPMN0_WIDTH		UL(4)
#define ID_AA64DFR0_EL1_HPMN0_MASK		MASK(ID_AA64DFR0_EL1_HPMN0)

#define ID_AA64DFR0_EL1_BRBE_SHIFT		UL(52)
#define ID_AA64DFR0_EL1_BRBE_WIDTH		UL(4)
#define ID_AA64DFR0_EL1_BRBE_MASK		MASK(ID_AA64DFR0_EL1_BRBE)

#define ID_AA64DFR0_EL1_MTPMU_SHIFT		UL(48)
#define ID_AA64DFR0_EL1_MTPMU_WIDTH		UL(4)
#define ID_AA64DFR0_EL1_MTPMU_MASK		MASK(ID_AA64DFR0_EL1_MTPMU)

#define ID_AA64DFR0_EL1_TraceBuffer_SHIFT	UL(44)
#define ID_AA64DFR0_EL1_TraceBuffer_WIDTH	UL(4)
#define ID_AA64DFR0_EL1_TraceBuffer_MASK	MASK(ID_AA64DFR0_EL1_TraceBuffer)

#define ID_AA64DFR0_EL1_TraceFilt_SHIFT		UL(40)
#define ID_AA64DFR0_EL1_TraceFilt_WIDTH		UL(4)
#define ID_AA64DFR0_EL1_TraceFilt_MASK		MASK(ID_AA64DFR0_EL1_TraceFilt)

#define ID_AA64DFR0_EL1_DoubleLock_SHIFT	UL(36)
#define ID_AA64DFR0_EL1_DoubleLock_WIDTH	UL(4)
#define ID_AA64DFR0_EL1_DoubleLock_MASK		MASK(ID_AA64DFR0_EL1_DoubleLock)

#define ID_AA64DFR0_EL1_PMSVer_SHIFT		UL(32)
#define ID_AA64DFR0_EL1_PMSVer_WIDTH		UL(4)
#define ID_AA64DFR0_EL1_PMSVer_MASK		MASK(ID_AA64DFR0_EL1_PMSVer)

#define ID_AA64DFR0_EL1_CTX_CMPS_SHIFT		UL(28)
#define ID_AA64DFR0_EL1_CTX_CMPS_WIDTH		UL(4)
#define ID_AA64DFR0_EL1_CTX_CMPS_MASK		MASK(ID_AA64DFR0_EL1_CTX_CMPS)

#define ID_AA64DFR0_EL1_WRPs_SHIFT		UL(20)
#define ID_AA64DFR0_EL1_WRPs_WIDTH		UL(4)
#define ID_AA64DFR0_EL1_WRPs_MASK		MASK(ID_AA64DFR0_EL1_WRPs)

#define ID_AA64DFR0_EL1_BRPs_SHIFT		UL(12)
#define ID_AA64DFR0_EL1_BRPs_WIDTH		UL(4)
#define ID_AA64DFR0_EL1_BRPs_MASK		MASK(ID_AA64DFR0_EL1_BRPs)

#define ID_AA64DFR0_EL1_PMUVer_SHIFT		UL(8)
#define ID_AA64DFR0_EL1_PMUVer_WIDTH		UL(4)
#define ID_AA64DFR0_EL1_PMUVer_MASK		MASK(ID_AA64DFR0_EL1_PMUVer)

#define ID_AA64DFR0_EL1_TraceVer_SHIFT		UL(4)
#define ID_AA64DFR0_EL1_TraceVer_WIDTH		UL(4)
#define ID_AA64DFR0_EL1_TraceVer_MASK		MASK(ID_AA64DFR0_EL1_TraceVer)

#define ID_AA64DFR0_EL1_DebugVer_SHIFT		UL(0)
#define ID_AA64DFR0_EL1_DebugVer_WIDTH		UL(4)
#define ID_AA64DFR0_EL1_DebugVer_MASK		MASK(ID_AA64DFR0_EL1_DebugVer)

/* Debug architecture version */
#define ID_AA64DFR0_EL1_DebugVer_8	UL(6)
#define ID_AA64DFR0_EL1_DebugVer_8_VHE	UL(7)
#define ID_AA64DFR0_EL1_DebugVer_8_2	UL(8)
#define ID_AA64DFR0_EL1_DebugVer_8_4	UL(9)
#define ID_AA64DFR0_EL1_DebugVer_8_8	UL(10)

/* ID_AA64PFR0_EL1 definitions */
#define ID_AA64PFR0_EL1_SVE_SHIFT	UL(32)
#define ID_AA64PFR0_EL1_SVE_WIDTH	UL(4)
#define ID_AA64PFR0_EL1_SVE_MASK	UL(0xf)

#define ID_AA64PFR0_EL1_AMU_SHIFT	UL(44)
#define ID_AA64PFR0_EL1_AMU_WIDTH	4

/* ID_AA64MMFR0_EL1 definitions */
#define ID_AA64MMFR0_EL1_PARANGE_SHIFT	U(0)
#define ID_AA64MMFR0_EL1_PARANGE_MASK	ULL(0xf)

#define PARANGE_0000_WIDTH	U(32)
#define PARANGE_0001_WIDTH	U(36)
#define PARANGE_0010_WIDTH	U(40)
#define PARANGE_0011_WIDTH	U(42)
#define PARANGE_0100_WIDTH	U(44)
#define PARANGE_0101_WIDTH	U(48)
#define PARANGE_0110_WIDTH	U(52)

#define ID_AA64MMFR0_EL1_ECV_SHIFT		U(60)
#define ID_AA64MMFR0_EL1_ECV_MASK		ULL(0xf)
#define ID_AA64MMFR0_EL1_ECV_NOT_SUPPORTED	ULL(0x0)
#define ID_AA64MMFR0_EL1_ECV_SUPPORTED		ULL(0x1)
#define ID_AA64MMFR0_EL1_ECV_SELF_SYNCH	ULL(0x2)

#define ID_AA64MMFR0_EL1_FGT_SHIFT		U(56)
#define ID_AA64MMFR0_EL1_FGT_MASK		ULL(0xf)
#define ID_AA64MMFR0_EL1_FGT_SUPPORTED		ULL(0x1)
#define ID_AA64MMFR0_EL1_FGT_NOT_SUPPORTED	ULL(0x0)

#define ID_AA64MMFR0_EL1_TGRAN4_2_SHIFT		U(40)
#define ID_AA64MMFR0_EL1_TGRAN4_2_MASK		ULL(0xf)
#define ID_AA64MMFR0_EL1_TGRAN4_2_TGRAN4	ULL(0x0)
#define ID_AA64MMFR0_EL1_TGRAN4_2_NOT_SUPPORTED	ULL(0x1)
#define ID_AA64MMFR0_EL1_TGRAN4_2_SUPPORTED	ULL(0x2)
#define ID_AA64MMFR0_EL1_TGRAN4_2_LPA2		ULL(0x3)

#define ID_AA64MMFR0_EL1_TGRAN16_2_SHIFT		U(32)
#define ID_AA64MMFR0_EL1_TGRAN16_2_MASK			ULL(0xf)
#define ID_AA64MMFR0_EL1_TGRAN16_2_TGRAN16		ULL(0x0)
#define ID_AA64MMFR0_EL1_TGRAN16_2_NOT_SUPPORTED	ULL(0x1)
#define ID_AA64MMFR0_EL1_TGRAN16_2_SUPPORTED		ULL(0x2)
#define ID_AA64MMFR0_EL1_TGRAN16_2_LPA2			ULL(0x3)

#define ID_AA64MMFR0_EL1_TGRAN4_SHIFT		U(28)
#define ID_AA64MMFR0_EL1_TGRAN4_MASK		ULL(0xf)
#define ID_AA64MMFR0_EL1_TGRAN4_SUPPORTED	ULL(0x0)
#define ID_AA64MMFR0_EL1_TGRAN4_LPA2		ULL(0x1)
#define ID_AA64MMFR0_EL1_TGRAN4_NOT_SUPPORTED	ULL(0xf)

#define ID_AA64MMFR0_EL1_TGRAN64_SHIFT		UL(24)
#define ID_AA64MMFR0_EL1_TGRAN64_MASK		UL(0xf)
#define ID_AA64MMFR0_EL1_TGRAN64_SUPPORTED	UL(0x0)
#define ID_AA64MMFR0_EL1_TGRAN64_NOT_SUPPORTED	UL(0xf)

#define ID_AA64MMFR0_EL1_TGRAN16_SHIFT		UL(20)
#define ID_AA64MMFR0_EL1_TGRAN16_MASK		UL(0xf)
#define ID_AA64MMFR0_EL1_TGRAN16_NOT_SUPPORTED	UL(0x0)
#define ID_AA64MMFR0_EL1_TGRAN16_SUPPORTED	UL(0x1)
#define ID_AA64MMFR0_EL1_TGRAN16_LPA2		UL(0x2)

/* RNDR definitions */
#define ID_AA64ISAR0_EL1_RNDR_SHIFT		UL(60)
#define ID_AA64ISAR0_EL1_RNDR_WIDTH		UL(4)
#define ID_AA64ISAR0_EL1_RNDR_MASK		UL(0xF)

/* ID_AA64MMFR1_EL1 definitions */
#define ID_AA64MMFR1_EL1_VMIDBits_SHIFT		UL(4)
#define ID_AA64MMFR1_EL1_VMIDBits_MASK		UL(0xf)
#define ID_AA64MMFR1_EL1_VMIDBits_8		UL(0)
#define ID_AA64MMFR1_EL1_VMIDBits_16		UL(2)

/* HPFAR_EL2 definitions */
#define HPFAR_EL2_FIPA_SHIFT		4
#define HPFAR_EL2_FIPA_WIDTH		40
#define HPFAR_EL2_FIPA_MASK		MASK(HPFAR_EL2_FIPA)
#define HPFAR_EL2_FIPA_OFFSET		8

/* SPSR definitions */
#define SPSR_EL2_MODE_SHIFT		0
#define SPSR_EL2_MODE_WIDTH		4
#define SPSR_EL2_MODE_EL0t		INPLACE(SPSR_EL2_MODE, 0)

#define SPSR_EL2_MODE_SHIFT		0
#define SPSR_EL2_MODE_WIDTH		4
#define SPSR_EL2_MODE_EL1h		INPLACE(SPSR_EL2_MODE, 5)
#define SPSR_EL2_MODE_EL1t		INPLACE(SPSR_EL2_MODE, 4)

/* FIXME: DAIF definitions are redundant here. Might need unification. */
#define SPSR_EL2_nRW_SHIFT		4
#define SPSR_EL2_nRW_WIDTH		1
#define SPSR_EL2_nRW_AARCH64		INPLACE(SPSR_EL2_nRW, 0)
#define SPSR_EL2_nRW_AARCH32		INPLACE(SPSR_EL2_nRW, 1)

#define SPSR_EL2_DAIF_SHIFT		U(6)
#define SPSR_EL2_DAIF_MASK		U(0xf)

#define SPSR_EL2_AIF_SHIFT		U(6)
#define SPSR_EL2_AIF_MASK		U(0x7)

#define SPSR_EL2_F_SHIFT		6
#define SPSR_EL2_F_WIDTH		1
#define SPSR_EL2_F_BIT			INPLACE(SPSR_EL2_F, 1)
#define DAIF_FIQ_BIT			(U(1) << 0)

#define SPSR_EL2_I_SHIFT		7
#define SPSR_EL2_I_WIDTH		1
#define SPSR_EL2_I_BIT			INPLACE(SPSR_EL2_I, 1)
#define DAIF_IRQ_BIT			(U(1) << 1)

#define SPSR_EL2_A_SHIFT		8
#define SPSR_EL2_A_WIDTH		1
#define SPSR_EL2_A_BIT			INPLACE(SPSR_EL2_A, 1)
#define DAIF_ABT_BIT			(U(1) << 2)

#define SPSR_EL2_D_SHIFT		9
#define SPSR_EL2_D_WIDTH		1
#define SPSR_EL2_D_BIT			INPLACE(SPSR_EL2_D, 1)
#define DAIF_DBG_BIT			(U(1) << 3)

#define SPSR_EL2_SSBS_SHIFT		12
#define SPSR_EL2_SSBS_WIDTH		1
#define SPSR_EL2_SSBS_BIT		INPLACE(SPSR_EL2_SSBS, 1)

#define SPSR_EL2_IL_SHIFT		20
#define SPSR_EL2_IL_WIDTH		1
#define SPSR_EL2_IL_BIT			INPLACE(SPSR_EL2_IL, 1)

#define SPSR_EL2_SS_SHIFT		21
#define SPSR_EL2_SS_WIDTH		1
#define SPSR_EL2_SS_BIT			INPLACE(SPSR_EL2_SS, 1)

#define SPSR_EL2_PAN_SHIFT		22
#define SPSR_EL2_PAN_WIDTH		1
#define SPSR_EL2_PAN_BIT		INPLACE(SPSR_EL2_PAN, 1)

#define SPSR_EL2_UAO_SHIFT		23
#define SPSR_EL2_UAO_WIDTH		1
#define SPSR_EL2_UAO_BIT		INPLACE(SPSR_EL2_UAO, 1)

#define SPSR_EL2_V_SHIFT		28
#define SPSR_EL2_V_WIDTH		1
#define SPSR_EL2_V_BIT			INPLACE(SPSR_EL2_V, 1)

#define SPSR_EL2_C_SHIFT		29
#define SPSR_EL2_C_WIDTH		1
#define SPSR_EL2_C_BIT			INPLACE(SPSR_EL2_C, 1)

#define SPSR_EL2_Z_SHIFT		30
#define SPSR_EL2_Z_WIDTH		1
#define SPSR_EL2_Z_BIT			INPLACE(SPSR_EL2_Z, 1)

#define SPSR_EL2_N_SHIFT		31
#define SPSR_EL2_N_WIDTH		1
#define SPSR_EL2_N_BIT			INPLACE(SPSR_EL2_N, 1)

/* VTCR definitions */
#define VTCR_T0SZ_SHIFT		0
#define VTCR_T0SZ_WIDTH		6

#define VTCR_SL0_SHIFT		6
#define VTCR_SL0_WIDTH		2

#define VTCR_SL0_4K_L2		INPLACE(VTCR_SL0, 0)
#define VTCR_SL0_4K_L1		INPLACE(VTCR_SL0, 1)
#define VTCR_SL0_4K_L0		INPLACE(VTCR_SL0, 2)
#define VTCR_SL0_4K_L3		INPLACE(VTCR_SL0, 3)

#define VTCR_IRGN0_SHIFT	8
#define VTCR_IRGN0_WIDTH	2
#define VTCR_IRGN0_WBRAWA	INPLACE(VTCR_IRGN0, 1)

#define VTCR_ORGN0_SHIFT	10
#define VTCR_ORGN0_WIDTH	2
#define VTCR_ORGN0_WBRAWA	INPLACE(VTCR_ORGN0, 1)

#define VTCR_SH0_SHIFT		12
#define VTCR_SH0_WIDTH		2
#define VTCR_SH0_IS		INPLACE(VTCR_SH0, 3)

#define VTCR_TG0_SHIFT		14
#define VTCR_TG0_WIDTH		2
#define VTCR_TG0_4K		INPLACE(VTCR_TG0, 0)

#define VTCR_PS_SHIFT		16
#define VTCR_PS_WIDTH		3
#define VTCR_PS_40		INPLACE(VTCR_PS, 2)

#define VTCR_VS			(UL(1) << 19)
#define VTCR_NSA		(UL(1) << 30)
#define VTCR_RES1		(UL(1) << 31)

#define VTCR_FLAGS ( \
	VTCR_IRGN0_WBRAWA | /* PTW inner cache attr. is WB RAWA*/ \
	VTCR_ORGN0_WBRAWA | /* PTW outer cache attr. is WB RAWA*/ \
	VTCR_SH0_IS       | /* PTW shareability attr. is Outer Sharable*/\
	VTCR_TG0_4K       | /* 4K granule size in non-secure PT*/ \
	VTCR_PS_40        | /* size(PA) = 40 */   \
	/* VS = 0              size(VMID) = 8 */ \
	/* NSW = 0             non-secure s2 is made of secure pages*/ \
	VTCR_NSA           | /* non-secure IPA maps to non-secure PA */ \
	VTCR_RES1 \
	)


/* SCTLR definitions */
#define SCTLR_EL1_EE		(UL(1) << 25)
#define SCTLR_EL1_SPAN		(UL(1) << 23)
#define SCTLR_EL1_EIS		(UL(1) << 22)
#define SCTLR_EL1_nTWE		(UL(1) << 18)
#define SCTLR_EL1_nTWI		(UL(1) << 16)
#define SCTLR_EL1_EOS		(UL(1) << 11)
#define SCTLR_EL1_nAA		(UL(1) << 6)
#define SCTLR_EL1_CP15BEN	(UL(1) << 5)
#define SCTLR_EL1_SA0		(UL(1) << 4)
#define SCTLR_EL1_SA		(UL(1) << 3)

#define SCTLR_EL1_FLAGS (SCTLR_EL1_SPAN | SCTLR_EL1_EIS | SCTLR_EL1_nTWE | \
	SCTLR_EL1_nTWI | SCTLR_EL1_EOS | SCTLR_EL1_nAA | SCTLR_EL1_CP15BEN | \
	SCTLR_EL1_SA0 | SCTLR_EL1_SA)

/* PMCR_EL0 Definitions */
#define PMCR_EL0_LC_SHIFT		6
#define PMCR_EL0_LC_WIDTH		1
#define PMCR_EL0_LC_BIT			INPLACE(PMCR_EL0_LC, 1)

#define PMCR_EL0_RES1			PMCR_EL0_LC_BIT


/* MDSCR_EL1 Definitions */
#define MDSCR_EL1_TDCC_SHIFT		12
#define MDSCR_EL1_TDCC_WIDTH		1
#define MDSCR_EL1_TDCC_BIT		INPLACE(MDSCR_EL1_TDCC, 1)

/* SCTLR register definitions */
#define SCTLR_EL2_RES1		((UL(1) << 22) /* TODO: ARMv8.5-CSEH, otherwise RES1 */ | \
				 (1U << 11) /* TODO: ARMv8.5-CSEH, otherwise RES1 */)

#define SCTLR_EL2_M		(UL(1) << 0)
#define SCTLR_EL2_C		(UL(1) << 2)
#define SCTLR_EL2_SA		(UL(1) << 3)
#define SCTLR_EL2_SA0		(UL(1) << 4)
#define SCTLR_EL2_SED		(UL(1) << 8)
/* TODO: ARMv8.5-CSEH, otherwise RES1 */
/* #define SCTLR_EL2_EOS	(UL(1) << 11) */
#define SCTLR_EL2_I		(UL(1) << 12)
#define SCTLR_EL2_DZE		(UL(1) << 14)
#define SCTLR_EL2_UCT		(UL(1) << 15)
#define SCTLR_EL2_NTWI		(UL(1) << 16)
#define SCTLR_EL2_NTWE		(UL(1) << 18)
#define SCTLR_EL2_WXN		(UL(1) << 19)
#define SCTLR_EL2_TSCXT		(UL(1) << 20)
/* TODO: ARMv8.5-CSEH, otherwise RES1 */
/* #define SCTLR_EL2_EIS	(UL(1) << 22) */
#define SCTLR_EL2_SPAN		(UL(1) << 23)
#define SCTLR_EL2_UCI		(UL(1) << 26)
#define SCTLR_EL2_NTLSMD	(UL(1) << 28)
#define SCTLR_EL2_LSMAOE	(UL(1) << 29)
/* HCR_EL2.E2H == 0b1 and HCR_EL2.TGE == 0b1 */
#define SECURE_SCTLR_EL2_RES1	((UL(1) << 22) /* TODO: ARMv8.5-CSEH, otherwise RES1 */ | \
				 (UL(1) << 11) /* TODO: ARMv8.5-CSEH, otherwise RES1 */)

#define SCTLR_EL2_INIT		(/* SCTLR_EL2_M = 0 (MMU disabled) */  \
				/* SCTLR_EL2_A = 0 (No alignment checks) */  \
				 SCTLR_EL2_C   /* Data accesses are cacheable
						* as per translation tables */ | \
				 SCTLR_EL2_SA  /* SP aligned at EL2 */ | \
				 SCTLR_EL2_SA0  /* SP Alignment check enable for EL0 */ \
				/* SCTLR_EL2_CP15BEN = 0 (EL0 using AArch32:
				 * EL0 execution of the CP15DMB, CP15DSB, and
				 * CP15ISB instructions is UNDEFINED. */ \
				/* SCTLR_EL2_NAA = 0 (unaligned MA fault at EL2 and EL0) */ \
				/* SCTLR_EL2_ITD = 0 (A32 Only) */ | \
				 SCTLR_EL2_SED /* A32 Only, RES1 for non-A32 systems */ \
				/* SCTLR_EL2_EOS TODO: ARMv8.5-CSEH, otherwise RES1 */ | \
				 SCTLR_EL2_I	 /* I$ is ON for EL2 and EL0 */ | \
				 SCTLR_EL2_DZE   /* Do not trap DC ZVA */ | \
				 SCTLR_EL2_UCT   /* Allow EL0 access to CTR_EL0 */ | \
				 SCTLR_EL2_NTWI  /* Don't trap WFI from EL0 to EL2 */ | \
				 SCTLR_EL2_NTWE  /* Don't trap WFE from EL0 to EL2 */ | \
				 SCTLR_EL2_WXN   /* W implies XN */ | \
				 SCTLR_EL2_TSCXT /* Trap EL0 accesss to SCXTNUM_EL0 */ \
				/* SCTLR_EL2_EIS EL2 exception is context
				 * synchronizing
				 * TODO: ARMv8.5-CSEH, otherwise RES1 */ \
				 /* SCTLR_EL2_SPAN = 0 (Set PSTATE.PAN = 1 on
				 * exceptions to EL2)) */ | \
				 SCTLR_EL2_UCI /* Allow cache maintenance
						* instructions at EL0 */ | \
				 SCTLR_EL2_NTLSMD /* A32/T32 only */ | \
				 SCTLR_EL2_LSMAOE /* A32/T32 only */ | \
				 SECURE_SCTLR_EL2_RES1)

#define SCTLR_EL2_RUNTIME	(SCTLR_EL2_INIT| \
				 SCTLR_EL2_M   /* MMU enabled */)

/* CPTR_EL2 definitions */
#define CPTR_EL2_RES1			((UL(1) << 13) | (UL(1) << 12) | (UL(1) << 9) | 0xff)
#define CPTR_EL2_FPEN			(UL(1) << 20)
#define CPTR_EL2_TTA			(UL(1) << 28)
#define CPTR_EL2_TAM			(UL(1) << 30)
#define CPTR_EL2_FPEN_SHIFT		20
#define CPTR_EL2_FPEN_MASK		0x3
#define	CPTR_EL2_FPEN_TRAP_ALL_00	0x0
#define	CPTR_EL2_FPEN_TRAP_TGE_01	0x1
#define CPTR_EL2_FPEN_TRAP_ALL_10	0x2
#define	CPTR_EL2_FPEN_NO_TRAP_11	0x3
#define CPTR_EL2_ZEN_SHIFT		UL(16)
#define CPTR_EL2_ZEN_MASK		UL(0x3)
#define CPTR_EL2_ZEN_TRAP_ALL_00	UL(0x0)
#define CPTR_EL2_ZEN_NO_TRAP_11		UL(0x3)
				/* Trap all FPU/SVE accesses */
#define CPTR_EL2_INIT		((CPTR_EL2_ZEN_TRAP_ALL_00 << \
				  CPTR_EL2_ZEN_SHIFT) | \
				 (CPTR_EL2_FPEN_TRAP_ALL_00 << CPTR_EL2_FPEN_SHIFT) | \
				 CPTR_EL2_TTA  /* trap trace access */ | \
				 CPTR_EL2_TAM  /* trap AMU access */ | \
				 CPTR_EL2_RES1)

/* MDCR_EL2 definitions */
#define MDCR_EL2_HLP		(U(1) << 26)
#define MDCR_EL2_HCCD		(U(1) << 23)
#define MDCR_EL2_TTRF		(U(1) << 19)
#define MDCR_EL2_HPMD		(U(1) << 17)
#define MDCR_EL2_TPMS		(U(1) << 14)
#define MDCR_EL2_E2PB(x)	((x) << 12)
#define MDCR_EL2_E2PB_EL1	U(0x3)
#define MDCR_EL2_TDRA_BIT	(U(1) << 11)
#define MDCR_EL2_TDOSA_BIT	(U(1) << 10)
#define MDCR_EL2_TDA_BIT	(U(1) << 9)
#define MDCR_EL2_TDE_BIT	(U(1) << 8)
#define MDCR_EL2_HPME_BIT	(U(1) << 7)
#define MDCR_EL2_TPM_BIT	(U(1) << 6)
#define MDCR_EL2_TPMCR_BIT	(U(1) << 5)
#define MDCR_EL2_INIT		(MDCR_EL2_TPMCR_BIT \
				| MDCR_EL2_TPM_BIT \
				| MDCR_EL2_TDA_BIT)

/* MPIDR definitions */
#define MPIDR_EL1_AFF_MASK	0xFF
#define MPIDR_EL1_AFF0_SHIFT	0
#define MPIDR_EL1_AFF1_SHIFT	8
#define MPIDR_EL1_AFF2_SHIFT	16
#define MPIDR_EL1_AFF3_SHIFT	32
#define MPIDR_EL1_MT_MASK	(UL(1) << 24)
#define MPIDR_EL1_AFFINITY_BITS	8

#define MPIDR_EL1_AFF0		INPLACE(MPIDR_EL1_AFF0, MPIDR_EL1_AFF_MASK)
#define MPIDR_EL1_AFF1		INPLACE(MPIDR_EL1_AFF1, MPIDR_EL1_AFF_MASK)
#define MPIDR_EL1_AFF2		INPLACE(MPIDR_EL1_AFF2, MPIDR_EL1_AFF_MASK)
#define MPIDR_EL1_AFF3		INPLACE(MPIDR_EL1_AFF3, MPIDR_EL1_AFF_MASK)

/*
 * RmiRecMpidr type definitions.
 *
 * 'MPIDR_EL2_AFF<n>_VAL_SHIFT' constants specify the right shift
 * for affinity field <n> that gives the field's actual value.
 *
 * Aff0[3:0] - Affinity level 0
 * For compatibility with GICv3 only Aff0[3:0] field is used,
 * and Aff0[7:4] of a REC MPIDR value is RES0.
 */
#define MPIDR_EL2_AFF0_SHIFT			0
#define MPIDR_EL2_AFF0_WIDTH			4
#define MPIDR_EL2_AFF0_VAL_SHIFT		0

/* Aff1[15:8] - Affinity level 1 */
#define MPIDR_EL2_AFF1_SHIFT			8
#define MPIDR_EL2_AFF1_WIDTH			8
#define MPIDR_EL2_AFF1_VAL_SHIFT		4

/* Aff2[23:16] - Affinity level 2 */
#define MPIDR_EL2_AFF2_SHIFT			16
#define MPIDR_EL2_AFF2_WIDTH			8
#define MPIDR_EL2_AFF2_VAL_SHIFT		4

/* Aff3[39:32] - Affinity level 3 */
#define MPIDR_EL2_AFF3_SHIFT			32
#define MPIDR_EL2_AFF3_WIDTH			8
#define MPIDR_EL2_AFF3_VAL_SHIFT		12

/*
 * Extract the value of Aff<n> register field shifted right
 * so it can be evaluated directly.
 */
#define	MPIDR_EL2_AFF(n, reg)	\
	(((reg) & MASK(MPIDR_EL2_AFF##n)) >> MPIDR_EL2_AFF##n##_VAL_SHIFT)

/* VMPIDR_EL2 bit [31] = RES1 */
#define VMPIDR_EL2_RES1				(UL(1) << 31)

/* ICC_SRE_EL2 defintions */
#define ICC_SRE_EL2_ENABLE	(UL(1) << 3)	/* Enable lower EL access to ICC_SRE_EL1 */
#define ICC_SRE_EL2_DIB		(UL(1) << 2)	/* Disable IRQ bypass   */
#define ICC_SRE_EL2_DFB		(UL(1) << 1)	/* Disable FIQ bypass   */
#define ICC_SRE_EL2_SRE		(UL(1) << 0)	/* Enable sysreg access */

#define	ICC_SRE_EL2_INIT	(ICC_SRE_EL2_ENABLE | ICC_SRE_EL2_DIB | \
				 ICC_SRE_EL2_DFB | ICC_SRE_EL2_SRE)

/* MPAM definitions */
#define MPAM2_EL2_INIT		0x0
#define MPAMHCR_EL2_INIT	0x0

#define PMSCR_EL2_INIT		0x0

#define SYSREG_ESR(op0, op1, crn, crm, op2) \
		(((op0) << ESR_EL2_SYSREG_TRAP_OP0_SHIFT) | \
		 ((op1) << ESR_EL2_SYSREG_TRAP_OP1_SHIFT) | \
		 ((crn) << ESR_EL2_SYSREG_TRAP_CRN_SHIFT) | \
		 ((crm) << ESR_EL2_SYSREG_TRAP_CRM_SHIFT) | \
		 ((op2) << ESR_EL2_SYSREG_TRAP_OP2_SHIFT))

#define ESR_EL2_SYSREG_MASK		SYSREG_ESR(3, 7, 15, 15, 7)

#define ESR_EL2_SYSREG_ID_MASK		SYSREG_ESR(3, 7, 15, 0, 0)
#define ESR_EL2_SYSREG_ID		SYSREG_ESR(3, 0, 0, 0, 0)

#define ESR_EL2_SYSREG_ID_AA64PFR0_EL1	SYSREG_ESR(3, 0, 0, 4, 0)
#define ESR_EL2_SYSREG_ID_AA64PFR1_EL1	SYSREG_ESR(3, 0, 0, 4, 1)
#define ESR_EL2_SYSREG_ID_AA64ZFR0_EL1	SYSREG_ESR(3, 0, 0, 4, 4)

#define ESR_EL2_SYSREG_ID_AA64DFR0_EL1	SYSREG_ESR(3, 0, 0, 5, 0)
#define ESR_EL2_SYSREG_ID_AA64DFR1_EL1	SYSREG_ESR(3, 0, 0, 5, 1)

#define ESR_EL2_SYSREG_ID_AA64AFR0_EL1	SYSREG_ESR(3, 0, 0, 5, 4)
#define ESR_EL2_SYSREG_ID_AA64AFR1_EL1	SYSREG_ESR(3, 0, 0, 5, 5)

#define ESR_EL2_SYSREG_ID_AA64ISAR0_EL1	SYSREG_ESR(3, 0, 0, 6, 0)
#define ESR_EL2_SYSREG_ID_AA64ISAR1_EL1	SYSREG_ESR(3, 0, 0, 6, 1)

#define ESR_EL2_SYSREG_ID_AA64MMFR0_EL1	SYSREG_ESR(3, 0, 0, 7, 0)
#define ESR_EL2_SYSREG_ID_AA64MMFR1_EL1	SYSREG_ESR(3, 0, 0, 7, 1)
#define ESR_EL2_SYSREG_ID_AA64MMFR2_EL1	SYSREG_ESR(3, 0, 0, 7, 2)

/* ID_AA64ISAR1_EL1 definitions */
#define ID_AA64ISAR1_EL1_GPI_SHIFT	UL(28)
#define ID_AA64ISAR1_EL1_GPI_WIDTH	UL(4)
#define ID_AA64ISAR1_EL1_GPI_MASK	MASK(ID_AA64ISAR1_EL1_GPI)

#define ID_AA64ISAR1_EL1_GPA_SHIFT	UL(24)
#define ID_AA64ISAR1_EL1_GPA_WIDTH	UL(4)
#define ID_AA64ISAR1_EL1_GPA_MASK	MASK(ID_AA64ISAR1_EL1_GPA)

#define ID_AA64ISAR1_EL1_API_SHIFT	UL(8)
#define ID_AA64ISAR1_EL1_API_WIDTH	UL(4)
#define ID_AA64ISAR1_EL1_API_MASK	MASK(ID_AA64ISAR1_EL1_API)

#define ID_AA64ISAR1_EL1_APA_SHIFT	UL(4)
#define ID_AA64ISAR1_EL1_APA_WIDTH	UL(4)
#define ID_AA64ISAR1_EL1_APA_MASK	MASK(ID_AA64ISAR1_EL1_APA)

#define ESR_EL2_SYSREG_TIMERS_MASK		SYSREG_ESR(3, 3, 15, 12, 0)
#define ESR_EL2_SYSREG_TIMERS			SYSREG_ESR(3, 3, 14, 0, 0)

#define ESR_EL2_SYSREG_TIMER_CNTP_TVAL_EL0	SYSREG_ESR(3, 3, 14, 2, 0)
#define ESR_EL2_SYSREG_TIMER_CNTP_CTL_EL0	SYSREG_ESR(3, 3, 14, 2, 1)
#define ESR_EL2_SYSREG_TIMER_CNTP_CVAL_EL0	SYSREG_ESR(3, 3, 14, 2, 2)
#define ESR_EL2_SYSREG_TIMER_CNTV_TVAL_EL0	SYSREG_ESR(3, 3, 14, 3, 0)
#define ESR_EL2_SYSREG_TIMER_CNTV_CTL_EL0	SYSREG_ESR(3, 3, 14, 3, 1)
#define ESR_EL2_SYSREG_TIMER_CNTV_CVAL_EL0	SYSREG_ESR(3, 3, 14, 3, 2)

#define ESR_EL2_SYSREG_ICC_PMR_EL1		SYSREG_ESR(3, 0, 4, 6, 0)

/*
 * GIC system registers encoding mask for registers from
 * ICC_IAR0_EL1(3, 0, 12, 8, 0) to ICC_IGRPEN1_EL1(3, 0, 12, 12, 7).
 */
#define ESR_EL2_SYSREG_ICC_EL1_MASK		SYSREG_ESR(3, 3, 15, 8, 0)
#define ESR_EL2_SYSREG_ICC_EL1			SYSREG_ESR(3, 0, 12, 8, 0)

#define ESR_EL2_SYSREG_ICC_DIR			SYSREG_ESR(3, 0, 12, 11, 1)
#define ESR_EL2_SYSREG_ICC_SGI1R_EL1		SYSREG_ESR(3, 0, 12, 11, 5)
#define ESR_EL2_SYSREG_ICC_SGI0R_EL1		SYSREG_ESR(3, 0, 12, 11, 7)

#define ESR_EL2_SYSREG_DIRECTION	(UL(1) << 0)
#define ESR_EL2_SYSREG_IS_WRITE(esr)	(!((esr) & ESR_EL2_SYSREG_DIRECTION))

#define ESR_IL(esr)	((esr) & ESR_EL2_IL_MASK)

#define ESR_EL2_SYSREG_ISS_RT(esr)	EXTRACT(ESR_EL2_SYSREG_TRAP_RT, esr)

#define ICC_HPPIR1_EL1_INTID_SHIFT	0
#define ICC_HPPIR1_EL1_INTID_WIDTH	24
#define ICC_HPPIR1_EL1_INTID_MASK	MASK(ICC_HPPIR1_EL1_INTID)

#define CNTHCTL_EL2_EL0PCTEN	(UL(1) << UL(0))
#define CNTHCTL_EL2_EL0VCTEN	(UL(1) << UL(1))
#define CNTHCTL_EL2_EL1PCTEN	(UL(1) << 10)
#define CNTHCTL_EL2_EL1PTEN	(UL(1) << 11)
#define CNTHCTL_EL2_EL1TVT	(UL(1) << 13)
#define CNTHCTL_EL2_EL1TVCT	(UL(1) << 14)
#define CNTHCTL_EL2_CNTVMASK	(UL(1) << 18)
#define CNTHCTL_EL2_CNTPMASK	(UL(1) << 19)

#define CNTHCTL_EL2_INIT	(CNTHCTL_EL2_EL0VCTEN | CNTHCTL_EL2_EL0PCTEN)

#define CNTHCTL_EL2_NO_TRAPS	(CNTHCTL_EL2_EL1PCTEN | \
				 CNTHCTL_EL2_EL1PTEN)

#define CNTx_CTL_ENABLE		(UL(1) << 0)
#define CNTx_CTL_IMASK		(UL(1) << 1)
#define CNTx_CTL_ISTATUS	(UL(1) << 2)

/*******************************************************************************
 * Definitions of register offsets, fields and macros for CPU system
 * instructions.
 ******************************************************************************/

#define TLBI_ADDR_SHIFT		U(12)
#define TLBI_ADDR_MASK		U(0x0FFFFFFFFFFF)
#define TLBI_ADDR(x)		(((x) >> TLBI_ADDR_SHIFT) & TLBI_ADDR_MASK)

/* ID_AA64MMFR2_EL1 definitions */
#define ID_AA64MMFR2_EL1_ST_SHIFT	U(28)
#define ID_AA64MMFR2_EL1_ST_MASK	ULL(0xf)

#define ID_AA64MMFR2_EL1_CNP_SHIFT	U(0)
#define ID_AA64MMFR2_EL1_CNP_MASK	ULL(0xf)

/* Custom defined values to indicate the vector offset to exception handlers */
#define ARM_EXCEPTION_SYNC_LEL		0
#define ARM_EXCEPTION_IRQ_LEL		1
#define ARM_EXCEPTION_FIQ_LEL		2
#define ARM_EXCEPTION_SERROR_LEL	3

#define VBAR_CEL_SP_EL0_OFFSET	0x0
#define VBAR_CEL_SP_ELx_OFFSET	0x200
#define VBAR_LEL_AA64_OFFSET	0x400
#define VBAR_LEL_AA32_OFFSET	0x600

#endif /* ARCH_H */
