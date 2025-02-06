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

/* Interrupt Controller registers */
#define ICC_HPPIR1_EL1		S3_0_C12_C12_2
#define ICC_SRE_EL2		S3_4_C12_C9_5

/* Interrupt Controller Control Register */
#define ICC_CTLR_EL1		S3_0_C12_C12_4

#define ICC_CTLR_EL1_EXT_RANGE_BIT	(UL(1) << 19)

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

/* Data Independent Timing Registers */
#define DIT			S3_3_C4_C2_5
#define DIT_BIT			(UL(1) << 24)

/* SCTLR2_EL12 register */
#define SCTLR2_EL12		S3_5_C1_C0_3

/* TCR2_EL12 register */
#define TCR2_EL12		S3_5_C2_C0_3

/* Permission Indirection Registers*/
#define PIRE0_EL2		S3_4_C10_C2_2
#define PIRE0_EL12		S3_5_C10_C2_2
#define PIR_EL12		S3_5_C10_C2_3
#define POR_EL12		S3_5_C10_C2_4
#define S2PIR_EL2		S3_4_C10_C2_5
#define S2POR_EL1		S3_0_C10_C2_5

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

#define TCR_EL2_T1SZ_SHIFT	UL(16)
#define TCR_EL2_T1SZ_WIDTH	UL(6)

#define TCR_EL2_EPD0_BIT	(UL(1) << 7)

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
#define TCR_EL2_TG1_4K		INPLACE(TCR_EL2_TG1, UL(2))

#define TCR_EL2_IPS_SHIFT	UL(32)
#define TCR_EL2_IPS_WIDTH	UL(3)
#define TCR_PS_BITS_4GB		INPLACE(TCR_EL2_IPS, UL(0))
#define TCR_PS_BITS_64GB	INPLACE(TCR_EL2_IPS, UL(1))
#define TCR_PS_BITS_1TB		INPLACE(TCR_EL2_IPS, UL(2))
#define TCR_PS_BITS_4TB		INPLACE(TCR_EL2_IPS, UL(3))
#define TCR_PS_BITS_16TB	INPLACE(TCR_EL2_IPS, UL(4))
#define TCR_PS_BITS_256TB	INPLACE(TCR_EL2_IPS, UL(5))
#define TCR_PS_BITS_4PB		INPLACE(TCR_EL2_IPS, UL(6))

#define TCR_EL2_DS_SHIFT	UL(59)
#define TCR_EL2_DS_WIDTH	UL(1)
#define TCR_EL2_DS_LPA2_EN	INPLACE(TCR_EL2_DS, UL(1))

#define TCR_EL2_A1		(UL(1) << 22)
#define TCR_EL2_AS		(UL(1) << 36)
#define TCR_EL2_HPD0		(UL(1) << 41)
#define TCR_EL2_HPD1		(UL(1) << 42)
#define TCR_EL2_E0PD0		(UL(1) << 55)
#define TCR_EL2_E0PD1		(UL(1) << 56)

#define TCR_TxSZ_MIN		UL(16)
#define TCR_TxSZ_MIN_LPA2	UL(12)
#define TCR_TxSZ_MAX		UL(48)

/* HCR definitions */
#define HCR_FWB		(UL(1) << 46)
#define HCR_TEA		(UL(1) << 37)
#define HCR_API		(UL(1) << 41)
#define HCR_APK		(UL(1) << 40)
#define HCR_TERR	(UL(1) << 36)
#define HCR_TLOR	(UL(1) << 35)
#define HCR_E2H		(UL(1) << 34)
#define HCR_RW		(UL(1) << 31)
#define HCR_TDZ		(UL(1) << 28)
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
#define HCR_BSU_WIDTH	U(2)
#define HCR_BSU_IS	INPLACE(HCR_BSU, UL(1)) /* Barriers are promoted to IS */

#define HCR_FB		(UL(1) << 9)
#define HCR_VI		(UL(1) << 7)
#define HCR_AMO		(UL(1) << 5)
#define HCR_IMO		(UL(1) << 4)
#define HCR_FMO		(UL(1) << 3)
#define HCR_PTW		(UL(1) << 2)
#define HCR_SWIO	(UL(1) << 1)
#define HCR_VM		(UL(1) << 0)

#define HCR_REALM_FLAGS		(HCR_FWB | HCR_E2H | HCR_RW | HCR_TSC |		\
				HCR_AMO | HCR_BSU_IS | HCR_IMO | HCR_FMO |	\
				HCR_PTW | HCR_SWIO | HCR_VM | HCR_TID3 |	\
				HCR_TEA | HCR_API | HCR_APK)

#define HCR_EL2_INIT		(HCR_TGE | HCR_E2H | HCR_TEA)

/* HCRX_EL2 Register */
#define HCRX_EL2	S3_4_C1_C2_2

/* HCRX_EL2 definitions */
#define HCRX_TCR2EN	(UL(1) << 14)
#define HCRX_SCTLR2EN	(UL(1) << 15)

#define HCRX_INIT	(UL(0))

#define MAIR_ELx_ATTR0_SHIFT	0
#define MAIR_ELx_ATTR0_WIDTH	U(8)

/* BRBCR Register */
#define BRBCR_EL1		S2_1_C9_C0_0
#define BRBCR_EL2		S2_4_C9_C0_0

#define BRBCR_INIT		UL(0)

/* HDFGRTR_EL2 Register */
#define HDFGRTR_EL2			S3_4_C3_C1_4

#define HDFGRTR_EL2_NBRBDATA_SHIFT	61
#define HDFGRTR_EL2_NBRBDATA_WIDTH	UL(1)
#define HDFGRTR_EL2_NBRBCTL_SHIFT	60
#define HDFGRTR_EL2_NBRBCTL_WIDTH	UL(1)
#define HDFGRTR_EL2_NBRBIDR_SHIFT	59
#define HDFGRTR_EL2_NBRBIDR_WIDTH	UL(1)

#define HDFGRTR_EL2_INIT_CLEAR_MASK	MASK(HDFGRTR_EL2_NBRBDATA) | \
					MASK(HDFGRTR_EL2_NBRBCTL) | \
					MASK(HDFGRTR_EL2_NBRBIDR)
/* Hypervisor Fine Granule Trap Registers */
#define HFGRTR_EL2			S3_4_C1_C1_4

#define HFGRTR_EL2_NPOR_EL1_BIT		(UL(1) << 60)
#define HFGRTR_EL2_NPOR_EL0_BIT		(UL(1) << 59)
#define HFGRTR_EL2_NPIR_EL1_BIT		(UL(1) << 58)
#define HFGRTR_EL2_NPIRE0_EL1_BIT	(UL(1) << 57)

#define HFGRTR_EL2_INIT			(HFGRTR_EL2_NPOR_EL1_BIT	| \
					 HFGRTR_EL2_NPOR_EL0_BIT	| \
					 HFGRTR_EL2_NPIR_EL1_BIT	| \
					 HFGRTR_EL2_NPIRE0_EL1_BIT)

#define HFGWTR_EL2			S3_4_C1_C1_5


#define HFGWTR_EL2_NPOR_EL1_BIT		(UL(1) << 60)
#define HFGWTR_EL2_NPOR_EL0_BIT		(UL(1) << 59)
#define HFGWTR_EL2_NPIR_EL1_BIT		(UL(1) << 58)
#define HFGWTR_EL2_NPIRE0_EL1_BIT	(UL(1) << 57)

#define HFGWTR_EL2_INIT			(HFGWTR_EL2_NPOR_EL1_BIT	| \
					 HFGWTR_EL2_NPOR_EL0_BIT	| \
					 HFGWTR_EL2_NPIR_EL1_BIT	| \
					 HFGWTR_EL2_NPIRE0_EL1_BIT)

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
#define TTBR_CNP_BIT		UL(1)

#define TTBRx_EL2_CnP_SHIFT	0
#define TTBRx_EL2_CnP_WIDTH	U(1)

#define TTBRx_EL2_BADDR_SHIFT	1
#define TTBRx_EL2_BADDR_WIDTH	U(47)

#define TTBRx_EL2_BADDR_MSB_LPA2_SHIFT		2
#define TTBRx_EL2_BADDR_MSB_LPA2_WIDTH		U(4)
#define EL2_BADDR_MSB_LPA2_SHIFT		48
#define EL2_BADDR_MSB_LPA2_WIDTH		TTBRx_EL2_BADDR_MSB_LPA2_WIDTH

#define TTBRx_EL2_SET_MSB_LPA2(_addr, _dest)	(((_dest) & ~MASK(TTBRx_EL2_BADDR_MSB_LPA2)) |	\
						 (INPLACE(TTBRx_EL2_BADDR_MSB_LPA2,		\
							  EXTRACT(EL2_BADDR_MSB_LPA2, (_addr)))))

#define TTBRx_EL2_ASID_SHIFT	48
#define TTBRx_EL2_ASID_WIDTH	U(16)

/*
 * VTTBR Definitions
 */
#define VTTBR_EL2_VMID_SHIFT	48
#define VTTBR_EL2_VMID_WIDTH	U(16)

/*
 * ESR Definitions
 */
#define ESR_EL2_EC_SHIFT	26
#define ESR_EL2_EC_WIDTH	U(6)

#define ESR_EL2_IL_SHIFT	25
#define ESR_EL2_IL_WIDTH	U(1)

#define ESR_EL2_ISS_SHIFT	0
#define ESR_EL2_ISS_WIDTH	U(25)

#define ESR_EL2_EC_UNKNOWN	INPLACE(ESR_EL2_EC, UL(0))
#define ESR_EL2_EC_WFX		INPLACE(ESR_EL2_EC, UL(1))
#define ESR_EL2_EC_FPU		INPLACE(ESR_EL2_EC, UL(7))
#define ESR_EL2_EC_SVC		INPLACE(ESR_EL2_EC, UL(21))
#define ESR_EL2_EC_HVC		INPLACE(ESR_EL2_EC, UL(22))
#define ESR_EL2_EC_SMC		INPLACE(ESR_EL2_EC, UL(23))
#define ESR_EL2_EC_SYSREG	INPLACE(ESR_EL2_EC, UL(24))
#define ESR_EL2_EC_SVE		INPLACE(ESR_EL2_EC, UL(25))
#define ESR_EL2_EC_SME		INPLACE(ESR_EL2_EC, UL(29))
#define ESR_EL2_EC_INST_ABORT		INPLACE(ESR_EL2_EC, UL(32))
#define ESR_EL2_EC_INST_ABORT_SEL	INPLACE(ESR_EL2_EC, UL(33))
#define ESR_EL2_EC_DATA_ABORT		INPLACE(ESR_EL2_EC, UL(36))
#define ESR_EL2_EC_DATA_ABORT_SEL	INPLACE(ESR_EL2_EC, UL(37))
#define ESR_EL2_EC_SERROR		INPLACE(ESR_EL2_EC, UL(47))

/* Data/Instruction Abort ESR fields */
#define ESR_EL2_ABORT_ISV_BIT		(UL(1) << 24)

#define ESR_EL2_ABORT_SAS_SHIFT		22
#define ESR_EL2_ABORT_SAS_WIDTH		U(2)

#define ESR_EL2_ABORT_SAS_BYTE_VAL	0U
#define ESR_EL2_ABORT_SAS_HWORD_VAL	1U
#define ESR_EL2_ABORT_SAS_WORD_VAL	2U
#define ESR_EL2_ABORT_SAS_DWORD_VAL	3U

#define ESR_EL2_ABORT_SSE_BIT		(UL(1) << 21)

#define ESR_EL2_ABORT_SRT_SHIFT		16
#define ESR_EL2_ABORT_SRT_WIDTH		U(5)

#define ESR_EL2_ABORT_SET_SHIFT		11
#define ESR_EL2_ABORT_SET_WIDTH		U(2)
#define ESR_EL2_ABORT_SET_UER		INPLACE(ESR_EL2_ABORT_SET, UL(0))
#define ESR_EL2_ABORT_SET_UC		INPLACE(ESR_EL2_ABORT_SET, UL(2))
#define ESR_EL2_ABORT_SET_UEO		INPLACE(ESR_EL2_ABORT_SET, UL(3))

#define ESR_EL2_ABORT_SF_BIT		(UL(1) << 15)
#define ESR_EL2_ABORT_FNV_BIT		(UL(1) << 10)
#define ESR_EL2_ABORT_EA_BIT		(UL(1) << 9)
#define ESR_EL2_ABORT_S1PTW_BIT		(UL(1) << 7)
#define ESR_EL2_ABORT_WNR_BIT		(UL(1) << 6)
#define ESR_EL2_ABORT_FSC_SHIFT		0
#define ESR_EL2_ABORT_FSC_WIDTH		U(6)

#define ESR_EL2_ABORT_FSC_TRANSLATION_FAULT	UL(0x04)
#define ESR_EL2_ABORT_FSC_PERM_FAULT_START	UL(0x0c)
#define ESR_EL2_ABORT_FSC_PERM_FAULT_END	UL(0x0f)
#define ESR_EL2_ABORT_FSC_TRANSLATION_FAULT_L0	UL(0x04)
#define ESR_EL2_ABORT_FSC_SEA			UL(0x10)
#define ESR_EL2_ABORT_FSC_SEA_TTW_START		UL(0x13)
#define ESR_EL2_ABORT_FSC_SEA_TTW_END		UL(0x17)
#define ESR_EL2_ABORT_FSC_GPF			UL(0x28)
#define ESR_EL2_ABORT_FSC_LEVEL_SHIFT		0
#define ESR_EL2_ABORT_FSC_LEVEL_WIDTH		U(2)

/* The ESR fields that are reported to the host on Instr./Data Synchronous Abort */
#define ESR_NONEMULATED_ABORT_MASK	( \
		MASK(ESR_EL2_EC)	| \
		MASK(ESR_EL2_ABORT_SET) | \
		ESR_EL2_ABORT_FNV_BIT	| \
		ESR_EL2_ABORT_EA_BIT	| \
		MASK(ESR_EL2_ABORT_FSC))

#define ESR_EMULATED_ABORT_MASK		   ( \
		ESR_NONEMULATED_ABORT_MASK | \
		ESR_EL2_ABORT_ISV_BIT	   | \
		MASK(ESR_EL2_ABORT_SAS)	   | \
		ESR_EL2_ABORT_SF_BIT	   | \
		ESR_EL2_ABORT_WNR_BIT)

#define ESR_EL2_SERROR_DFSC_SHIFT	0
#define ESR_EL2_SERROR_DFSC_WIDTH	U(6)
#define ESR_EL2_SERROR_DFSC_UNCAT	INPLACE(ESR_EL2_SERROR_DFSC, UL(0))
#define ESR_EL2_SERROR_DFSC_ASYNC	INPLACE(ESR_EL2_SERROR_DFSC, UL(0x11))

#define ESR_EL2_SERROR_EA_BIT		(UL(1) << 9)

#define ESR_EL2_SERROR_AET_SHIFT	10
#define ESR_EL2_SERROR_AET_WIDTH	U(3)
#define ESR_EL2_SERROR_AET_UC		INPLACE(ESR_EL2_SERROR_AET, UL(0))
#define ESR_EL2_SERROR_AET_UEU		INPLACE(ESR_EL2_SERROR_AET, UL(1))
#define ESR_EL2_SERROR_AET_UEO		INPLACE(ESR_EL2_SERROR_AET, UL(2))
#define ESR_EL2_SERROR_AET_UER		INPLACE(ESR_EL2_SERROR_AET, UL(3))
#define ESR_EL2_SERROR_AET_CE		INPLACE(ESR_EL2_SERROR_AET, UL(6))

#define ESR_EL2_SERROR_IESB_BIT		(UL(1) << 13)
#define ESR_EL2_SERROR_IDS_BIT		(UL(1) << 24)

/* The ESR fields that are reported to the host on SError */
#define ESR_SERROR_MASK			 ( \
		ESR_EL2_SERROR_IDS_BIT	 | \
		MASK(ESR_EL2_SERROR_AET) | \
		ESR_EL2_SERROR_EA_BIT	 | \
		MASK(ESR_EL2_SERROR_DFSC))

/*
 * Define macros to generate EL2 SYSREGs ID as reported by ESR on an
 * exception.
 */
#define ESR_EL2_SYSREG_TRAP_OP0_SHIFT	20
#define ESR_EL2_SYSREG_TRAP_OP0_WIDTH	U(2)

#define ESR_EL2_SYSREG_TRAP_OP2_SHIFT	17
#define ESR_EL2_SYSREG_TRAP_OP2_WIDTH	U(3)

#define ESR_EL2_SYSREG_TRAP_OP1_SHIFT	14
#define ESR_EL2_SYSREG_TRAP_OP1_WIDTH	U(3)

#define ESR_EL2_SYSREG_TRAP_CRN_SHIFT	10
#define ESR_EL2_SYSREG_TRAP_CRN_WIDTH	U(4)

#define ESR_EL2_SYSREG_TRAP_RT_SHIFT	5
#define ESR_EL2_SYSREG_TRAP_RT_WIDTH	U(5)

#define ESR_EL2_SYSREG_TRAP_CRM_SHIFT	1
#define ESR_EL2_SYSREG_TRAP_CRM_WIDTH	U(4)

/* WFx ESR fields */
#define ESR_EL2_WFx_TI_BIT		(UL(1) << 0)

/* xVC ESR fields */
#define ESR_EL2_xVC_IMM_SHIFT		0
#define ESR_EL2_xVC_IMM_WIDTH		U(16)

/* MPAM2_EL2 definitions */
#define MPAM2_EL2_TIDR_BIT		(UL(1) << 58)
#define MPAM2_EL2_TRAPMPAM0EL1_BIT	(UL(1) << 49)
#define MPAM2_EL2_TRAPMPAM1EL1_BIT	(UL(1) << 48)

#define MPAM2_EL2_INIT			(MPAM2_EL2_TRAPMPAM0EL1_BIT | \
					 MPAM2_EL2_TRAPMPAM1EL1_BIT | \
					 MPAM2_EL2_TIDR_BIT)

/* MPAMHCR_EL2 definitions */
#define MPAMHCR_EL2_TRAP_MPAMIDR_EL1_BIT	(UL(1) << 31)

#define MPAMHCR_EL2_INIT			(MPAMHCR_EL2_TRAP_MPAMIDR_EL1_BIT)

/* MPAMIDR_EL1 definitions */
#define MPAMIDR_EL1_HAS_TIDR_BIT		(UL(1) << 58)
#define MPAMIDR_EL1_HAS_HCR_BIT			(UL(1) << 17)

/******************************************************
 * ID_AA64DFR0_EL1 definitions
 ******************************************************/

#define ID_AA64DFR0_EL1_HPMN0_SHIFT		UL(60)
#define ID_AA64DFR0_EL1_HPMN0_WIDTH		UL(4)

#define ID_AA64DFR0_EL1_ExtTrcBuff_SHIFT	UL(56)
#define ID_AA64DFR0_EL1_ExtTrcBuff_WIDTH	UL(4)

#define ID_AA64DFR0_EL1_BRBE_SHIFT		UL(52)
#define ID_AA64DFR0_EL1_BRBE_WIDTH		UL(4)

#define ID_AA64DFR0_EL1_MTPMU_SHIFT		UL(48)
#define ID_AA64DFR0_EL1_MTPMU_WIDTH		UL(4)

#define ID_AA64DFR0_EL1_TraceBuffer_SHIFT	UL(44)
#define ID_AA64DFR0_EL1_TraceBuffer_WIDTH	UL(4)

#define ID_AA64DFR0_EL1_TraceFilt_SHIFT		UL(40)
#define ID_AA64DFR0_EL1_TraceFilt_WIDTH		UL(4)

#define ID_AA64DFR0_EL1_DoubleLock_SHIFT	UL(36)
#define ID_AA64DFR0_EL1_DoubleLock_WIDTH	UL(4)

#define ID_AA64DFR0_EL1_PMSVer_SHIFT		UL(32)
#define ID_AA64DFR0_EL1_PMSVer_WIDTH		UL(4)

#define ID_AA64DFR0_EL1_CTX_CMPS_SHIFT		UL(28)
#define ID_AA64DFR0_EL1_CTX_CMPS_WIDTH		UL(4)

#define ID_AA64DFR0_EL1_SEBEP_SHIFT		UL(24)
#define ID_AA64DFR0_EL1_SEBEP_WIDTH		UL(4)

#define ID_AA64DFR0_EL1_WRPs_SHIFT		UL(20)
#define ID_AA64DFR0_EL1_WRPs_WIDTH		UL(4)

#define ID_AA64DFR0_EL1_PMSS_SHIFT		UL(16)
#define ID_AA64DFR0_EL1_PMSS_WIDTH		UL(4)

#define ID_AA64DFR0_EL1_BRPs_SHIFT		UL(12)
#define ID_AA64DFR0_EL1_BRPs_WIDTH		UL(4)

#define ID_AA64DFR0_EL1_PMUVer_SHIFT		UL(8)
#define ID_AA64DFR0_EL1_PMUVer_WIDTH		UL(4)

/* Performance Monitors Extension version */
#define ID_AA64DFR0_EL1_PMUv3p7			UL(7)
#define ID_AA64DFR0_EL1_PMUv3p8			UL(8)
#define ID_AA64DFR0_EL1_PMUv3p9			UL(9)

#define ID_AA64DFR0_EL1_TraceVer_SHIFT		UL(4)
#define ID_AA64DFR0_EL1_TraceVer_WIDTH		UL(4)

#define ID_AA64DFR0_EL1_DebugVer_SHIFT		UL(0)
#define ID_AA64DFR0_EL1_DebugVer_WIDTH		UL(4)

/* Debug architecture version */
#define ID_AA64DFR0_EL1_Debugv8			UL(6)
#define ID_AA64DFR0_EL1_Debugv8p1		UL(7)
#define ID_AA64DFR0_EL1_Debugv8p2		UL(8)
#define ID_AA64DFR0_EL1_Debugv8p4		UL(9)
#define ID_AA64DFR0_EL1_Debugv8p8		UL(10)
#define ID_AA64DFR0_EL1_Debugv8p9		UL(11)

/******************************************************
 * ID_AA64DFR1_EL1 definitions
 ******************************************************/

#define ID_AA64DFR1_EL1_ABL_CMPS_SHIFT		UL(56)
#define ID_AA64DFR1_EL1_ABL_CMPS_WIDTH		UL(8)

#define ID_AA64DFR1_EL1_DPFZS_SHIFT		UL(52)
#define ID_AA64DFR1_EL1_DPFZS_WIDTH		UL(4)

#define ID_AA64DFR1_EL1_EBEP_SHIFT		UL(48)
#define ID_AA64DFR1_EL1_EBEP_WIDTH		UL(4)

#define ID_AA64DFR1_EL1_ITE_SHIFT		UL(44)
#define ID_AA64DFR1_EL1_ITE_WIDTH		UL(4)

#define ID_AA64DFR1_EL1_ABLE_SHIFT		UL(40)
#define ID_AA64DFR1_EL1_ABLE_WIDTH		UL(4)

#define ID_AA64DFR1_EL1_ICNTR_SHIFT		UL(36)
#define ID_AA64DFR1_EL1_ICNTR_WIDTH		UL(4)

#define ID_AA64DFR1_EL1_SPMU_SHIFT		UL(32)
#define ID_AA64DFR1_EL1_SPMU_WIDTH		UL(4)

#define ID_AA64DFR1_EL1_CTX_CMP_SHIFT		UL(24)
#define ID_AA64DFR1_EL1_CTX_CMP_WIDTH		UL(8)

#define ID_AA64DFR1_EL1_WRPs_SHIFT		UL(16)
#define ID_AA64DFR1_EL1_WRPs_WIDTH		UL(8)

#define ID_AA64DFR1_EL1_BRPs_SHIFT		UL(8)
#define ID_AA64DFR1_EL1_BRPs_WIDTH		UL(8)

#define ID_AA64DFR1_EL1_SYSPMUID_SHIFT         UL(0)
#define ID_AA64DFR1_EL1_SYSPMUID_WIDTH         UL(8)

/******************************************************
 * ID_AA64DFR2_EL1 definitions
 ******************************************************/

#define ID_AA64DFR2_EL1_BWE_SHIFT		UL(4)
#define ID_AA64DFR2_EL1_BWE_WIDTH		UL(4)

/******************************************************
 * ID_AA64PFR0_EL1 definitions
 ******************************************************/

#define ID_AA64PFR0_EL1_CSV3_SHIFT	UL(60)
#define ID_AA64PFR0_EL1_CSV3_WIDTH	UL(4)

#define ID_AA64PFR0_EL1_CSV2_SHIFT	UL(56)
#define ID_AA64PFR0_EL1_CSV2_WIDTH	UL(4)

#define ID_AA64PFR0_EL1_DIT_SHIFT	UL(48)
#define ID_AA64PFR0_EL1_DIT_WIDTH	UL(4)

#define ID_AA64PFR0_EL1_AMU_SHIFT	UL(44)
#define ID_AA64PFR0_EL1_AMU_WIDTH	UL(4)

#define ID_AA64PFR0_EL1_MPAM_SHIFT	UL(40)
#define ID_AA64PFR0_EL1_MPAM_WIDTH	UL(4)

#define ID_AA64PFR0_EL1_SEL2_SHIFT	UL(36)
#define ID_AA64PFR0_EL1_SEL2_WIDTH	UL(4)

#define ID_AA64PFR0_EL1_SVE_SHIFT	UL(32)
#define ID_AA64PFR0_EL1_SVE_WIDTH	UL(4)

#define ID_AA64PFR0_EL1_RAS_SHIFT	UL(28)
#define ID_AA64PFR0_EL1_RAS_WIDTH	UL(4)

#define ID_AA64PFR0_EL1_GIC_SHIFT	UL(24)
#define ID_AA64PFR0_EL1_GIC_WIDTH	UL(4)

#define ID_AA64PFR0_EL1_ADVSIMD_WIDTH	UL(20)
#define ID_AA64PFR0_EL1_ADVSIMD_SHIFT	UL(4)

#define ID_AA64PFR0_EL1_FP_WIDTH	UL(16)
#define ID_AA64PFR0_EL1_FP_SHIFT	UL(4)

#define ID_AA64PFR0_EL1_EL3_WIDTH	UL(12)
#define ID_AA64PFR0_EL1_EL3_SHIFT	UL(4)

#define ID_AA64PFR0_EL1_EL2_WIDTH	UL(8)
#define ID_AA64PFR0_EL1_EL2_SHIFT	UL(4)

#define ID_AA64PFR0_EL1_EL1_SHIFT	UL(4)
#define ID_AA64PFR0_EL1_EL1_WIDTH	UL(4)

#define ID_AA64PFR0_EL1_EL0_SHIFT	UL(0)
#define ID_AA64PFR0_EL1_EL0_WIDTH	UL(4)

/******************************************************
 * ID_AA64PFR1_EL1 definitions
 ******************************************************/

#define ID_AA64PFR1_EL1_PFAR_SHIFT		UL(60)
#define ID_AA64PFR1_EL1_PFAR_WIDTH		UL(4)

#define ID_AA64PFR1_EL1_DF2_SHIFT		UL(56)
#define ID_AA64PFR1_EL1_DF2_WIDTH		UL(4)

#define ID_AA64PFR1_EL1_MTEX_SHIFT		UL(52)
#define ID_AA64PFR1_EL1_MTEX_WIDTH		UL(4)

#define ID_AA64PFR1_EL1_THE_SHIFT		UL(48)
#define ID_AA64PFR1_EL1_THE_WIDTH		UL(4)

#define ID_AA64PFR1_EL1_GCS_SHIFT		UL(44)
#define ID_AA64PFR1_EL1_GCS_WIDTH		UL(4)

#define ID_AA64PFR1_EL1_NMI_SHIFT		UL(36)
#define ID_AA64PFR1_EL1_NMI_WIDTH		UL(4)

#define ID_AA64PFR1_EL1_CSV2_F_SHIFT		UL(32)
#define ID_AA64PFR1_EL1_CSV2_F_WIDTH		UL(4)

#define ID_AA64PFR1_EL1_RNDR_TRAP_SHIFT		UL(28)
#define ID_AA64PFR1_EL1_RNDR_TRAP_WIDTH		UL(4)

#define ID_AA64PFR1_EL1_SME_SHIFT		UL(24)
#define ID_AA64PFR1_EL1_SME_WIDTH		UL(4)
#define ID_AA64PFR1_EL1_SME_NOT_IMPLEMENTED	UL(0)
#define ID_AA64PFR1_EL1_SME_IMPLEMENTED		UL(1)
#define ID_AA64PFR1_EL1_SME2_IMPLEMENTED	UL(2)

#define ID_AA64PFR1_EL1_MPAM_F_SHIFT		UL(16)
#define ID_AA64PFR1_EL1_MPAM_F_WIDTH		UL(4)

#define ID_AA64PFR1_EL1_RAS_F_SHIFT		UL(12)
#define ID_AA64PFR1_EL1_RAS_F_WIDTH		UL(4)

#define ID_AA64PFR1_EL1_MTE_SHIFT		UL(8)
#define ID_AA64PFR1_EL1_MTE_WIDTH		UL(4)
#define ID_AA64PFR1_EL1_MTE_NOT_IMPLEMENTED	UL(0)
#define ID_AA64PFR1_EL1_MTE1			UL(1)
#define ID_AA64PFR1_EL1_MTE2			UL(2)
#define ID_AA64PFR1_EL1_MTE3			UL(3)

#define ID_AA64PFR1_EL1_SSBS_SHIFT		UL(4)
#define ID_AA64PFR1_EL1_SSBS_WIDTH		UL(4)
#define ID_AA64PFR1_EL1_SSBS_NOT_IMPLEMENTED	UL(0)
#define ID_AA64PFR1_EL1_FEAT_SSBS		UL(1)
#define ID_AA64PFR1_EL1_FEAT_SSBS2		UL(2)

#define ID_AA64PFR1_EL1_BT_SHIFT		UL(0)
#define ID_AA64PFR1_EL1_BT_WIDTH		UL(4)

/******************************************************
 * ID_AA64PFR2_EL1 definitions
 ******************************************************/

#define ID_AA64PFR2_EL1			S3_0_C0_C4_2

#define ID_AA64PFR2_EL1_UINJ_SHIFT		UL(16)
#define ID_AA64PFR2_EL1_UINJ_WIDTH		UL(4)

/******************************************************
 * ID_AA64MMFR0_EL1 definitions
 ******************************************************/

#define ID_AA64MMFR0_EL1_ECV_SHIFT		UL(60)
#define ID_AA64MMFR0_EL1_ECV_WIDTH		UL(4)
#define ID_AA64MMFR0_EL1_ECV_NOT_SUPPORTED	UL(0x0)
#define ID_AA64MMFR0_EL1_ECV_SUPPORTED		UL(0x1)
#define ID_AA64MMFR0_EL1_ECV_SELF_SYNCH		ULL(0x2)

#define ID_AA64MMFR0_EL1_FGT_SHIFT		UL(56)
#define ID_AA64MMFR0_EL1_FGT_WIDTH		UL(4)
#define ID_AA64MMFR0_EL1_FGT_NOT_SUPPORTED	UL(0x0)
#define ID_AA64MMFR0_EL1_FGT_SUPPORTED		UL(0x1)
#define ID_AA64MMFR0_EL1_FGT2_SUPPORTED		UL(0x2)

#define ID_AA64MMFR0_EL1_ExS_SHIFT		UL(44)
#define ID_AA64MMFR0_EL1_ExS_WIDTH		UL(4)

#define ID_AA64MMFR0_EL1_TGRAN4_2_SHIFT		U(40)
#define ID_AA64MMFR0_EL1_TGRAN4_2_WIDTH		U(4)
#define ID_AA64MMFR0_EL1_TGRAN4_2_TGRAN4	UL(0x0)
#define ID_AA64MMFR0_EL1_TGRAN4_2_NOT_SUPPORTED	UL(0x1)
#define ID_AA64MMFR0_EL1_TGRAN4_2_SUPPORTED	UL(0x2)
#define ID_AA64MMFR0_EL1_TGRAN4_2_LPA2		UL(0x3)

#define ID_AA64MMFR0_EL1_TGRAN64_2_SHIFT	U(36)
#define ID_AA64MMFR0_EL1_TGRAN64_2_WIDTH	U(4)

#define ID_AA64MMFR0_EL1_TGRAN16_2_SHIFT		UL(32)
#define ID_AA64MMFR0_EL1_TGRAN16_2_WIDTH		UL(4)
#define ID_AA64MMFR0_EL1_TGRAN16_2_TGRAN16		UL(0x0)
#define ID_AA64MMFR0_EL1_TGRAN16_2_NOT_SUPPORTED	UL(0x1)
#define ID_AA64MMFR0_EL1_TGRAN16_2_SUPPORTED		UL(0x2)
#define ID_AA64MMFR0_EL1_TGRAN16_2_LPA2			UL(0x3)

#define ID_AA64MMFR0_EL1_TGRAN4_SHIFT		UL(28)
#define ID_AA64MMFR0_EL1_TGRAN4_WIDTH		UL(4)
#define ID_AA64MMFR0_EL1_TGRAN4_SUPPORTED	UL(0x0)
#define ID_AA64MMFR0_EL1_TGRAN4_LPA2		UL(0x1)
#define ID_AA64MMFR0_EL1_TGRAN4_NOT_SUPPORTED	UL(0xf)

#define ID_AA64MMFR0_EL1_TGRAN64_SHIFT		UL(24)
#define ID_AA64MMFR0_EL1_TGRAN64_WIDTH		UL(4)
#define ID_AA64MMFR0_EL1_TGRAN64_SUPPORTED	UL(0x0)
#define ID_AA64MMFR0_EL1_TGRAN64_NOT_SUPPORTED	UL(0xf)

#define ID_AA64MMFR0_EL1_TGRAN16_SHIFT		UL(20)
#define ID_AA64MMFR0_EL1_TGRAN16_WIDTH		UL(4)
#define ID_AA64MMFR0_EL1_TGRAN16_NOT_SUPPORTED	UL(0x0)
#define ID_AA64MMFR0_EL1_TGRAN16_SUPPORTED	UL(0x1)
#define ID_AA64MMFR0_EL1_TGRAN16_LPA2		UL(0x2)

#define ID_AA64MMFR0_EL1_BIGENDEL0_SHIFT	UL(16)
#define ID_AA64MMFR0_EL1_BIGENDEL0_WIDTH	UL(4)

#define ID_AA64MMFR0_EL1_SNSMEM_SHIFT		UL(12)
#define ID_AA64MMFR0_EL1_SNSMEM_WIDTH		UL(4)

#define ID_AA64MMFR0_EL1_BIGEND_SHIFT		UL(8)
#define ID_AA64MMFR0_EL1_BIGEND_WIDTH		UL(4)

#define ID_AA64MMFR0_EL1_ASID_SHIFT		UL(4)
#define ID_AA64MMFR0_EL1_ASID_WIDTH		UL(4)

#define ID_AA64MMFR0_EL1_PARANGE_SHIFT		U(0)
#define ID_AA64MMFR0_EL1_PARANGE_WIDTH		UL(4)

/* Defines for PA width corresponding to PARange [0:3] in id_aa64mmfr0_el1 */
#define PARANGE_WIDTH_32BITS	U(32)		/* PARange - 0x0 */
#define PARANGE_WIDTH_36BITS	U(36)		/* PARange - 0x1 */
#define PARANGE_WIDTH_40BITS	U(40)		/* PARange - 0x2 */
#define PARANGE_WIDTH_42BITS	U(42)		/* PARange - 0x3 */
#define PARANGE_WIDTH_44BITS	U(44)		/* PARange - 0x4 */
#define PARANGE_WIDTH_48BITS	U(48)		/* PARange - 0x5 */
#define PARANGE_WIDTH_52BITS	U(52)		/* PARange - 0x6 */


/******************************************************
 * ID_AA64MMFR1_EL1 definitions
 ******************************************************/

#define ID_AA64MMFR1_EL1_VMIDBits_SHIFT		UL(4)
#define ID_AA64MMFR1_EL1_VMIDBits_WIDTH		UL(4)
#define ID_AA64MMFR1_EL1_VMIDBits_8		UL(0)
#define ID_AA64MMFR1_EL1_VMIDBits_16		UL(2)

/******************************************************
 * ID_AA64MMFR2_EL1 definitions
 ******************************************************/

#define ID_AA64MMFR2_EL1_ST_SHIFT	UL(28)
#define ID_AA64MMFR2_EL1_ST_WIDTH	UL(4)

#define ID_AA64MMFR2_EL1_CNP_SHIFT	UL(0)
#define ID_AA64MMFR2_EL1_CNP_WIDTH	UL(4)

/******************************************************
 * ID_AA64MMFR3_EL1 definitions
 ******************************************************/

#define ID_AA64MMFR3_EL1_FPACC_SHIFT	UL(60)
#define ID_AA64MMFR3_EL1_FPACC_WIDTH	UL(4)

#define ID_AA64MMFR3_EL1_ADERR_SHIFT	UL(56)
#define ID_AA64MMFR3_EL1_ADERR_WIDTH	UL(4)

#define ID_AA64MMFR3_EL1_SDERR_SHIFT	UL(52)
#define ID_AA64MMFR3_EL1_SDERR_WIDTH	UL(4)

#define ID_AA64MMFR3_EL1_ANERR_SHIFT	UL(44)
#define ID_AA64MMFR3_EL1_ANERR_WIDTH	UL(4)

#define ID_AA64MMFR3_EL1_SNERR_SHIFT	UL(40)
#define ID_AA64MMFR3_EL1_SNERR_WIDTH	UL(4)

#define ID_AA64MMFR3_EL1_D128_2_SHIFT	UL(36)
#define ID_AA64MMFR3_EL1_D128_2_WIDTH	UL(4)

#define ID_AA64MMFR3_EL1_D128_SHIFT	UL(32)
#define ID_AA64MMFR3_EL1_D128_WIDTH	UL(4)

#define ID_AA64MMFR3_EL1_MEC_SHIFT	UL(28)
#define ID_AA64MMFR3_EL1_MEC_WIDTH	UL(4)

#define ID_AA64MMFR3_EL1_AIE_SHIFT	UL(24)
#define ID_AA64MMFR3_EL1_AIE_WIDTH	UL(4)

#define ID_AA64MMFR3_EL1_S2POE_SHIFT	UL(20)
#define ID_AA64MMFR3_EL1_S2POE_WIDTH	UL(4)

#define ID_AA64MMFR3_EL1_S1POE_SHIFT	UL(16)
#define ID_AA64MMFR3_EL1_S1POE_WIDTH	UL(4)

#define ID_AA64MMFR3_EL1_S2PIE_SHIFT	UL(12)
#define ID_AA64MMFR3_EL1_S2PIE_WIDTH	UL(4)

#define ID_AA64MMFR3_EL1_S1PIE_SHIFT	UL(8)
#define ID_AA64MMFR3_EL1_S1PIE_WIDTH	UL(4)

#define ID_AA64MMFR3_EL1_SCTLRX_SHIFT	UL(4)
#define ID_AA64MMFR3_EL1_SCTLRX_WIDTH	UL(4)

#define ID_AA64MMFR3_EL1_TCRX_SHIFT	UL(0)
#define ID_AA64MMFR3_EL1_TCRX_WIDTH	UL(4)

/******************************************************
 * ID_AA64MMFR4_EL1 definitions
 ******************************************************/

#define ID_AA64MMFR4_EL1_E3DSE_SHIFT	UL(36)
#define ID_AA64MMFR4_EL1_E3DSE_WIDTH	UL(4)

#define ID_AA64MMFR4_EL1_RMEGDI_SHIFT	UL(28)
#define ID_AA64MMFR4_EL1_RMEGDI_WIDTH	UL(4)

#define ID_AA64MMFR4_EL1_E2H0_SHIFT	UL(24)
#define ID_AA64MMFR4_EL1_E2H0_WIDTH	UL(4)

#define ID_AA64MMFR4_EL1_NV_FRAC_SHIFT	UL(20)
#define ID_AA64MMFR4_EL1_NV_FRAC_WIDTH	UL(4)

#define ID_AA64MMFR4_EL1_FGWTE3_SHIFT	UL(16)
#define ID_AA64MMFR4_EL1_FGWTE3_WIDTH	UL(4)

#define ID_AA64MMFR4_EL1_HACDBS_SHIFT	UL(12)
#define ID_AA64MMFR4_EL1_HACDBS_WIDTH	UL(4)

#define ID_AA64MMFR4_EL1_ASID2_SHIFT	UL(8)
#define ID_AA64MMFR4_EL1_ASID2_WIDTH	UL(4)

#define ID_AA64MMFR4_EL1_EIESB_SHIFT	UL(4)
#define ID_AA64MMFR4_EL1_EIESB_WIDTH	UL(4)

#define ID_AA64MMFR4_EL1_POPS_SHIFT	UL(0)
#define ID_AA64MMFR4_EL1_POPS_WIDTH	UL(4)

/******************************************************
 * ID_AA64ISAR0_EL1 definitions
 ******************************************************/

#define ID_AA64ISAR0_EL1_RNDR_SHIFT		UL(60)
#define ID_AA64ISAR0_EL1_RNDR_WIDTH		UL(4)

/* SME Feature ID register 0 */
#define ID_AA64SMFR0_EL1		S3_0_C0_C4_5

/* SVE Feature ID register 0 */
#define ID_AA64ZFR0_EL1			S3_0_C0_C4_4

#define ID_AA64FPFR0_EL1		S3_0_C0_C4_7
#define ID_AA64DFR2_EL1			S3_0_C0_C5_2
#define ID_AA64ISAR2_EL1		S3_0_C0_C6_2
#define ID_AA64ISAR3_EL1		S3_0_C0_C6_3

#define ID_AA64MMFR3_EL1		S3_0_C0_C7_3
#define ID_AA64MMFR4_EL1		S3_0_C0_C7_4


/* PAR_EL1 definitions */
#define PAR_EL1_F_BIT			(UL(1) << 0)

/* HPFAR_EL2 definitions */
#define HPFAR_EL2_FIPA_SHIFT		4
#define HPFAR_EL2_FIPA_WIDTH		U(40)
#define HPFAR_EL2_FIPA_OFFSET		8

/* SPSR definitions */
#define SPSR_EL2_MODE_SHIFT		0
#define SPSR_EL2_MODE_WIDTH		U(4)
#define SPSR_EL2_MODE_EL0t		INPLACE(SPSR_EL2_MODE, UL(0))

#define SPSR_EL2_MODE_SHIFT		0
#define SPSR_EL2_MODE_WIDTH		U(4)
#define SPSR_EL2_MODE_EL1h		INPLACE(SPSR_EL2_MODE, UL(5))
#define SPSR_EL2_MODE_EL1t		INPLACE(SPSR_EL2_MODE, UL(4))

/* FIXME: DAIF definitions are redundant here. Might need unification. */
#define SPSR_EL2_nRW_SHIFT		4
#define SPSR_EL2_nRW_WIDTH		U(1)
#define SPSR_EL2_nRW_AARCH64		INPLACE(SPSR_EL2_nRW, UL(0))
#define SPSR_EL2_nRW_AARCH32		INPLACE(SPSR_EL2_nRW, UL(1))

#define SPSR_EL2_DAIF_SHIFT		6
#define SPSR_EL2_DAIF_WIDTH		U(4)
#define SPSR_EL2_AIF_SHIFT		U(6)

#define SPSR_EL2_BTYPE_SHIFT		U(10)
#define SPSR_EL2_BTYPE_WIDTH		U(2)

#define SPSR_EL2_NZCV_BITS_SHIFT	U(28)
#define SPSR_EL2_NZCV_BITS_WIDTH	U(4)

#define DAIF_FIQ_BIT			(UL(1) << 0)
#define DAIF_IRQ_BIT			(UL(1) << 1)
#define DAIF_ABT_BIT			(UL(1) << 2)
#define DAIF_DBG_BIT			(UL(1) << 3)

#define SPSR_EL2_F_BIT			(UL(1) << 6)
#define SPSR_EL2_I_BIT			(UL(1) << 7)
#define SPSR_EL2_A_BIT			(UL(1) << 8)
#define SPSR_EL2_D_BIT			(UL(1) << 9)
#define SPSR_EL2_SSBS_BIT		(UL(1) << 12)
#define SPSR_EL2_ALLINT_BIT		(UL(1) << 13)
#define SPSR_EL2_IL_BIT			(UL(1) << 20)
#define SPSR_EL2_SS_BIT			(UL(1) << 21)
#define SPSR_EL2_PAN_BIT		(UL(1) << 22)
#define SPSR_EL2_UAO_BIT		(UL(1) << 23)
#define SPSR_EL2_DIT_BIT		(UL(1) << 24)
#define SPSR_EL2_TCO_BIT		(UL(1) << 25)
#define SPSR_EL2_V_BIT			(UL(1) << 28)
#define SPSR_EL2_C_BIT			(UL(1) << 29)
#define SPSR_EL2_Z_BIT			(UL(1) << 30)
#define SPSR_EL2_N_BIT			(UL(1) << 31)
#define SPSR_EL2_PM_BIT			(UL(1) << 32)
#define SPSR_EL2_PPEND_BIT		(UL(1) << 33)
#define SPSR_EL2_EXLOCK_BIT		(UL(1) << 34)

/* Floating point control and status register */
#define FPCR				S3_3_C4_C4_0
#define FPSR				S3_3_C4_C4_1

/* SVE Control Register */
#define ZCR_EL2				S3_4_C1_C2_0
#define ZCR_EL2_LEN_SHIFT		UL(0)
#define ZCR_EL2_LEN_WIDTH		UL(4)

#define ZCR_EL12			S3_5_C1_C2_0

/* SME Control Register */
#define SMCR_EL2			S3_4_C1_C2_6
#define SMCR_EL2_LEN_SHIFT		UL(0)
#define SMCR_EL2_LEN_WIDTH		UL(4)
/*
 * SMCR_EL2_RAZ_LEN is defined to find the architecturally permitted SVL. This
 * is a combination of RAZ and LEN bit fields.
 */
#define SMCR_EL2_RAZ_LEN_SHIFT		UL(0)
#define SMCR_EL2_RAZ_LEN_WIDTH		UL(9)
#define SMCR_EL2_EZT0_BIT		(UL(1) << 30)
#define SMCR_EL2_FA64_BIT		(UL(1) << 31)

/* Streaming Vector Control register */
#define SVCR				S3_3_C4_C2_2
#define SVCR_SM_BIT			(UL(1) << 0)
#define SVCR_ZA_BIT			(UL(1) << 1)

/* VTCR definitions */
#define VTCR_T0SZ_SHIFT		0
#define VTCR_T0SZ_WIDTH		U(6)

#define VTCR_SL0_SHIFT		6
#define VTCR_SL0_WIDTH		U(2)

#define VTCR_SL0_4K_L2		INPLACE(VTCR_SL0, UL(0))
#define VTCR_SL0_4K_L1		INPLACE(VTCR_SL0, UL(1))
#define VTCR_SL0_4K_L0		INPLACE(VTCR_SL0, UL(2))
#define VTCR_SL0_4K_L3		INPLACE(VTCR_SL0, UL(3))
#define VTCR_SL0_4K_LM1		VTCR_SL0_4K_L2

#define VTCR_SL2_SHIFT		33
#define VTCR_SL2_WIDTH		U(1)
#define VCTR_SL2_4K_LM1		INPLACE(VTCR_SL2, UL(1))

#define VTCR_DS_SHIFT		32
#define VTCR_DS_WIDTH		U(1)
#define VTCR_DS_52BIT		INPLACE(VTCR_DS, UL(1))

#define VTCR_IRGN0_SHIFT	8
#define VTCR_IRGN0_WIDTH	U(2)
#define VTCR_IRGN0_WBRAWA	INPLACE(VTCR_IRGN0, UL(1))

#define VTCR_ORGN0_SHIFT	10
#define VTCR_ORGN0_WIDTH	U(2)
#define VTCR_ORGN0_WBRAWA	INPLACE(VTCR_ORGN0, UL(1))

#define VTCR_SH0_SHIFT		12
#define VTCR_SH0_WIDTH		U(2)
#define VTCR_SH0_IS		INPLACE(VTCR_SH0, UL(3))

#define VTCR_TG0_SHIFT		14
#define VTCR_TG0_WIDTH		U(2)
#define VTCR_TG0_4K		INPLACE(VTCR_TG0, UL(0))

#define VTCR_PS_SHIFT		16
#define VTCR_PS_WIDTH		U(3)
#define VTCR_PS_32		INPLACE(VTCR_PS, UL(0))
#define VTCR_PS_36		INPLACE(VTCR_PS, UL(1))
#define VTCR_PS_40		INPLACE(VTCR_PS, UL(2))
#define VTCR_PS_42		INPLACE(VTCR_PS, UL(3))
#define VTCR_PS_44		INPLACE(VTCR_PS, UL(4))
#define VTCR_PS_48		INPLACE(VTCR_PS, UL(5))
#define VTCR_PS_52		INPLACE(VTCR_PS, UL(6))

#define VTCR_VS			(UL(1) << 19)
#define VTCR_NSA		(UL(1) << 30)
#define VTCR_RES1		(UL(1) << 31)
#define VTCR_S2PIE		(UL(1) << 36)
#define VTCR_S2POE		(UL(1) << 37)

#define VTCR_FLAGS ( \
	VTCR_IRGN0_WBRAWA | /* PTW inner cache attr. is WB RAWA */ \
	VTCR_ORGN0_WBRAWA | /* PTW outer cache attr. is WB RAWA */ \
	VTCR_SH0_IS       | /* PTW shareability attr. is Inner Sharable */ \
	VTCR_TG0_4K       | /* 4K granule size in non-secure PT */ \
	/* VS = 0              size(VMID) = 8 */ \
	/* NSW = 0             non-secure s2 is made of secure pages */ \
	VTCR_NSA	  | /* non-secure IPA maps to non-secure PA */ \
	VTCR_RES1 \
	)

/* PMCR_EL0 Definitions */
#define PMCR_EL0_N_SHIFT		11
#define PMCR_EL0_N_WIDTH		U(5)
#define PMCR_EL0_LC_BIT			(UL(1) << 6)
#define PMCR_EL0_DP_BIT			(UL(1) << 5)
#define PMCR_EL0_C_BIT			(UL(1) << 2)
#define PMCR_EL0_P_BIT			(UL(1) << 1)
#define PMCR_EL0_E_BIT			(UL(1) << 0)

#define PMCR_EL0_INIT			(PMCR_EL0_LC_BIT | PMCR_EL0_DP_BIT)
#define PMCR_EL0_INIT_RESET		(PMCR_EL0_INIT | PMCR_EL0_C_BIT | \
					 PMCR_EL0_P_BIT)
/* PMSELR_EL0 Definitions */
#define PMSELR_EL0_SEL_SHIFT		0
#define PMSELR_EL0_SEL_WIDTH		U(5)

/* DCZID_EL0 Definitions */
#define DCZID_EL0_BS_SHIFT		0
#define DCZID_EL0_BS_WIDTH		U(4)
#define DCZID_EL0_DZP_BIT		(UL(1) << 4)

/* CTR_EL0 Definitions */
#define CTR_EL0				S3_3_C0_C0_1
#define CTR_EL0_DminLine_SHIFT		16
#define CTR_EL0_DminLine_WIDTH		U(4)

/* MDSCR_EL1 Definitions */
#define MDSCR_EL1_TDCC_BIT	(UL(1) << 12)

/* SCTLR register definitions */
#define SCTLR_ELx_RES1_BIT		((UL(1) << 22)	/* TODO: ARMv8.5-CSEH, otherwise RES1 */ | \
					 (UL(1) << 11)	/* TODO: ARMv8.5-CSEH, otherwise RES1 */)

#define SCTLR_ELx_M_BIT			(UL(1) << 0)
#define SCTLR_ELx_A_BIT			(UL(1) << 1)
#define SCTLR_ELx_C_BIT			(UL(1) << 2)
#define SCTLR_ELx_SA_BIT		(UL(1) << 3)
#define SCTLR_ELx_SA0_BIT		(UL(1) << 4)
#define SCTLR_ELx_CP15BEN_BIT		(UL(1) << 5)
#define SCTLR_ELx_nAA_BIT		(UL(1) << 6)
#define SCTLR_ELx_SED_BIT		(UL(1) << 8)
#define SCTLR_ELx_EOS_BIT		(UL(1) << 11)
#define SCTLR_ELx_I_BIT			(UL(1) << 12)
#define SCTLR_ELx_DZE_BIT		(UL(1) << 14)
#define SCTLR_ELx_UCT_BIT		(UL(1) << 15)
#define SCTLR_ELx_nTWI_BIT		(UL(1) << 16)
#define SCTLR_ELx_nTWE_BIT		(UL(1) << 18)
#define SCTLR_ELx_WXN_BIT		(UL(1) << 19)
#define SCTLR_ELx_TSCXT_BIT		(UL(1) << 20)
#define SCTLR_ELx_EIS_BIT		(UL(1) << 22)
#define SCTLR_ELx_SPAN_BIT		(UL(1) << 23)
#define SCTLR_ELx_EE_BIT		(UL(1) << 25)
#define SCTLR_ELx_UCI_BIT		(UL(1) << 26)
#define SCTLR_ELx_nTLSMD_BIT		(UL(1) << 28)
#define SCTLR_ELx_LSMAOE_BIT		(UL(1) << 29)
#define SCTLR_ELx_EnIA_BIT		(UL(1) << 31)
#define SCTLR_ELx_BT0_BIT		(UL(1) << 35)
#define SCTLR_ELx_BT1_BIT		(UL(1) << 36)
#define SCTLR_ELx_DSSBS_BIT		(UL(1) << 44)
#define SCTLR_ELx_SPINTMASK_BIT		(UL(1) << 62)

#define SCTLR_EL1_FLAGS (SCTLR_ELx_SPAN_BIT | SCTLR_ELx_EIS_BIT | SCTLR_ELx_nTWE_BIT | \
			 SCTLR_ELx_nTWI_BIT | SCTLR_ELx_EOS_BIT | SCTLR_ELx_nAA_BIT | \
			 SCTLR_ELx_CP15BEN_BIT | SCTLR_ELx_SA0_BIT | SCTLR_ELx_SA_BIT)

#define SCTLR_EL2_BITS		(SCTLR_ELx_C_BIT	/* Data accesses are cacheable
							 * as per translation tables */ | \
							/* SCTLR_EL2_M = 0 (MMU disabled) */  \
							/* SCTLR_EL2_A = 0
							 * (No alignment checks) */  \
				 SCTLR_ELx_SA_BIT	/* SP aligned at EL2 */ | \
				 SCTLR_ELx_SA0_BIT	/* SP Alignment check enable for EL0 */ \
							/* SCTLR_EL2_CP15BEN = 0 (EL0 using AArch32:
							 * EL0 execution of the CP15DMB, CP15DSB,
							 * and CP15ISB instructions is
							 * UNDEFINED. */ \
							/* SCTLR_EL2_NAA = 0 (unaligned MA fault
							 * at EL2 and EL0) */ \
							/* SCTLR_EL2_ITD = 0 (A32 Only) */ | \
				 SCTLR_ELx_SED_BIT	/* A32 Only, RES1 for non-A32 systems */ \
							/* SCTLR_EL2_EOS TODO: ARMv8.5-CSEH,
							 * otherwise RES1 */ | \
				 SCTLR_ELx_I_BIT	/* I$ is ON for EL2 and EL0 */ | \
				 SCTLR_ELx_DZE_BIT	/* Do not trap DC ZVA */ | \
				 SCTLR_ELx_UCT_BIT	/* Allow EL0 access to CTR_EL0 */ | \
				 SCTLR_ELx_nTWI_BIT	/* Don't trap WFI from EL0 to EL2 */ | \
				 SCTLR_ELx_nTWE_BIT	/* Don't trap WFE from EL0 to EL2 */ | \
				 SCTLR_ELx_WXN_BIT	/* W implies XN */ | \
				 SCTLR_ELx_TSCXT_BIT	/* Trap EL0 accesss to SCXTNUM_EL0 */ | \
							/* SCTLR_EL2_EIS EL2 exception is context
							 * synchronizing
							 */ \
				 SCTLR_ELx_RES1_BIT	| \
							/* SCTLR_EL2_SPAN = 0 (Set PSTATE.PAN = 1 on
							 * exceptions to EL2)) */ \
				 SCTLR_ELx_UCI_BIT	/* Allow cache maintenance
							 * instructions at EL0 */ | \
				 SCTLR_ELx_nTLSMD_BIT	/* A32/T32 only */ | \
				 SCTLR_ELx_LSMAOE_BIT	/* A32/T32 only */)

#ifdef RMM_FPU_USE_AT_REL2
#define SCTLR_EL2_INIT		SCTLR_EL2_BITS
#else
#define SCTLR_EL2_INIT		(SCTLR_EL2_BITS		| \
				 SCTLR_ELx_A_BIT	/* Alignment fault check enable */)
#endif

#define SCTLR_EL2_RUNTIME	(SCTLR_EL2_INIT		| \
				 SCTLR_ELx_M_BIT	/* MMU enabled */)

/* SCTLR2_ELx Register definitions */
#define SCTLR2_ELx_NMEA_BIT		(UL(1) << 2)
#define SCTLR2_ELx_EnADERR_BIT		(UL(1) << 3)
#define SCTLR2_ELx_EnANERR_BIT		(UL(1) << 4)
#define SCTLR2_ELx_EASE_BIT		(UL(1) << 5)
#define SCTLR2_ELx_EnIDCP128_BIT	(UL(1) << 6)

/* RMM sets HCR_EL2.E2H to 1. CPTR_EL2 definitions when HCR_EL2.E2H == 1 */
#define CPTR_EL2_VHE_TTA		(UL(1) << 28)
#define CPTR_EL2_VHE_TAM		(UL(1) << 30)

#define CPTR_EL2_VHE_FPEN_SHIFT		UL(20)
#define CPTR_EL2_VHE_FPEN_WIDTH		UL(2)
#define CPTR_EL2_VHE_FPEN_TRAP_ALL_00	UL(0)
#define CPTR_EL2_VHE_FPEN_TRAP_TGE_01	UL(1)
#define CPTR_EL2_VHE_FPEN_TRAP_ALL_10	UL(2)
#define CPTR_EL2_VHE_FPEN_NO_TRAP_11	UL(3)

#define CPTR_EL2_VHE_ZEN_SHIFT		UL(16)
#define CPTR_EL2_VHE_ZEN_WIDTH		UL(2)
#define CPTR_EL2_VHE_ZEN_TRAP_ALL_00	UL(0x0)
#define CPTR_EL2_VHE_ZEN_NO_TRAP_11	UL(0x3)

#define CPTR_EL2_VHE_SMEN_SHIFT		UL(24)
#define CPTR_EL2_VHE_SMEN_WIDTH		UL(2)
#define CPTR_EL2_VHE_SMEN_TRAP_ALL_00	UL(0x0)
#define CPTR_EL2_VHE_SMEN_NO_TRAP_11	UL(0x3)

#define CPTR_EL2_VHE_SIMD_MASK		(MASK(CPTR_EL2_VHE_FPEN) |	\
					 MASK(CPTR_EL2_VHE_ZEN) |	\
					 MASK(CPTR_EL2_VHE_SMEN))

/* Trap all AMU, trace, FPU, SVE, SME accesses */
#define CPTR_EL2_VHE_INIT		((CPTR_EL2_VHE_ZEN_TRAP_ALL_00 << \
					  CPTR_EL2_VHE_ZEN_SHIFT)	| \
					 (CPTR_EL2_VHE_SMEN_TRAP_ALL_00 << \
					  CPTR_EL2_VHE_SMEN_SHIFT)	| \
					 (CPTR_EL2_VHE_FPEN_TRAP_ALL_00 << \
					  CPTR_EL2_VHE_FPEN_SHIFT)	| \
					 CPTR_EL2_VHE_TTA		| \
					 CPTR_EL2_VHE_TAM)

/* MDCR_EL2 definitions */
#define MDCR_EL2_HPMFZS		(UL(1) << 36)
#define MDCR_EL2_HPMFZO		(UL(1) << 29)
#define MDCR_EL2_MTPME		(UL(1) << 28)
#define MDCR_EL2_TDCC		(UL(1) << 27)
#define MDCR_EL2_HLP		(UL(1) << 26)
#define MDCR_EL2_HCCD		(UL(1) << 23)
#define MDCR_EL2_TTRF		(UL(1) << 19)
#define MDCR_EL2_HPMD		(UL(1) << 17)
#define MDCR_EL2_TPMS		(UL(1) << 14)
#define MDCR_EL2_E2PB(x)	((x) << 12)
#define MDCR_EL2_E2PB_EL1	UL(3)
#define MDCR_EL2_TDRA_BIT	(UL(1) << 11)
#define MDCR_EL2_TDOSA_BIT	(UL(1) << 10)
#define MDCR_EL2_TDA_BIT	(UL(1) << 9)
#define MDCR_EL2_TDE_BIT	(UL(1) << 8)
#define MDCR_EL2_HPME_BIT	(UL(1) << 7)
#define MDCR_EL2_TPM_BIT	(UL(1) << 6)
#define MDCR_EL2_TPMCR_BIT	(UL(1) << 5)

#define MDCR_EL2_HPMN_SHIFT	UL(0)
#define MDCR_EL2_HPMN_WIDTH	UL(5)

#define MDCR_EL2_INIT		(MDCR_EL2_MTPME		| \
				 MDCR_EL2_HCCD		| \
				 MDCR_EL2_HPMD		| \
				 MDCR_EL2_TDA_BIT	| \
				 MDCR_EL2_TPM_BIT	| \
				 MDCR_EL2_TPMCR_BIT)

/* Armv8.3 Pointer Authentication Registers */
#define APIAKeyLo_EL1		S3_0_C2_C1_0
#define APIAKeyHi_EL1		S3_0_C2_C1_1
#define APIBKeyLo_EL1		S3_0_C2_C1_2
#define APIBKeyHi_EL1		S3_0_C2_C1_3
#define APDAKeyLo_EL1		S3_0_C2_C2_0
#define APDAKeyHi_EL1		S3_0_C2_C2_1
#define APDBKeyLo_EL1		S3_0_C2_C2_2
#define APDBKeyHi_EL1		S3_0_C2_C2_3
#define APGAKeyLo_EL1		S3_0_C2_C3_0
#define APGAKeyHi_EL1		S3_0_C2_C3_1

/*
 * MPIDR_EL1 definitions
 * 'MPIDR_EL1_AFF<n>_VAL_SHIFT' constants specify the right shift
 * for affinity field <n> that gives the field's actual value.
 */

/* Aff0[3:0] - Affinity level 0
 * For compatibility with GICv3 only Aff0[3:0] field is used,
 * and Aff0[7:4] of MPIDR_EL1 value is RES0 to match RmiRecMpidr.
 */
#define MPIDR_EL1_AFF0_SHIFT		U(0)
#define MPIDR_EL1_AFF0_WIDTH		U(4)
#define MPIDR_EL1_AFF0_VAL_SHIFT	U(0)

/* Aff1[15:8] - Affinity level 1 */
#define MPIDR_EL1_AFF1_SHIFT		U(8)
#define MPIDR_EL1_AFF1_WIDTH		U(8)
#define MPIDR_EL1_AFF1_VAL_SHIFT	U(4)

/* Aff2[23:16] - Affinity level 2 */
#define MPIDR_EL1_AFF2_SHIFT		U(16)
#define MPIDR_EL1_AFF2_WIDTH		U(8)
#define MPIDR_EL1_AFF2_VAL_SHIFT	U(4)

/* Aff3[39:32] - Affinity level 3 */
#define MPIDR_EL1_AFF3_SHIFT		U(32)
#define MPIDR_EL1_AFF3_WIDTH		U(8)
#define MPIDR_EL1_AFF3_VAL_SHIFT	U(12)

/*
 * Extract the value of MPIDR_EL1.Aff<n> register field shifted right
 * so it can be evaluated directly.
 */
#define MPIDR_EL1_AFF(n, reg)	\
	(((reg) & MASK(MPIDR_EL1_AFF##n)) >> MPIDR_EL1_AFF##n##_VAL_SHIFT)

/*
 * RmiRecMpidr type definitions.
 *
 * 'RMI_MPIDR_AFF<n>_VAL_SHIFT' constants specify the right shift
 * for affinity field <n> that gives the field's actual value.
 *
 * Aff0[3:0] - Affinity level 0
 * For compatibility with GICv3 only Aff0[3:0] field is used,
 * and Aff0[7:4] of a REC MPIDR value is RES0.
 */
#define RMI_MPIDR_AFF0_SHIFT		U(0)
#define RMI_MPIDR_AFF0_WIDTH		U(4)
#define RMI_MPIDR_AFF0_VAL_SHIFT	U(0)

/* Aff1[15:8] - Affinity level 1 */
#define RMI_MPIDR_AFF1_SHIFT		U(8)
#define RMI_MPIDR_AFF1_WIDTH		U(8)
#define RMI_MPIDR_AFF1_VAL_SHIFT	U(4)

/* Aff2[23:16] - Affinity level 2 */
#define RMI_MPIDR_AFF2_SHIFT		U(16)
#define RMI_MPIDR_AFF2_WIDTH		U(8)
#define RMI_MPIDR_AFF2_VAL_SHIFT	U(4)

/* Aff3[31:24] - Affinity level 3 */
#define RMI_MPIDR_AFF3_SHIFT		U(24)
#define RMI_MPIDR_AFF3_WIDTH		U(8)
#define RMI_MPIDR_AFF3_VAL_SHIFT	U(4)

/*
 * Extract the value of RmiRecMpidr.Aff<n> field shifted right
 * so it can be evaluated directly.
 */
#define RMI_MPIDR_AFF(n, val)	\
	(((val) & MASK(RMI_MPIDR_AFF##n)) >> RMI_MPIDR_AFF##n##_VAL_SHIFT)

/* VMPIDR bit [31] = RES1 */
#define VMPIDR_EL2_RES1		(UL(1) << 31)

/* ICC_SRE_EL2 defintions */
#define ICC_SRE_EL2_ENABLE	(UL(1) << 3)	/* Enable lower EL access to ICC_SRE_EL1 */
#define ICC_SRE_EL2_DIB		(UL(1) << 2)	/* Disable IRQ bypass   */
#define ICC_SRE_EL2_DFB		(UL(1) << 1)	/* Disable FIQ bypass   */
#define ICC_SRE_EL2_SRE		(UL(1) << 0)	/* Enable sysreg access */

#define ICC_SRE_EL2_INIT	(ICC_SRE_EL2_ENABLE | ICC_SRE_EL2_DIB | \
				 ICC_SRE_EL2_DFB | ICC_SRE_EL2_SRE)

#define PMSCR_EL2_INIT		0x0

#define SYSREG_TRAP_OPCODE(op0, op1, crn, crm, op2) \
		((UL(op0) << ESR_EL2_SYSREG_TRAP_OP0_SHIFT) | \
		 (UL(op1) << ESR_EL2_SYSREG_TRAP_OP1_SHIFT) | \
		 (UL(crn) << ESR_EL2_SYSREG_TRAP_CRN_SHIFT) | \
		 (UL(crm) << ESR_EL2_SYSREG_TRAP_CRM_SHIFT) | \
		 (UL(op2) << ESR_EL2_SYSREG_TRAP_OP2_SHIFT))

#define ESR_EL2_SYSREG_MASK		SYSREG_TRAP_OPCODE(3, 7, 15, 15, 7)

/* @TODO: Review this mask */
#define ESR_EL2_SYSREG_ID_MASK		SYSREG_TRAP_OPCODE(3, 7, 15, 0, 0)
#define ESR_EL2_SYSREG_ID		SYSREG_TRAP_OPCODE(3, 0, 0, 0, 0)

#define ESR_EL2_SYSREG_ID_AA64PFR0_EL1	SYSREG_TRAP_OPCODE(3, 0, 0, 4, 0)
#define ESR_EL2_SYSREG_ID_AA64PFR1_EL1	SYSREG_TRAP_OPCODE(3, 0, 0, 4, 1)
#define ESR_EL2_SYSREG_ID_AA64PFR2_EL1	SYSREG_TRAP_OPCODE(3, 0, 0, 4, 2)
#define ESR_EL2_SYSREG_ID_AA64ZFR0_EL1	SYSREG_TRAP_OPCODE(3, 0, 0, 4, 4)
#define ESR_EL2_SYSREG_ID_AA64SMFR0_EL1	SYSREG_TRAP_OPCODE(3, 0, 0, 4, 5)
#define ESR_EL2_SYSREG_ID_AA64FPFR0_EL1	SYSREG_TRAP_OPCODE(3, 0, 0, 4, 7)

#define ESR_EL2_SYSREG_ID_AA64DFR0_EL1	SYSREG_TRAP_OPCODE(3, 0, 0, 5, 0)
#define ESR_EL2_SYSREG_ID_AA64DFR1_EL1	SYSREG_TRAP_OPCODE(3, 0, 0, 5, 1)
#define ESR_EL2_SYSREG_ID_AA64DFR2_EL1	SYSREG_TRAP_OPCODE(3, 0, 0, 5, 2)

#define ESR_EL2_SYSREG_ID_AA64AFR0_EL1	SYSREG_TRAP_OPCODE(3, 0, 0, 5, 4)
#define ESR_EL2_SYSREG_ID_AA64AFR1_EL1	SYSREG_TRAP_OPCODE(3, 0, 0, 5, 5)

#define ESR_EL2_SYSREG_ID_AA64ISAR0_EL1	SYSREG_TRAP_OPCODE(3, 0, 0, 6, 0)
#define ESR_EL2_SYSREG_ID_AA64ISAR1_EL1	SYSREG_TRAP_OPCODE(3, 0, 0, 6, 1)
#define ESR_EL2_SYSREG_ID_AA64ISAR2_EL1	SYSREG_TRAP_OPCODE(3, 0, 0, 6, 2)
#define ESR_EL2_SYSREG_ID_AA64ISAR3_EL1	SYSREG_TRAP_OPCODE(3, 0, 0, 6, 3)

#define ESR_EL2_SYSREG_ID_AA64MMFR0_EL1	SYSREG_TRAP_OPCODE(3, 0, 0, 7, 0)
#define ESR_EL2_SYSREG_ID_AA64MMFR1_EL1	SYSREG_TRAP_OPCODE(3, 0, 0, 7, 1)
#define ESR_EL2_SYSREG_ID_AA64MMFR2_EL1	SYSREG_TRAP_OPCODE(3, 0, 0, 7, 2)
#define ESR_EL2_SYSREG_ID_AA64MMFR3_EL1	SYSREG_TRAP_OPCODE(3, 0, 0, 7, 3)
#define ESR_EL2_SYSREG_ID_AA64MMFR4_EL1	SYSREG_TRAP_OPCODE(3, 0, 0, 7, 4)

#define ESR_EL2_SYSREG_S2POR_EL1	SYSREG_TRAP_OPCODE(3, 0, 10, 2, 5)

/*
 * FEAT_MPAM system registers encoding mask for registers
 * MPAM0_EL1: (3, 0, 10, 5, 1)
 * MPAM1_EL1: (3, 0, 10, 5, 0)
 * MPAMSM_EL1: (3, 0, 10, 5, 3)
 * MPAMIDR_EL1: (3, 0, 10, 4, 4)
 */
#define ESR_EL2_SYSREG_MPAM_MASK		SYSREG_TRAP_OPCODE(3, 7, 15, 14, 0)
#define ESR_EL2_SYSREG_MPAM			SYSREG_TRAP_OPCODE(3, 0, 10, 4, 0)

/* ID_AA64ISAR1_EL1 definitions */
#define ID_AA64ISAR1_EL1_GPI_SHIFT	UL(28)
#define ID_AA64ISAR1_EL1_GPI_WIDTH	UL(4)

#define ID_AA64ISAR1_EL1_GPA_SHIFT	UL(24)
#define ID_AA64ISAR1_EL1_GPA_WIDTH	UL(4)

#define ID_AA64ISAR1_EL1_API_SHIFT	UL(8)
#define ID_AA64ISAR1_EL1_API_WIDTH	UL(4)

#define ID_AA64ISAR1_EL1_APA_SHIFT	UL(4)
#define ID_AA64ISAR1_EL1_APA_WIDTH	UL(4)

#define ESR_EL2_SYSREG_TIMERS_MASK		SYSREG_TRAP_OPCODE(3, 3, 15, 12, 0)
#define ESR_EL2_SYSREG_TIMERS			SYSREG_TRAP_OPCODE(3, 3, 14, 0, 0)

#define ESR_EL2_SYSREG_TIMER_CNTP_TVAL_EL0	SYSREG_TRAP_OPCODE(3, 3, 14, 2, 0)
#define ESR_EL2_SYSREG_TIMER_CNTP_CTL_EL0	SYSREG_TRAP_OPCODE(3, 3, 14, 2, 1)
#define ESR_EL2_SYSREG_TIMER_CNTP_CVAL_EL0	SYSREG_TRAP_OPCODE(3, 3, 14, 2, 2)
#define ESR_EL2_SYSREG_TIMER_CNTV_TVAL_EL0	SYSREG_TRAP_OPCODE(3, 3, 14, 3, 0)
#define ESR_EL2_SYSREG_TIMER_CNTV_CTL_EL0	SYSREG_TRAP_OPCODE(3, 3, 14, 3, 1)
#define ESR_EL2_SYSREG_TIMER_CNTV_CVAL_EL0	SYSREG_TRAP_OPCODE(3, 3, 14, 3, 2)

#define ESR_EL2_SYSREG_ICC_PMR_EL1		SYSREG_TRAP_OPCODE(3, 0, 4, 6, 0)

/*
 * GIC system registers encoding mask for registers from
 * ICC_IAR0_EL1(3, 0, 12, 8, 0) to ICC_IGRPEN1_EL1(3, 0, 12, 12, 7).
 */
#define ESR_EL2_SYSREG_ICC_EL1_MASK		SYSREG_TRAP_OPCODE(3, 3, 15, 8, 0)
#define ESR_EL2_SYSREG_ICC_EL1			SYSREG_TRAP_OPCODE(3, 0, 12, 8, 0)

#define ESR_EL2_SYSREG_ICC_DIR			SYSREG_TRAP_OPCODE(3, 0, 12, 11, 1)
#define ESR_EL2_SYSREG_ICC_SGI1R_EL1		SYSREG_TRAP_OPCODE(3, 0, 12, 11, 5)
#define ESR_EL2_SYSREG_ICC_SGI0R_EL1		SYSREG_TRAP_OPCODE(3, 0, 12, 11, 7)

#define ESR_EL2_SYSREG_DIRECTION	(UL(1) << 0)
#define ESR_EL2_SYSREG_IS_WRITE(esr)	(((esr) & ESR_EL2_SYSREG_DIRECTION) == 0UL)

/*
 * FEAT_BRBE system registers encoding mask for registers from
 * BRBINF<n>_EL1(2, 1, 8, 0, 0) to BRBTGTINJ_EL1(2, 1, 9, 1, 2).
 */
#define ESR_EL2_SYSREG_BRBE			SYSREG_TRAP_OPCODE(2, 1, 8, 0, 0)
#define ESR_EL2_SYSREG_BRBE_MASK		SYSREG_TRAP_OPCODE(2, 7, 14, 0, 0)

#define ESR_IL(esr)			((esr) & MASK(ESR_EL2_IL))

#define ESR_EL2_SYSREG_ISS_RT(esr)	EXTRACT(ESR_EL2_SYSREG_TRAP_RT, esr)

#define ICC_HPPIR1_EL1_INTID_SHIFT	UL(0)
#define ICC_HPPIR1_EL1_INTID_WIDTH	UL(24)

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

#define TLBI_ADDR_SHIFT		U(12)
#define TLBI_ADDR_MASK		UL(0x0FFFFFFFFFFF)
#define TLBI_ADDR(x)		(((x) >> TLBI_ADDR_SHIFT) & TLBI_ADDR_MASK)

/* Custom defined values to indicate the vector offset to exception handlers */
#define ARM_EXCEPTION_SYNC_LEL		0
#define ARM_EXCEPTION_IRQ_LEL		1
#define ARM_EXCEPTION_FIQ_LEL		2
#define ARM_EXCEPTION_SERROR_LEL	3

#define VBAR_CEL_SP_EL0_OFFSET		0x0
#define VBAR_CEL_SP_ELx_OFFSET		0x200
#define VBAR_LEL_AA64_OFFSET		0x400
#define VBAR_LEL_AA32_OFFSET		0x600

/* SError vector offset from Sync exception vector */
#define VBAR_SERROR_OFFSET		UL(0x180)

/* Stack Pointer selection */
#define MODE_SP_EL0			UL(0)
#define MODE_SP_ELX			UL(1)

/*******************************************************************************
 * FEAT_GCS - Guarded Control Stack Registers
 ******************************************************************************/
#define ID_GCSCR_EL12			S3_5_C2_C5_0
#define GCSCR_EXLOCK_EN_BIT		(UL(1) << 6)

/*******************************************************************************
 * Define macros to generate system register IDs to use with msr/mrs
 ******************************************************************************/
#define EL2_SYSREG_ACCESS_RT_SHIFT	UL(0)
#define EL2_SYSREG_ACCESS_RT_WIDTH	UL(5)

#define EL2_SYSREG_ACCESS_OP2_SHIFT	UL(5)
#define EL2_SYSREG_ACCESS_OP2_WIDTH	UL(3)

#define EL2_SYSREG_ACCESS_CRM_SHIFT	UL(8)
#define EL2_SYSREG_ACCESS_CRM_WIDTH	UL(4)

#define EL2_SYSREG_ACCESS_CRN_SHIFT	UL(12)
#define EL2_SYSREG_ACCESS_CRN_WIDTH	UL(4)

#define EL2_SYSREG_ACCESS_OP1_SHIFT	UL(16)
#define EL2_SYSREG_ACCESS_OP1_WIDTH	UL(3)

#define EL2_SYSREG_ACCESS_OP0_SHIFT	UL(19)
#define EL2_SYSREG_ACCESS_OP0_WIDTH	UL(2)

#endif /* ARCH_H */
