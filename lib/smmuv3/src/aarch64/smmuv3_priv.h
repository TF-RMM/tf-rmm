/*
 * SPDX-License-Identifier: BSD-3-Clause
 * Copyright 2021 The Hafnium Authors.
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors
 * SPDX-FileCopyrightText: Copyright (c) 2025 NVIDIA CORPORATION & AFFILIATES. All rights reserved.
 */

#ifndef SMMUV3_PRIV_H
#define SMMUV3_PRIV_H

#include <spinlock.h>
#include <utils_def.h>

typedef __uint128_t	uint128_t;

/* Registers in Page 0 */
#define SMMU_IDR0		U(0x00)
#define SMMU_IDR1		U(0x04)
#define SMMU_IDR2		U(0x08)
#define SMMU_IDR3		U(0x0C)
#define SMMU_IDR4		U(0x10)
#define SMMU_IDR5		U(0x14)
#define SMMU_IIDR		U(0x18)
#define SMMU_AIDR		U(0x1C)
#define SMMU_CR0		U(0x20)
#define SMMU_CR0_ACK		U(0x24)
#define SMMU_CR1		U(0x28)
#define SMMU_CR2		U(0x2C)

/* Registers in Realm Page 0 */
#define SMMU_R_IDR0		U(0x000)
#define SMMU_R_IDR1		U(0x004)
#define SMMU_R_IDR2		U(0x008)
#define SMMU_R_IDR3		U(0x00C)
#define SMMU_R_IDR4		U(0x010)
#define SMMU_R_AIDR		U(0x01C)
#define SMMU_R_CR0		U(0x020)
#define SMMU_R_CR0ACK		U(0x024)
#define SMMU_R_CR1		U(0x028)
#define SMMU_R_CR2		U(0x02C)
#define SMMU_R_GBPA		U(0x044)
#define SMMU_R_AGBPA		U(0x048)
#define SMMU_R_IRQ_CTRL		U(0x050)
#define SMMU_R_IRQ_CTRLACK	U(0x054)
#define SMMU_R_GERROR		U(0x060)
#define SMMU_R_GERRORN		U(0x064)
#define SMMU_R_GERROR_IRQ_CFG0	U(0x068)
#define SMMU_R_GERROR_IRQ_CFG1	U(0x070)
#define SMMU_R_GERROR_IRQ_CFG2	U(0x074)
#define SMMU_R_STRTAB_BASE	U(0x080)
#define SMMU_R_STRTAB_BASE_CFG	U(0x088)
#define SMMU_R_CMDQ_BASE	U(0x090)
#define SMMU_R_CMDQ_PROD	U(0x098)
#define SMMU_R_CMDQ_CONS	U(0x09C)
#define SMMU_R_EVENTQ_BASE	U(0x0A0)
#define SMMU_R_EVENTQ_IRQ_CFG0	U(0x0B0)
#define SMMU_R_EVENTQ_IRQ_CFG1	U(0x0B8)
#define SMMU_R_EVENTQ_IRQ_CFG2	U(0x0BC)
#define SMMU_R_PRIQ_BASE	U(0x0C0)
#define SMMU_R_PRIQ_IRQ_CFG0	U(0x0D0)
#define SMMU_R_PRIQ_IRQ_CFG1	U(0x0D8)
#define SMMU_R_PRIQ_IRQ_CFG2	U(0x0DC)
#define SMMU_R_MPAMIDR		U(0x130)
#define SMMU_R_GMPAM		U(0x138)

#define SMMU_R_IDR6		U(0x190)
#define SMMU_R_DPT_BASE		U(0x200)
#define SMMU_R_DPT_BASE_CFG	U(0x208)
#define SMMU_R_DPT_CFG_FAR	U(0x210)
#define SMMU_R_MECIDR		U(0x220)
#define SMMU_R_GMECID		U(0x228)

/* Registers in Realm Page 1 */
#define SMMU_R_PAGE_1_OFFSET	U(0x10000)

#define SMMU_R_EVENTQ_PROD	(SMMU_R_PAGE_1_OFFSET + U(0xA8))
#define SMMU_R_EVENTQ_CONS	(SMMU_R_PAGE_1_OFFSET + U(0xAC))
#define SMMU_R_PRIQ_PROD	(SMMU_R_PAGE_1_OFFSET + U(0xC8))
#define SMMU_R_PRIQ_CONS	(SMMU_R_PAGE_1_OFFSET + U(0xCC))

/* SMMU_IDR0 register fields and features */
#define IDR0_S2P_BIT		BIT32(0)
#define IDR0_S1P_BIT		BIT32(1)
#define IDR0_TTF_SHIFT		U(2)
#define IDR0_TTF_WIDTH		U(2)
#define IDR0_BTM_BIT		BIT32(5)
#define IDR0_ASID16_BIT		BIT32(12)
#define IDR0_VMW_BIT		BIT32(17)
#define IDR0_VMID16_BIT		BIT32(18)
#define IDR0_TTENDIAN_SHIFT	U(21)
#define IDR0_TTENDIAN_WIDTH	U(2)
#define IDR0_ST_LEVEL_SHIFT	U(27)
#define IDR0_ST_LEVEL_WIDTH	U(2)

#define AARCH32_TTF		U(1)
#define AARCH64_TTF		U(2)
#define AARCH32_64_TTF		U(3)

/* IR0 features bitmap */
#define FEAT_2_LVL_STRTAB	BIT32(0)
#define FEAT_BTM		BIT32(1)
#define FEAT_COHACC		BIT32(2)
#define FEAT_S1P		BIT32(3)
#define FEAT_ASID16		BIT32(5)
#define FEAT_VMID16		BIT32(6)

/* SMMU_IDR1 register fields */
#define IDR1_SIDSIZE_SHIFT	U(0)
#define IDR1_SIDSIZE_WIDTH	U(6)
#define IDR1_SSIDSIZE_SHIFT	U(6)
#define IDR1_SSIDSIZE_WIDTH	U(5)
#define IDR1_PRIQS_SHIFT	U(11)
#define IDR1_PRIQS_WIDTH	U(5)
#define IDR1_EVTQS_SHIFT	U(16)
#define IDR1_EVTQS_WIDTH	U(5)
#define IDR1_CMDQS_SHIFT	U(21)
#define IDR1_CMDQS_WIDTH	U(5)
#define IDR1_QUEUES_PRESET_BIT	BIT32(29)
#define IDR1_TABLES_PRESET_BIT	BIT32(30)

/* SMMU_AIDR */
#define AIDR_ARCH_MINOR_REV_SHIFT	U(0)
#define AIDR_ARCH_MINOR_REV_WIDTH	U(4)
#define AIDR_ARCH_MAJOR_REV_SHIFT	U(4)
#define AIDR_ARCH_MAJOR_REV_WIDTH	U(4)

/* SMMU_R_IDR0 features */
#define R_IDR0_ATS_BIT		BIT32(10)
#define R_IDR0_MSI_BIT		BIT32(13)
#define R_IDR0_PRI_BIT		BIT32(16)

/* R_IDR0 realm_features bitmap */
#define FEAT_R_ATS		BIT32(0)
#define FEAT_R_MSI		BIT32(1)
#define FEAT_R_PRI		BIT32(2)

/* SMMU_R_IDR3 features */
#define R_IDR3_DPT_BIT		BIT32(15)
#define R_IDR3_MEC_BIT		BIT32(16)

/* R_IDR3 realm_features bitmap */
#define FEAT_R_MEC		BIT32(3)
#define FEAT_R_DPT		BIT32(4)

#define TTF_SHIFT		U(2)
#define TTF_WIDTH		U(2)

/* Log2 of maximum number of Command and Event queues entries */
#define QUEUE_SIZE_MAX		U(19)

/* Max bits of SubstreamID */
#define SSID_SIZE_MAX		U(20)

/* Max bits of StreamID */
#define SID_SIZE_MAX		U(32)

/* SMMU_R_GBPA register fields */
#define SMMU_R_GBPA_ABORT	BIT32(20)

/*
 * SMMU_R_CMDQ_BASE.RA, bit[62]
 * SMMU_R_EVENTQ_BASE.WA, bit[62]
 * SMMU_R_STRTAB_BASE.RA, bit[62]
 */
#define RAWA_BIT		BIT(62)

/* SMMU_R_CR0 register fields */
#define R_CR0_SMMUEN_BIT	BIT32(0)
#define R_CR0_PRIQEN_BIT	BIT32(1)
#define R_CR0_EVTQEN_BIT	BIT32(2)
#define R_CR0_CMDQEN_BIT	BIT32(3)
#define R_CR0_ATSCHK_BIT	BIT32(4)
#define R_CR0_VMW_SHIFT		U(6)
#define R_CR0_VMW_WIDTH		U(7)
#define R_CR0_DPT_WALK_EN_BIT	BIT32(10)

/* TLB invalidations match VMID tags exactly */
#define R_CR0_VMW_VMID		U(0)

/*
 * Realm state SMMU disabled.
 * Writes to the Realm state PRI queue are disabled.
 * Writes to the Realm state Event queue are disabled.
 * Processing of commands from the Realm state Command queue is disabled.
 * TLB invalidations match VMID tags exactly (SMMU_IDR0.VMW == 1),
 * otherwise reserved, RES0.
 * Realm DPT walks are disabled.
 */
#define SMMU_R_CR0_INIT		INPLACE32(R_CR0_VMW, R_CR0_VMW_VMID)

/* SMMU_R_CR0ACK register fields */
#define R_CR0ACK_SMMUEN_BIT	BIT32(0)
#define R_CR0ACK_EVTQEN_BIT	BIT32(2)
#define R_CR0ACK_CMDQEN_BIT	BIT32(3)

/* SMMU_R_CR1 attributes and fields */
#define R_CR1_QUEUE_IC_SHIFT	U(0)
#define R_CR1_QUEUE_OC_SHIFT	U(2)
#define R_CR1_QUEUE_SH_SHIFT	U(4)
#define R_CR1_TABLE_IC_SHIFT	U(6)
#define R_CR1_TABLE_OC_SHIFT	U(8)
#define R_CR1_TABLE_SH_SHIFT	U(10)

#define CR1_WBCACHE		U(1)
#define CR1_INSH		U(3)

/*
 * Realm state Table and Queue access:
 *	Inner Shareable,
 *	Outer Cacheability: Write-Back Cacheable
 *	Inner Cacheability: Write-Back Cacheable
 */
#define SMMU_R_CR1_INIT (			  \
	INPLACE32(R_CR1_QUEUE_IC, CR1_WBCACHE)	| \
	INPLACE32(R_CR1_QUEUE_OC, CR1_WBCACHE)	| \
	INPLACE32(R_CR1_QUEUE_SH, CR1_INSH)	| \
	INPLACE32(R_CR1_TABLE_IC, CR1_WBCACHE)	| \
	INPLACE32(R_CR1_TABLE_OC, CR1_WBCACHE)	| \
	INPLACE32(R_CR1_TABLE_SH, CR1_INSH))

/* SMMU_R_CR2 */
#define R_CR2_E2H_BIT		BIT32(0)
#define R_CR2_RECINVSID_BIT	BIT32(1)
#define R_CR2_PTM_BIT		BIT32(2)
#define R_CR2_REC_CFG_ATS_BIT	BIT32(3)

/*
 * EL2-E2H translation regime used, with ASID, macthing HCR_EL2.E2H.
 * C_BAD_STREAMID events are permitted to be recorded.
 * SMMU records only the base set of Events for Realm state ATS-related
 * and PRI requests.
 */
#define SMMU_R_CR2_INIT	(	\
	R_CR2_E2H_BIT	|	\
	R_CR2_RECINVSID_BIT)

#define CMD_RECORD_SIZE		16U
#define EVT_RECORD_SIZE		32U
#define STE_SIZE		64U

/* Command opcodes */
#define CMD_PREFETCH_CONFIG	UL(0x01)
#define CMD_CFGI_STE		UL(0x03)
#define CMD_CFGI_ALL		UL(0x04)
#define CMD_TLBI_EL2_ALL	UL(0x20)
#define CMD_TLBI_S12_VMALL	UL(0x28)
#define CMD_TLBI_S2_IPA		UL(0x2A)
#define CMD_TLBI_NSNH_ALL	UL(0x30)
#define CMD_SYNC		UL(0x46)

/* Bit fields related to command format */
#define CMD_SHIFT		U(0)
#define CMD_WIDTH		U(8)

/*
 * CMD_CFGI_ALL
 * CMD_CFGI_STE
 * CMD_PREFETCH_CONFIG
 */
#define SSEC_BIT		BIT(10)

/*
 * CMD_CFGI_ALL
 * CMD_PREFETCH_CONFIG
 */
#define SSV_BIT			BIT(11)

/*
 * CMD_PREFETCH_CONFIG
 * CMD_CFGI_STE
 */
#define SID_SHIFT		U(32)
#define SID_WIDTH		U(32)

/* CMD_CFGI_STE */
#define LEAF_BIT		BIT(0)

/* CMD_CFGI_ALL */
#define SID_ALL			UL(31)

/* CMD_SYNC */
#define SIG_NONE		U(0)
#define SIG_IRQ			U(1)
#define SIG_SEV			U(2)
#define CS_SHIFT		U(12)
#define CS_WIDTH		U(2)

/* CMD_TLBI_S2_IPA, CMD_TLBI_S12_VMALL */
#define VMID_SHIFT		U(32)
#define VMID_WIDTH		U(16)

/* CMD_TLBI_S2_IPA */
#define ADDRESS_SHIFT		U(12)

/* SMMU_CMDQ_CONS error codes and fields */
#define CMDQ_CONS_ERR_SHIFT	U(24)
#define CMDQ_CONS_ERR_WIDTH	U(7)
#define CERROR_NONE		U(0)
#define CERROR_ILL		U(1)
#define CERROR_ABT		U(2)
#define CERROR_ATC_INV_SYNC	U(3)

/* Global Error register fields */
#define SFM_ERR_MASK		(U(1) << 8)
#define CMDQ_ERR_BIT		BIT32(0)

/* SMMU_R_STRTAB_BASE_CFG */
#define STRTAB_BASE_CFG_LOG2SIZE_SHIFT	U(0)
#define STRTAB_BASE_CFG_SPLIT_SHIFT	U(6)
#define STRTAB_BASE_CFG_FMT_SHIFT	U(16)

/* SMMU_R_CMDQ_BASE, SMMU_R_EVENTQ_BASE */
#define SMMU_R_BASE_LOG2SIZE_SHIFT	U(0)

#define LINEAR_STR_TABLE		U(0)
#define TWO_LVL_STR_TABLE		U(1)

#define STRTAB_L1_DESC_SPAN_SHIFT	U(0)
#define STRTAB_L1_DESC_SPAN_WIDTH	U(5)
#define STRTAB_L1_DESC_L2PTR_SHIFT	U(6)
#define STRTAB_L1_DESC_L2PTR_WIDTH	U(50)

/* Stream Table Entry [63:0] */
#define STE0_V_BIT		BIT(0)
#define STE0_CONFIG_SHIFT	U(1)
#define STE0_CONFIG_WIDTH	U(3)
#define STE0_CONFIG_ABORT	U(0)
#define STE0_CONFIG_BYPASS	U(4)
#define STE0_CONFIG_S1		U(5)
#define STE0_CONFIG_S2		U(6)
#define STE0_CONFIG_S1_S2	U(7)

/* Stream Table Entry [127:64] */
#define STE1_SHCFG_SHIFT	U(44)
#define STE1_SHCFG_WIDTH	U(2)
#define STE1_SHCFG_NONSH	U(0)
#define STE1_SHCFG_INCOMING	U(1)
#define STE1_SHCFG_OSH		U(2)
#define STE1_SHCFG_ISH		U(3)

/* Stream Table Entry [191:128] */
#define STE2_S2VMID_SHIFT	U(0)
#define STE2_S2VMID_WIDTH	U(16)
#define STE2_VTCR_SHIFT		U(32)
#define STE2_VTCR_WIDTH		U(19)
#define STE2_S2AA64_BIT		BIT(51)
#define STE2_S2ENDI_BIT		BIT(52)
#define STE2_S2PTW_BIT		BIT(54)
#define STE2_S2R_BIT		BIT(58)

/* Stream Table Entry [255:192] */
#define STE3_S2TTB_SHIFT	U(4)

/* Command queue maximum size */
#define CMDQ_MAX_SIZE		((1UL << SMMU_MAX_LOG2_CMDQ_SIZE) * CMD_RECORD_SIZE)

/* Command queue alignment */
#if (CMDQ_MAX_SIZE > 32UL)
#define CMDQ_ALIGN		CMDQ_MAX_SIZE
#else
#define CMDQ_ALIGN		32UL
#endif

/* Event queue maximum size */
#define EVTQ_MAX_SIZE		((1UL << SMMU_MAX_LOG2_EVTQ_SIZE) * EVT_RECORD_SIZE)

/* Event queue alignment */
#if (EVTQ_MAX_SIZE > 32U)
#define EVTQ_ALIGN		EVTQ_MAX_SIZE
#else
#define EVTQ_ALIGN		32UL
#endif

/* Maximum number of L1 descriptors */
#define STRTAB_L1_DESC_MAX	(1UL << (SMMU_MAX_SID_BITS - SMMU_STRTAB_SPLIT))

/* L1 Stream Table Descriptor size */
#define STRTAB_L1_DESC_SIZE	8U

/* L1 Stream Table size */
#define STRTAB_L1_MAX_SIZE	(STRTAB_L1_DESC_MAX * STRTAB_L1_DESC_SIZE)

/* L1 Stream Table alignment */
#if (STRTAB_L1_MAX_SIZE > 64UL)
#define STRTAB_L1_ALIGN		STRTAB_L1_MAX_SIZE
#else
#define STRTAB_L1_ALIGN		64UL
#endif

/* Maximum number of STEs per L1STD descriptor */
#define STRTAB_L1_STE_MAX	(UL(1) << SMMU_STRTAB_SPLIT)

/* L2 Stream table size */
#define STRTAB_L2_SIZE		(STRTAB_L1_STE_MAX * STE_SIZE)

#define SID_BITMAP_MAX_SIZE	((U(1) << SMMU_MAX_SID_BITS) / BITS_PER_UL)

#define MAX_RETRIES		100000U

enum queue_type {
	CMDQ,
	EVTQ,
	PRIQ
};

struct smmu_info;

/* STE is a 64-byte structure */
struct ste_entry {
	uint64_t ste[8];
};

COMPILER_ASSERT(sizeof(struct ste_entry) == STE_SIZE);

/* L2 Stream Table */
struct l2tab {
	/*
	 * NOTE: As per the specification L2 table must be
	 * aligned based on the strtab span configuration.
	 */
	struct ste_entry l2tab_entry[STRTAB_L1_STE_MAX];
} __aligned(STRTAB_L2_SIZE);

/* Array of L2 Stream Tables */
struct l2tabs {
	struct l2tab l2tabs_entry[STRTAB_L1_DESC_MAX];
};

struct arm_smmu_layout {
	/* Number of SMMUv3 */
	uint64_t num_smmus;
	/* Array of SMMUv3 Info structures */
	struct smmu_info arm_smmu_info[RMM_MAX_SMMUS];
};

struct smmu_config {
	unsigned int minor_rev;
	unsigned int features;
	unsigned int realm_features;
	unsigned int cmdq_log2size;
	unsigned int evtq_log2size;
	unsigned int substreamid_bits;
	unsigned int streamid_bits;
};

struct smmu_queue {
	void *q_base;
	uint32_t rd_idx, wr_idx;
	uint32_t q_entries;
	void *cons_reg;
	void *prod_reg;
};

struct smmuv3_driver {
	void *ns_base_addr;
	void *r_base_addr;

	struct smmu_config config;
	struct smmu_queue cmdq;
	struct smmu_queue evtq;

	uint64_t *strtab_base;
	struct l2tabs *l2strtab_base;

	/* Bitmap for keeping track of allocated SIDs */
	unsigned long sids[SID_BITMAP_MAX_SIZE];
	unsigned int num_l1_ents;

	/* TODO: statically allocate */
	void *l1std_l2ptr[STRTAB_L1_DESC_MAX];
	unsigned short l1std_cnt[STRTAB_L1_DESC_MAX];

	spinlock_t lock;
};

#endif /* SMMUV3_PRIV_H */
