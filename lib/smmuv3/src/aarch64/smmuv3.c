/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors
 */

#include <arch_features.h>
#include <assert.h>
#include <bitmap.h>
#include <errno.h>
#include <mmio.h>
#include <rmm_el3_ifc.h>
#include <smmuv3.h>
#include <smmuv3_priv.h>

/* Index to point L2 table */
#define L1_IDX(sid)	((sid) >> SMMU_STRTAB_SPLIT)

/* Index to point STE in Level 2 table */
#define L2_IDX(sid)	((sid) & ((U(1) << SMMU_STRTAB_SPLIT) - 1U))

static struct {
	uint8_t entry[CMDQ_MAX_SIZE] __aligned(CMDQ_ALIGN);
} cmd_queue[RMM_MAX_SMMUS];

static struct {
	uint8_t entry[EVTQ_MAX_SIZE] __aligned(EVTQ_ALIGN);
} evt_queue[RMM_MAX_SMMUS];

static struct {
	/* L1STD, Level 1 Stream Table Descriptor is a 8-byte structure */
	uint64_t entry[STRTAB_L1_DESC_MAX] __aligned(STRTAB_L1_ALIGN);
} strtab[RMM_MAX_SMMUS];

/* Array of L2 Stream Tables */
static struct l2tabs l2_strtab[RMM_MAX_SMMUS];

struct arm_smmu_layout arm_smmu;

struct smmuv3_driver arm_smmu_driver[RMM_MAX_SMMUS];

/* Indicates whether all SMMUs support broadcast TLB maintenance */
bool broadcast_tlb = true;

/* cppcheck-suppress misra-c2012-8.7 */
void setup_smmuv3_layout(struct smmu_list *plat_smmu_list)
{
	struct smmu_info *smmus_ptr;

	assert(plat_smmu_list != NULL);

	arm_smmu.num_smmus = plat_smmu_list->num_smmus;
	smmus_ptr = plat_smmu_list->smmus;

	for (uint64_t i = 0UL; i < plat_smmu_list->num_smmus; i++) {
		arm_smmu.arm_smmu_info[i] = *smmus_ptr++;
	}
}

static void write_strtab_l1std(uint64_t *l1std, void *l2ptr_pa)
{
	uint64_t val = COMPOSE(STRTAB_L1_DESC_SPAN, (SMMU_STRTAB_SPLIT + 1U)) |
			((uintptr_t)l2ptr_pa & MASK(STRTAB_L1_DESC_L2PTR));

	*l1std = val;
	dsb(ish);
}

/* Get address of STE */
static inline struct ste_entry *sid_to_ste(struct smmuv3_driver *smmu, unsigned int sid)
{
	return &smmu->l2strtab_base->l2tabs_entry[L1_IDX(sid)].l2tab_entry[L2_IDX(sid)];
}

static void configure_strtab(struct smmuv3_driver *smmu, void *strtab_base)
{
	uint32_t reg;
	uint64_t reg64;

	assert(ALIGNED(strtab_base, STRTAB_L1_ALIGN));

	reg  = INPLACE32(STRTAB_BASE_CFG_LOG2SIZE, smmu->config.streamid_bits);
	reg |= INPLACE32(STRTAB_BASE_CFG_SPLIT, SMMU_STRTAB_SPLIT);
	reg |= INPLACE32(STRTAB_BASE_CFG_FMT, TWO_LVL_STR_TABLE);
	write32(reg, (void *)((uintptr_t)smmu->r_base_addr + SMMU_R_STRTAB_BASE_CFG));

	reg64 = (uintptr_t)strtab_base | RAWA_BIT;
	write64(reg64, (void *)((uintptr_t)smmu->r_base_addr + SMMU_R_STRTAB_BASE));

	smmu->strtab_base = (uint64_t *)strtab_base;

	/* Number of L1 descriptors */
	smmu->num_l1_ents = U(1) << (smmu->config.streamid_bits - SMMU_STRTAB_SPLIT);

	SMMU_DEBUG("\t2-level Stream table @0x%lx\n",
					(uintptr_t)smmu->strtab_base);
	SMMU_DEBUG("\tStream ID bits %u\n", smmu->config.streamid_bits);
	SMMU_DEBUG("\tL1 entries %u\n", smmu->num_l1_ents);
}

static void configure_queue(struct smmuv3_driver *smmu, enum queue_type type,
			    void *queue_base)
{
	struct smmu_queue *queue;
	uint64_t base_reg;
	uint32_t base_offset, cons_offset, prod_offset;
	unsigned int log2size;

	if (type == CMDQ) {
		assert(ALIGNED(queue_base, CMDQ_ALIGN));

		queue = &smmu->cmdq;
		log2size = smmu->config.cmdq_log2size;
		base_offset = SMMU_R_CMDQ_BASE;
		cons_offset = SMMU_R_CMDQ_CONS;
		prod_offset = SMMU_R_CMDQ_PROD;
	} else {
		assert(ALIGNED(queue_base, EVTQ_ALIGN));

		queue = &smmu->evtq;
		log2size = smmu->config.evtq_log2size;
		base_offset = SMMU_R_EVENTQ_BASE;
		cons_offset = SMMU_R_EVENTQ_CONS;
		prod_offset = SMMU_R_EVENTQ_PROD;
	}

	queue->q_base = queue_base;

	base_reg = (uintptr_t)queue_base | RAWA_BIT;
	base_reg |= INPLACE(SMMU_R_BASE_LOG2SIZE, log2size);

	queue->cons_reg = (void *)((uintptr_t)smmu->r_base_addr + cons_offset);
	queue->prod_reg = (void *)((uintptr_t)smmu->r_base_addr + prod_offset);

	write64(base_reg, (void *)((uintptr_t)smmu->r_base_addr + base_offset));

	/* Queue RD/WR indexes = 0 */
	write32(0U, queue->cons_reg);
	write32(0U, queue->prod_reg);
}

static int init_config(struct smmuv3_driver *smmu)
{
	uint32_t idr1 = read32((void *)((uintptr_t)smmu->ns_base_addr + SMMU_IDR1));
	unsigned int log2size;

	if ((idr1 & (IDR1_QUEUES_PRESET_BIT | IDR1_TABLES_PRESET_BIT)) != 0U) {
		SMMU_ERROR(-ENOTSUP,
			"Driver doesn't support TABLES_PRESET and QUEUES_PRESET\n");
		return -ENOTSUP;
	}

	/* Command queue */
	/* cppcheck-suppress misra-c2012-12.2 */
	log2size = EXTRACT32(IDR1_CMDQS, idr1);
	assert(log2size <= QUEUE_SIZE_MAX);

	smmu->config.cmdq_log2size = MIN(log2size, SMMU_MAX_LOG2_CMDQ_SIZE);
	SMMU_DEBUG("\tCMDQ log2 size %u\n", smmu->config.cmdq_log2size);

	/* Event queue */
	/* cppcheck-suppress misra-c2012-12.2 */
	log2size = EXTRACT32(IDR1_EVTQS, idr1);
	assert(log2size <= QUEUE_SIZE_MAX);

	smmu->config.evtq_log2size = MIN(log2size, SMMU_MAX_LOG2_EVTQ_SIZE);
	SMMU_DEBUG("\tEVTQ log2 size %u\n", smmu->config.evtq_log2size);

	/* Max bits of SubstreamID */
	/* cppcheck-suppress misra-c2012-12.2 */
	log2size = EXTRACT32(IDR1_SSIDSIZE, idr1);
	assert(log2size <= SSID_SIZE_MAX);

	smmu->config.substreamid_bits = log2size;
	SMMU_DEBUG("\tSubstreamID max bits %u\n", log2size);

	/* Max bits of StreamID */
	/* cppcheck-suppress misra-c2012-12.2 */
	log2size = EXTRACT32(IDR1_SIDSIZE, idr1);
	assert(log2size <= SID_SIZE_MAX);

	smmu->config.streamid_bits = MIN(log2size, SMMU_MAX_SID_BITS);
	if (smmu->config.streamid_bits < SMMU_STRTAB_SPLIT) {
		SMMU_ERROR(-ENOTSUP, "StreamID max bits %u < SMMU_STRTAB_SPLIT %u\n",
				smmu->config.streamid_bits, SMMU_STRTAB_SPLIT);
		return -ENOTSUP;
	}

	return 0;
}

static int wait_for_ack(struct smmuv3_driver *smmu, uint32_t offset,
			uint32_t mask, uint32_t expected)
{
	unsigned int retries = 0U;

	while (retries++ < MAX_RETRIES) {
		uint32_t val = read32((void *)((uintptr_t)smmu->r_base_addr +
							offset));
		if ((val & mask) == (expected & mask)) {
			return 0;
		}
	}

	return -ETIMEDOUT;
}

static int check_cmdq_err(struct smmuv3_driver *smmu)
{
	uint32_t gerror_reg = read32((void *)((uintptr_t)smmu->r_base_addr +
							SMMU_R_GERROR));
	uint32_t gerror_n_reg = read32((void *)((uintptr_t)smmu->r_base_addr +
							SMMU_R_GERRORN));
	uint32_t cons_reg, err;

	if ((gerror_reg & CMDQ_ERR_BIT) == (gerror_n_reg & CMDQ_ERR_BIT)) {
		return 0;
	}

	SMMU_ERROR(-EIO, "Cannot process commands\n");
	SMMU_DEBUG("\tR_GERROR: %x; R_GERROR_N: %x\n", gerror_reg, gerror_n_reg);
	cons_reg = read32(smmu->cmdq.cons_reg);

	/* cppcheck-suppress misra-c2012-12.2 */
	err =  EXTRACT32(CMDQ_CONS_ERR, cons_reg);
	switch (err) {
	case CERROR_NONE:
		break;
	case CERROR_ILL:
		SMMU_DEBUG("\tCMDQ encountered error: CERROR_%s\n", "ILL");
		break;
	case CERROR_ABT:
		SMMU_DEBUG("\tCMDQ encountered error: CERROR_%s\n", "ABT");
		break;
	case CERROR_ATC_INV_SYNC:
		SMMU_DEBUG("\tCMDQ encountered error: CERROR_%s\n", "ATC_INV_SYNC");
		break;
	default:
		SMMU_DEBUG("\tCMDQ encountered error: UNKNOWN %u\n", err);
		break;
	}

	SMMU_DEBUG("\tAcknowledging error by toggling GERRORN.CMDQ_ERR\n");

	gerror_n_reg ^= CMDQ_ERR_BIT;
	write32(gerror_n_reg, (void *)((uintptr_t)smmu->r_base_addr + SMMU_R_GERRORN));

	return -EIO;
}

int wait_cmdq_empty(struct smmuv3_driver *smmu)
{
	uint32_t prod_reg, cons_reg;
	unsigned int retries = 0U;

	prod_reg = read32(smmu->cmdq.prod_reg);

	/* Wait until Command queue is empty */
	do {
		cons_reg = read32(smmu->cmdq.cons_reg);

		/*
		 * Arm System Memory Management Unit Architecture Specification
		 * SMMU architecture version 3.
		 * 3.5.1 SMMU circular queues.
		 * If the two indexes are equal and their wrap bits are equal,
		 * the queue is empty and nothing can be consumed from it.
		 */
		if (cons_reg == prod_reg) {
			return 0;
		}

	} while (++retries < MAX_RETRIES);

	SMMU_ERROR(-ETIMEDOUT, "Timeout processing commands CONS: 0x%x PROD: 0x%x\n",
			cons_reg, prod_reg);
	return -ETIMEDOUT;
}

static int send_cmd(struct smmuv3_driver *smmu, uint128_t cmd)
{
	uint32_t wrap_bit = U(1) << smmu->config.cmdq_log2size;
	uint32_t prod_reg = read32(smmu->cmdq.prod_reg);
	unsigned int retries = MAX_RETRIES;

	/* Wait until Command queue is not full */
	do {
		uint32_t cons_reg = read32(smmu->cmdq.cons_reg);

		/*
		 * Arm System Memory Management Unit Architecture Specification
		 * SMMU architecture version 3.
		 * 3.5.1 SMMU circular queues.
		 * If the two indexes are equal and their wrap bits are different,
		 * the queue is full and nothing can be produced to it.
		 */
		if ((cons_reg ^ prod_reg) != wrap_bit) {
			break;
		}
	} while (--retries != 0U);

	if (retries == 0U) {
		SMMU_ERROR(-ETIMEDOUT, "Command queue full\n");
		return -ETIMEDOUT;
	}

	/* Write command */
	/* coverity[misra_c_2012_rule_18_4_violation:SUPPRESS] */
	*((uint128_t *)smmu->cmdq.q_base + (prod_reg & (wrap_bit - 1U))) = cmd;
	dsb(ish);

	/*
	 * If current write index is already at the end, we need
	 * to wrap it around i.e, start from 0 and toggle wrap bit.
	 */
	prod_reg++;
	prod_reg &= ((wrap_bit << 1) - 1U);

	write32(prod_reg, smmu->cmdq.prod_reg);
	return 0;
}

int prepare_send_command(struct smmuv3_driver *smmu, unsigned long opcode,
			 unsigned long param0, unsigned long param1)
{
	uint128_t cmd = opcode;
	int ret;

	/* Check for errors */
	ret = check_cmdq_err(smmu);
	if (ret != 0) {
		return ret;
	}

	switch (opcode) {
	case CMD_PREFETCH_CONFIG:
		cmd |= (uint128_t)COMPOSE(SID, param0);
		break;
	case CMD_CFGI_STE:
		cmd |= (uint128_t)COMPOSE(SID, param0);
		cmd |= (uint128_t)param1 << 64;
		break;
	case CMD_CFGI_ALL:
		cmd |= (uint128_t)SID_ALL << 64;
		break;
	case CMD_SYNC:
		cmd |= (uint128_t)COMPOSE(CS, SIG_NONE);
		FALLTHROUGH;
	case CMD_TLBI_EL2_ALL:
		FALLTHROUGH;
	case CMD_TLBI_NSNH_ALL:
		break;
	case CMD_TLBI_S2_IPA:
		/* Address[55:12] */
		param1 >>= ADDRESS_SHIFT;
		/* TG=0b00 (TTL, TTL128 are RES0), Leaf=0 */
		cmd |= (uint128_t)(INPLACE(ADDRESS, param1)) << 64;
		/* TG=0b00 (SCALE, NUM  are RES0) */
		cmd |= (uint128_t)COMPOSE(VMID, param0);
		break;
	case CMD_TLBI_S12_VMALL:
		cmd |= (uint128_t)COMPOSE(VMID, param0);
		break;
	default:
		assert(false);
		return -ENOTSUP;
	}

	ret = send_cmd(smmu, cmd);
	if (ret != 0) {
		SMMU_ERROR(ret, "Failed to send command\n");
	}
	return ret;
}

static int inval_cached_ste(struct smmuv3_driver *smmu, unsigned int sid,
			    bool leaf_only)
{
	int ret;

	ret = prepare_send_command(smmu, CMD_CFGI_STE, sid,
				   leaf_only ? LEAF_BIT : 0UL);
	if (ret != 0) {
		SMMU_ERROR(ret, "Failed to send CMD_%s\n", "CFGI_STE");
		return ret;
	}

	ret = prepare_send_command(smmu, CMD_SYNC, 0UL, 0UL);
	if (ret != 0) {
		SMMU_ERROR(ret, "Failed to send CMD_%s\n", "SYNC");
		return ret;
	}

	return wait_cmdq_empty(smmu);
}

static int configure_ste(struct smmuv3_driver *smmu, unsigned int sid,
			 struct ste_entry *ste_ptr,
			 const struct smmu_stg2_config *s2_cfg)
{
	assert((ste_ptr->ste[0] & STE0_V_BIT) == 0UL);

	/*
	 * Set S2 fields, S1 bypassed
	 *
	 * Arm System Memory Management Unit Architecture Specification
	 * SMMU architecture version 3.
	 * 3.21.3.1 Configuration structure update procedure
	 */
	/* STE[63:0] */
	ste_ptr->ste[0] = INPLACE(STE0_CONFIG, STE0_CONFIG_S2);
	/* STE[127:64] */
	ste_ptr->ste[1] = INPLACE(STE1_SHCFG, STE1_SHCFG_INCOMING);
	/* STE[191:128] */
	ste_ptr->ste[2] = INPLACE(STE2_S2VMID, s2_cfg->vmid) |
			  COMPOSE(STE2_VTCR, s2_cfg->vtcr) |
			  STE2_S2PTW_BIT | STE2_S2AA64_BIT | STE2_S2R_BIT;
	/* STE[255:192] */
	ste_ptr->ste[3] = INPLACE(STE3_S2TTB, s2_cfg->s2ttb >> STE3_S2TTB_SHIFT);
	dsb(ish);

	/* Invalidate configuration structure */
	return inval_cached_ste(smmu, sid, true);
}

static int inval_cfg_tlbs(struct smmuv3_driver *smmu)
{
	int ret;

	ret = prepare_send_command(smmu, CMD_CFGI_ALL, 0UL, 0UL);
	if (ret != 0) {
		SMMU_ERROR(ret, "Failed to send CMD_%s\n", "CFGI_ALL");
		return ret;
	}

	ret = prepare_send_command(smmu, CMD_TLBI_EL2_ALL, 0UL, 0UL);
	if (ret != 0) {
		SMMU_ERROR(ret, "Failed to send CMD_%s\n", "TLBI_EL2_ALL");
		return ret;
	}

	ret = prepare_send_command(smmu, CMD_TLBI_NSNH_ALL, 0UL, 0UL);
	if (ret != 0) {
		SMMU_ERROR(ret, "Failed to send CMD_%s\n", "TLBI_NSNH_ALL");
		return ret;
	}

	ret = prepare_send_command(smmu, CMD_SYNC, 0UL, 0UL);
	if (ret != 0) {
		SMMU_ERROR(ret, "Failed to send CMD_%s\n", "SYNC");
		return ret;
	}

	return wait_cmdq_empty(smmu);
}

static int enable_smmu(struct smmuv3_driver *smmu)
{
	uint32_t cr0, cr2 = SMMU_R_CR2_INIT;
	int ret;

	write32(SMMU_R_CR1_INIT, (void *)((uintptr_t)smmu->r_base_addr +
							SMMU_R_CR1));
	if ((smmu->config.features & FEAT_BTM) != 0U) {
		/*
		 * 1: The SMMU is not required to invalidate
		 * any local TLB entries on receipt of broadcast
		 * TLB maintenance operations for Realm translation regimes.
		 */
		cr2 |= R_CR2_PTM_BIT;
	}
	write32(cr2, (void *)((uintptr_t)smmu->r_base_addr + SMMU_R_CR2));

	cr0 = SMMU_R_CR0_INIT | R_CR0_CMDQEN_BIT;

	/* Initialise and enable the Command queue */
	write32(cr0, (void *)((uintptr_t)smmu->r_base_addr + SMMU_R_CR0));
	ret = wait_for_ack(smmu, SMMU_R_CR0ACK, cr0, cr0);
	if (ret != 0) {
		SMMU_ERROR(ret, "Failed to enable %s queue\n", "Command");
		return ret;
	}

	cr0 |= R_CR0_EVTQEN_BIT;

	/* Enable the Event queue */
	write32(cr0, (void *)((uintptr_t)smmu->r_base_addr + SMMU_R_CR0));
	ret = wait_for_ack(smmu, SMMU_R_CR0ACK, R_CR0ACK_EVTQEN_BIT, cr0);
	if (ret != 0) {
		SMMU_ERROR(ret, "Failed to enable %s queue\n", "Event");
		return ret;
	}

	/* Invalidate cached configurations and TLBs */
	ret = inval_cfg_tlbs(smmu);
	if (ret != 0) {
		SMMU_ERROR(ret, "Failed to invalidate TLBs\n");
		return ret;
	}

	/* Enable SMMU translation */
	cr0 |= R_CR0_SMMUEN_BIT;
	write32(cr0, (void *)((uintptr_t)smmu->r_base_addr + SMMU_R_CR0));
	ret = wait_for_ack(smmu, SMMU_R_CR0ACK, R_CR0ACK_SMMUEN_BIT, cr0);
	if (ret != 0) {
		SMMU_ERROR(ret, "Failed to enable\n");
	}

	return ret;
}

static int get_features(struct smmuv3_driver *smmu)
{
	uint32_t aidr, idr0, r_idr0, r_idr3;
	uint32_t val;

	/* All configuration features are cleared as part of initialisation */

	aidr = read32((void *)((uintptr_t)smmu->ns_base_addr + SMMU_AIDR));
	/* cppcheck-suppress misra-c2012-12.2 */
	val = EXTRACT32(AIDR_ARCH_MINOR_REV, aidr);
	smmu->config.minor_rev = val;
	SMMU_DEBUG("SMMUv3: architecture revision 3.%u\n", val);

	idr0 = read32((void *)((uintptr_t)smmu->ns_base_addr + SMMU_IDR0));
	/* cppcheck-suppress misra-c2012-12.2 */
	val = EXTRACT32(IDR0_ST_LEVEL, idr0);
	if (val == TWO_LVL_STR_TABLE) {
		smmu->config.features |= FEAT_2_LVL_STRTAB;
		SMMU_DEBUG("\t2-level Stream table\n");
	} else {
		assert(val == LINEAR_STR_TABLE);
		SMMU_ERROR(-ENOTSUP, "2-level Stream table not supported\n");
		return -ENOTSUP;
	}

	/* cppcheck-suppress misra-c2012-12.2 */
	val = EXTRACT32(IDR0_TTF, idr0);

	switch (val) {
	case AARCH64_TTF:
	case AARCH32_64_TTF:
		SMMU_DEBUG("\tAArch64 translation table format\n");
		break;
	default:
		SMMU_ERROR(-ENOTSUP, "Unsupported translation table format %u\n", val);
		return -ENOTSUP;
	}

	if ((idr0 & IDR0_BTM_BIT) != 0U) {
		smmu->config.features |= FEAT_BTM;
		SMMU_DEBUG("\tBroadcast TLB maintenance\n");
	} else {
		broadcast_tlb = false;
	}

	if ((idr0 & IDR0_S1P_BIT) != 0U) {
		smmu->config.features |= FEAT_S1P;
		SMMU_DEBUG("\tStage %u translation\n", 1);
	}

	if ((idr0 & IDR0_S2P_BIT) != 0U) {
		SMMU_DEBUG("\tStage %u translation\n", 2);
	} else {
		SMMU_ERROR(-ENOTSUP, "Stage 2 translation not supported\n");
		return -ENOTSUP;
	}

	if ((idr0 & IDR0_VMW_BIT) != 0U) {
		SMMU_DEBUG("\tVMW\n");
	} else {
		SMMU_ERROR(-ENOTSUP, "VMID wildcard-matching is not supported\n");
		return -ENOTSUP;
	}

	if ((idr0 & IDR0_ASID16_BIT) != 0U) {
		smmu->config.features |= FEAT_ASID16;
		SMMU_DEBUG("\t16-bit ASID\n");
	}

	if ((idr0 & IDR0_VMID16_BIT) != 0U) {
		smmu->config.features |= FEAT_VMID16;
		SMMU_DEBUG("\t16-bit VMID\n");
	} else if (is_feat_vmid16_present()) {
		SMMU_ERROR(-ENOTSUP, "16-bit VMID is not supported\n");
		return -ENOTSUP;
	}

	r_idr0 = read32((void *)((uintptr_t)smmu->r_base_addr + SMMU_R_IDR0));
	if ((r_idr0 & R_IDR0_ATS_BIT) != 0U) {
		smmu->config.realm_features |= FEAT_R_ATS;
		SMMU_DEBUG("\tPCIe ATS for Realm state\n");
	}

	if ((r_idr0 & R_IDR0_MSI_BIT) != 0U) {
		smmu->config.realm_features |= FEAT_R_MSI;
		SMMU_DEBUG("\tMSIs for Realm state\n");
	}

	if ((r_idr0 & R_IDR0_PRI_BIT) != 0U) {
		smmu->config.realm_features |= FEAT_R_PRI;
		SMMU_DEBUG("\tPRI for Realm state\n");
	}

	r_idr3 = read32((void *)((uintptr_t)smmu->r_base_addr + SMMU_R_IDR3));
	if ((r_idr3 & R_IDR3_DPT_BIT) != 0U) {
		smmu->config.realm_features |= FEAT_R_DPT;
		SMMU_DEBUG("\tDPT\n");
	}

	if ((r_idr3 & R_IDR3_MEC_BIT) != 0U) {
		smmu->config.realm_features |= FEAT_R_MEC;
		SMMU_DEBUG("\tMEC\n");
	} else if (is_feat_mec_present()) {
		SMMU_ERROR(-ENOTSUP, "MEC is not supported\n");
		return -ENOTSUP;
	}

	return 0;
}

static int disable_smmu(struct smmuv3_driver *smmu)
{
	uint32_t cr0;
	int ret;

	cr0 = read32((void *)((uintptr_t)smmu->r_base_addr + SMMU_R_CR0));
	cr0 &= ~R_CR0_SMMUEN_BIT;

	write32(cr0, (void *)((uintptr_t)smmu->r_base_addr + SMMU_R_CR0));
	ret = wait_for_ack(smmu, SMMU_R_CR0ACK, R_CR0ACK_SMMUEN_BIT, cr0);
	if (ret != 0) {
		SMMU_ERROR(ret, "Failed to disable\n");
	}

	return ret;
}

struct smmuv3_driver *get_by_index(unsigned long smmu_idx, unsigned int sid)
{
	struct smmuv3_driver *smmu;

	/* The caller is responsible to ensure that SMMU index and SID are valid */
	if (smmu_idx >= arm_smmu.num_smmus) {
		SMMU_DEBUG("SMMUv3: Illegal ID %lu\n", smmu_idx);
		return NULL;
	}

	smmu = &arm_smmu_driver[smmu_idx];

	if (sid > ((U(1) << smmu->config.streamid_bits) - 1U)) {
		SMMU_ERROR(-EINVAL, "Illegal StreamID 0x%x\n", sid);
		return NULL;
	}

	return smmu;
}

static int change_ste(unsigned long smmu_idx, unsigned int sid, bool enable)
{
	struct smmuv3_driver *smmu;
	struct ste_entry *ste_ptr;
	bool valid;
	int ret;

	smmu = get_by_index(smmu_idx, sid);
	if (smmu == NULL) {
		return -EINVAL;
	}

	spinlock_acquire(&smmu->lock);
	ste_ptr = sid_to_ste(smmu, sid);

	/* Check STE.V bit */
	valid = (ste_ptr->ste[0] & STE0_V_BIT) != 0UL;
	if (valid == enable) {
		/* STE is already enabled/disabled */
		spinlock_release(&smmu->lock);
		return -EINVAL;
	}

	/* Toggle STE.V bit */
	ste_ptr->ste[0] ^= STE0_V_BIT;
	dsb(ish);

	/* Invalidate configuration structure */
	ret = inval_cached_ste(smmu, sid, false);
	if (ret != 0) {
		spinlock_release(&smmu->lock);
		return ret;
	}

	if (enable) {
		/*
		 * Issue prefetch command so that new config for SID is fetched
		 * by SMMU. Note that no sync+wait is required. SMMU will fetch
		 * the STE in the background.
		 */
		ret = prepare_send_command(smmu, CMD_PREFETCH_CONFIG, sid, 0UL);
	}

	spinlock_release(&smmu->lock);
	return ret;
}

int smmuv3_allocate_ste(unsigned long smmu_idx, unsigned int sid)
{
	struct smmuv3_driver *smmu;
	unsigned int sids_num, l1_idx;
	bool leaf;
	int ret;

	SMMU_DEBUG("%s(0x%x)\n", __func__, sid);

	smmu = get_by_index(smmu_idx, sid);
	if (smmu == NULL) {
		return -EINVAL;
	}

	/* Number of entries in smmu->sids bitmap */
	sids_num = ((U(1) << (smmu->config.streamid_bits)) +
			BITS_PER_UL - 1U) / BITS_PER_UL;

	/* L1STD index */
	l1_idx = L1_IDX(sid);

	spinlock_acquire(&smmu->lock);

	assert(smmu->l1std_cnt[l1_idx] < (STRTAB_L1_STE_MAX - 1U));

	/* Check that the StreamID is available */
	ret = bitmap_update(smmu->sids, sid, sids_num, true);
	if (ret != 0) {
		spinlock_release(&smmu->lock);
		return -ENOMEM;
	}

	/* Is L1STD already set? */
	if (smmu->l1std_cnt[l1_idx]++ == 0U) {
		/* Set L2 table */
		void *l2ptr_pa = &smmu->l2strtab_base->l2tabs_entry[l1_idx];

		smmu->l1std_l2ptr[l1_idx] = l2ptr_pa;

		/* Update L1STD */
		write_strtab_l1std(&smmu->strtab_base[l1_idx], l2ptr_pa);
		leaf = false;
	} else {
		leaf = true;
	}

	/* Invalidate configuration structure */
	ret = inval_cached_ste(smmu, sid, leaf);
	spinlock_release(&smmu->lock);
	return ret;
}

int smmuv3_release_ste(unsigned long smmu_idx, unsigned int sid)
{
	struct smmuv3_driver *smmu;
	struct ste_entry *ste_ptr;
	unsigned int sids_num, l1_idx;
	bool leaf;
	int ret;

	SMMU_DEBUG("%s(0x%x)\n", __func__, sid);

	smmu = get_by_index(smmu_idx, sid);
	if (smmu == NULL) {
		return -EINVAL;
	}

	/* Number of entries in smmu->sids bitmap */
	sids_num = ((U(1) << (smmu->config.streamid_bits)) +
			BITS_PER_UL - 1U) / BITS_PER_UL;

	l1_idx = L1_IDX(sid);

	spinlock_acquire(&smmu->lock);

	ste_ptr = sid_to_ste(smmu, sid);

	/* Check that STE is not valid, e.g. smmuv3_disable_ste() was called */
	if ((ste_ptr->ste[0] & STE0_V_BIT) != 0UL) {
		spinlock_release(&smmu->lock);
		SMMU_ERROR(-EINVAL, "Cannot release valid STE with SID 0x%x\n", sid);
		return -EINVAL;
	}

	assert(smmu->l1std_cnt[l1_idx] != 0U);

	/* Check that the StreamID was allocated */
	ret = bitmap_update(smmu->sids, sid, sids_num, false);
	if (ret != 0) {
		spinlock_release(&smmu->lock);
		SMMU_ERROR(ret, "Not allocated SID 0x%x\n", sid);
		return ret;
	}

	/*
	 * STE is not valid, STE.V == 0.
	 * Ensure that the context can no longer be used.
	 * Clear S2 STE fields.
	 */
	ste_ptr->ste[0] = 0UL;
	ste_ptr->ste[1] = 0UL;
	ste_ptr->ste[2] = 0UL;
	ste_ptr->ste[3] = 0UL;
	dsb(ish);

	if (--smmu->l1std_cnt[l1_idx] == 0U) {
		/* Drop the reference to the L2 table */
		smmu->l1std_l2ptr[l1_idx] = NULL;

		/* Remove L1STD */
		smmu->strtab_base[l1_idx] = 0UL;
		leaf = false;
	} else {
		leaf = true;
	}

	/* Invalidate configuration structure */
	ret = inval_cached_ste(smmu, sid, leaf);
	spinlock_release(&smmu->lock);
	return ret;
}

int smmuv3_enable_ste(unsigned long smmu_idx, unsigned int sid)
{
	SMMU_DEBUG("%s(0x%x)\n", __func__, sid);

	return change_ste(smmu_idx, sid, true);
}

int smmuv3_disable_ste(unsigned long smmu_idx, unsigned int sid)
{
	SMMU_DEBUG("%s(0x%x)\n", __func__, sid);

	return change_ste(smmu_idx, sid, false);
}

int smmuv3_configure_stream(unsigned long smmu_idx,
			    struct smmu_stg2_config *s2_cfg,
			    unsigned int sid)
{
	struct smmuv3_driver *smmu;
	struct ste_entry *ste_ptr;
	int ret;

	assert(s2_cfg != NULL);

	SMMU_DEBUG("%s(0x%x) s2ttb %lx vtcr %lx vmid %x\n",
		__func__, sid, s2_cfg->s2ttb, s2_cfg->vtcr, s2_cfg->vmid);

	smmu = get_by_index(smmu_idx, sid);
	if (smmu == NULL) {
		return -EINVAL;
	}

	assert((s2_cfg->vmid < (U(1) << 8)) ||
		((smmu->config.features & FEAT_VMID16) != 0U));

	spinlock_acquire(&smmu->lock);

	ste_ptr = sid_to_ste(smmu, sid);

	/* Check that STE is not valid */
	if ((ste_ptr->ste[0] & STE0_V_BIT) != 0UL) {
		spinlock_release(&smmu->lock);
		SMMU_ERROR(-EINVAL, "Cannot configure valid STE with SID 0x%x\n", sid);
		return -EINVAL;
	}

	ret = configure_ste(smmu, sid, ste_ptr, s2_cfg);
	spinlock_release(&smmu->lock);
	return ret;
}

int smmuv3_init(void)
{
	struct smmuv3_driver *smmu = arm_smmu_driver;
	struct smmu_info *info = arm_smmu.arm_smmu_info;
	unsigned long num_smmus = arm_smmu.num_smmus;
	int ret;

	/* SMMUv3 layout info not set */
	if (num_smmus == 0UL) {
		return -ENODEV;
	}

	for (unsigned long i = 0UL; i < num_smmus; i++) {
		smmu->ns_base_addr = (void *)(info->smmu_base);
		smmu->r_base_addr = (void *)(info->smmu_r_base);

		SMMU_DEBUG("SMMUv3 #%lu base pages: NS @0x%lx R @0x%lx\n", i,
				(uintptr_t)smmu->ns_base_addr,
				(uintptr_t)smmu->r_base_addr);

		ret = disable_smmu(smmu);
		if (ret != 0) {
			goto err;
		}

		ret = get_features(smmu);
		if (ret != 0) {
			goto err;
		}

		ret = init_config(smmu);
		if (ret != 0) {
			goto err;
		}

		configure_queue(smmu, CMDQ, &cmd_queue[i].entry);
		configure_queue(smmu, EVTQ, &evt_queue[i].entry);
		configure_strtab(smmu, &strtab[i].entry);

		/* Base address of L2 Stream Tables */
		smmu->l2strtab_base = &l2_strtab[i];

		ret = enable_smmu(smmu);
		if (ret != 0) {
			goto err;
		}

		smmu++;
		info++;
	}
	return 0;
err:
	arm_smmu.num_smmus = 0UL;
	return ret;
}
