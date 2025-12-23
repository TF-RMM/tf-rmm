/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors
 */

#include <arch_features.h>
#include <assert.h>
#include <bitmap.h>
#include <errno.h>
#include <glob_data.h>
#include <mmio.h>
#include <rmm_el3_ifc.h>
#include <smmuv3.h>
#include <smmuv3_priv.h>
#include <utils_def.h>

/* Index to point L2 table */
#define L1_IDX(sid)	((sid) >> SMMU_STRTAB_SPLIT)

/* Index to point STE in Level 2 table */
#define L2_IDX(sid)	((sid) & ((U(1) << SMMU_STRTAB_SPLIT) - 1U))

/* Log2 of max command record size */
#define MAX_LOG2_CMD_RECORD_SIZE	8U

COMPILER_ASSERT(MAX_LOG2_CMD_RECORD_SIZE == \
		(GRANULE_SHIFT - (unsigned int)__builtin_ctz(CMD_RECORD_SIZE)));

/* Log2 of max event record size */
#define MAX_LOG2_EVT_RECORD_SIZE	7U

COMPILER_ASSERT(MAX_LOG2_EVT_RECORD_SIZE == \
		(GRANULE_SHIFT - (unsigned int)__builtin_ctz(EVT_RECORD_SIZE)));

static struct smmuv3_driv *g_driver;
static struct smmuv3_dev *g_smmus;

bool get_smmu_broadcast_tlb(void)
{
	assert(g_driver != NULL);
	return g_driver->broadcast_tlb;
}

struct smmuv3_driv *get_smmuv3_driver(void)
{
	return g_driver;
}

/*
 * Memory layout of SMMU driver structure within a single granule:
 *
 * ┌─────────────────────────────────────────────────────┐ ← GRANULE start (aligned)
 * │                                                     │
 * │  struct smmuv3_driv                                 │
 * │  ┌────────────────────────────────────────────────┐ │
 * │  │ ....                                           │ │
 * │  │ struct smmuv3_dev *smmuv3_devs  ───────────────┼─┼─┐
 * │  └────────────────────────────────────────────────┘ │ │
 * │                                                     │ │
 * ├─────────────────────────────────────────────────────┤ │
 * │  struct smmuv3_dev[0]                               │◄┘
 * │  ┌────────────────────────────────────────────────┐ │
 * │  │ ...............                                │ │
 * │  └────────────────────────────────────────────────┘ │
 * │                                                     │
 * │  struct smmuv3_dev[1]                               │
 * │  ┌────────────────────────────────────────────────┐ │
 * │  │ ...                                            │ │
 * │  └────────────────────────────────────────────────┘ │
 * │                                                     │
 * │  ...                                                │
 * │                                                     │
 * │  struct smmuv3_dev[num_smmus-1]                     │
 * │  ┌────────────────────────────────────────────────┐ │
 * │  │ ...                                            │ │
 * │  └────────────────────────────────────────────────┘ │
 * │                                                     │
 * │  <unused space>                                     │
 * │                                                     │
 * └─────────────────────────────────────────────────────┘ ← GRANULE end
 *                                                           (GRANULE_SIZE bytes)
 *
 * Note: sizeof(struct smmuv3_driv) + num_smmus * sizeof(struct smmuv3_dev)
 *       must be <= GRANULE_SIZE (typically 4KB)
 */

/* cppcheck-suppress misra-c2012-8.7 */
uintptr_t smmuv3_driver_setup(struct smmu_list *plat_smmu_list, uintptr_t *out_pa,
				size_t *out_sz)
{
	int ret;
	uintptr_t va;
	size_t size;
	struct smmuv3_dev *smmu;
	struct smmuv3_driv *driver;

	assert(plat_smmu_list != NULL);
	assert(out_pa != NULL);
	assert(out_sz != NULL);

	/* Ensure the driver structure and all device records fit in one granule */
	size = plat_smmu_list->num_smmus * sizeof(struct smmuv3_dev);
	if ((size + sizeof(struct smmuv3_driv)) > GRANULE_SIZE) {
		*out_pa = 0UL;
		*out_sz = 0UL;
		ERROR("Not enough space to allocate smmuv3_dev array\n");
		return 0UL;
	}

	ret = rmm_el3_ifc_reserve_memory(GRANULE_SIZE, 0, GRANULE_SIZE, out_pa);
	if (ret != 0) {
		ERROR("Failed to reserve memory for smmu_layout\n");
		*out_pa = 0UL;
		*out_sz = 0UL;
		return 0UL;
	}

	va = xlat_low_va_map(GRANULE_SIZE, MT_RW_DATA | MT_REALM, *out_pa, true);
	if (va == 0U) {
		ERROR("Failed to allocate VA for smmu_layout\n");
		*out_pa = 0UL;
		*out_sz = 0UL;
		return 0UL;
	}

	assert(*out_pa != 0UL);
	*out_sz = GRANULE_SIZE;

	driver = (struct smmuv3_driv *)va;

	/* Set number of SMMUs */
	driver->num_smmus = plat_smmu_list->num_smmus;
	assert((plat_smmu_list->num_smmus == 0UL) || (plat_smmu_list->smmus != NULL));

	/* Setup smmuv3_dev array after `smmuv3_driver` */
	driver->smmuv3_devs = (struct smmuv3_dev *)((uintptr_t)driver +
						 sizeof(struct smmuv3_driv));

	/* Init smmuv3_dev fields based on SMMU info structures */
	smmu = driver->smmuv3_devs;
	for (uint64_t i = 0U; i < plat_smmu_list->num_smmus; i++) {
		smmu[i].ns_base_pa = (void *)plat_smmu_list->smmus[i].smmu_base;
		smmu[i].r_base_pa = (void *)plat_smmu_list->smmus[i].smmu_r_base;
		SMMU_DEBUG("SMMUv3[%lu]: NS base addr: 0x%lx, R base addr: 0x%lx\n",
			   i,
			   (uintptr_t)smmu[i].ns_base_pa,
			   (uintptr_t)smmu[i].r_base_pa);
	}

	return va;
}

static void write_strtab_l1std(uint64_t *l1std, void *l2ptr_pa)
{
	uint64_t val = COMPOSE(STRTAB_L1_DESC_SPAN, (SMMU_STRTAB_SPLIT + 1U)) |
			((uintptr_t)l2ptr_pa & MASK(STRTAB_L1_DESC_L2PTR));

	*l1std = val;
	dsb(ish);
}

/* Get address of STE */
static inline struct ste_entry *sid_to_ste(struct smmuv3_dev *smmu, unsigned int sid)
{
	return &smmu->l2strtab_base[L1_IDX(sid)].l2tab_entry[L2_IDX(sid)];
}

static void configure_strtab(struct smmuv3_dev *smmu, void *strtab_base_pa)
{
	uint32_t reg;
	uint64_t reg64;

	reg  = INPLACE32(STRTAB_BASE_CFG_LOG2SIZE, smmu->config.streamid_bits);
	reg |= INPLACE32(STRTAB_BASE_CFG_SPLIT, SMMU_STRTAB_SPLIT);
	reg |= INPLACE32(STRTAB_BASE_CFG_FMT, TWO_LVL_STR_TABLE);
	write32(reg, (void *)((uintptr_t)smmu->r_base + SMMU_R_STRTAB_BASE_CFG));

	reg64 = (uintptr_t)strtab_base_pa | RAWA_BIT;
	write64(reg64, (void *)((uintptr_t)smmu->r_base + SMMU_R_STRTAB_BASE));


	SMMU_DEBUG("\tConfigured 2-level Stream table @0x%lx mapped to 0x%lx\n",
					(uintptr_t)strtab_base_pa,
					(uintptr_t)smmu->strtab_base);
}

static void configure_queue(struct smmuv3_dev *smmu, enum queue_type type,
			    void *queue_base_pa)
{
	struct smmu_queue *queue;
	uint64_t base_reg;
	uint32_t base_offset, cons_offset, prod_offset;
	unsigned int log2size;

	if (type == CMDQ) {
		queue = &smmu->cmdq;
		log2size = smmu->config.cmdq_log2size;
		base_offset = SMMU_R_CMDQ_BASE;
		cons_offset = SMMU_R_CMDQ_CONS;
		prod_offset = SMMU_R_CMDQ_PROD;
	} else {
		queue = &smmu->evtq;
		log2size = smmu->config.evtq_log2size;
		base_offset = SMMU_R_EVENTQ_BASE;
		cons_offset = SMMU_R_EVENTQ_CONS;
		prod_offset = SMMU_R_EVENTQ_PROD;
	}

	base_reg = (uintptr_t)queue_base_pa | RAWA_BIT;
	base_reg |= INPLACE(SMMU_R_BASE_LOG2SIZE, log2size);

	queue->cons_reg = (void *)((uintptr_t)smmu->r_base + cons_offset);
	queue->prod_reg = (void *)((uintptr_t)smmu->r_base + prod_offset);

	write64(base_reg, (void *)((uintptr_t)smmu->r_base + base_offset));

	/* Queue RD/WR indexes = 0 */
	write32(0U, queue->cons_reg);
	write32(0U, queue->prod_reg);
}

static int init_config(struct smmuv3_dev *smmu)
{
	uint32_t idr1 = read32((void *)((uintptr_t)smmu->ns_base + SMMU_IDR1));
	unsigned int log2size;

	if ((idr1 & (IDR1_QUEUES_PRESET_BIT | IDR1_TABLES_PRESET_BIT)) != 0U) {
		SMMU_ERROR(smmu,
			"Driver doesn't support TABLES_PRESET and QUEUES_PRESET\n");
		return -ENOTSUP;
	}

	/* Command queue */
	/* cppcheck-suppress misra-c2012-12.2 */
	log2size = EXTRACT32(IDR1_CMDQS, idr1);

	/* Restrict to 4KB command queue (256 entries) */
	if (log2size > MAX_LOG2_CMD_RECORD_SIZE) {
		log2size = MAX_LOG2_CMD_RECORD_SIZE;
	}

	/* Use hardware-detected value bounded by max */
	smmu->config.cmdq_log2size = log2size;
	SMMU_DEBUG("\tCMDQ log2 size %u\n", smmu->config.cmdq_log2size);

	/* Event queue */
	/* cppcheck-suppress misra-c2012-12.2 */
	log2size = EXTRACT32(IDR1_EVTQS, idr1);

	/* Restrict to 4KB event queue (128 entries) */
	if (log2size > MAX_LOG2_EVT_RECORD_SIZE) {
		log2size = MAX_LOG2_EVT_RECORD_SIZE;
	}

	/* Use hardware-detected value bounded by max */
	smmu->config.evtq_log2size = log2size;
	SMMU_DEBUG("\tEVTQ log2 size %u\n", smmu->config.evtq_log2size);

	/* Max bits of SubstreamID */
	/* cppcheck-suppress misra-c2012-12.2 */
	log2size = EXTRACT32(IDR1_SSIDSIZE, idr1);

	smmu->config.substreamid_bits = log2size;
	SMMU_DEBUG("\tSubstreamID max bits %u\n", log2size);

	/* Max bits of StreamID */
	/* cppcheck-suppress misra-c2012-12.2 */
	log2size = EXTRACT32(IDR1_SIDSIZE, idr1);

	/* Use hardware-detected value */
	smmu->config.streamid_bits = log2size;
	SMMU_DEBUG("\tStreamID max bits %u\n", log2size);

	if (smmu->config.streamid_bits < SMMU_STRTAB_SPLIT) {
		SMMU_ERROR(smmu, "StreamID max bits %u < SMMU_STRTAB_SPLIT %u\n",
				smmu->config.streamid_bits, SMMU_STRTAB_SPLIT);
		return -ENOTSUP;
	}

	smmu->num_l1_ents = (1UL << (smmu->config.streamid_bits - SMMU_STRTAB_SPLIT));
	SMMU_DEBUG("\tNumber of Stream Table L1 entries %ld\n", smmu->num_l1_ents);

	return 0;
}

static int wait_for_ack(struct smmuv3_dev *smmu, uint32_t offset,
			uint32_t mask, uint32_t expected)
{
	unsigned int retries = 0U;

	while (retries++ < MAX_RETRIES) {
		uint32_t val = read32((void *)((uintptr_t)smmu->r_base +
							offset));
		if ((val & mask) == (expected & mask)) {
			return 0;
		}
	}

	return -ETIMEDOUT;
}

static int check_cmdq_err(struct smmuv3_dev *smmu)
{
	uint32_t gerror_reg = read32((void *)((uintptr_t)smmu->r_base +
							SMMU_R_GERROR));
	uint32_t gerror_n_reg = read32((void *)((uintptr_t)smmu->r_base +
							SMMU_R_GERRORN));
	uint32_t cons_reg, err;

	if ((gerror_reg & CMDQ_ERR_BIT) == (gerror_n_reg & CMDQ_ERR_BIT)) {
		return 0;
	}

	SMMU_ERROR(smmu, "Cannot process commands\n");
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
	write32(gerror_n_reg, (void *)((uintptr_t)smmu->r_base + SMMU_R_GERRORN));

	return -EIO;
}

int wait_cmdq_empty(struct smmuv3_dev *smmu)
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

	SMMU_ERROR(smmu, "Timeout processing commands CONS: 0x%x PROD: 0x%x\n",
			cons_reg, prod_reg);
	return -ETIMEDOUT;
}

static int send_cmd(struct smmuv3_dev *smmu, uint128_t cmd)
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
		SMMU_ERROR(smmu, "Command queue full\n");
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

int prepare_send_command(struct smmuv3_dev *smmu, unsigned long opcode,
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
		SMMU_ERROR(smmu, "Failed to send command\n");
	}
	return ret;
}

static int inval_cached_ste(struct smmuv3_dev *smmu, unsigned int sid,
			    bool leaf_only)
{
	int ret;

	ret = prepare_send_command(smmu, CMD_CFGI_STE, sid,
				   leaf_only ? LEAF_BIT : 0UL);
	if (ret != 0) {
		SMMU_ERROR(smmu, "Failed to send CMD_%s\n", "CFGI_STE");
		return ret;
	}

	ret = prepare_send_command(smmu, CMD_SYNC, 0UL, 0UL);
	if (ret != 0) {
		SMMU_ERROR(smmu, "Failed to send CMD_%s\n", "SYNC");
		return ret;
	}

	return wait_cmdq_empty(smmu);
}

static int configure_ste(struct smmuv3_dev *smmu, unsigned int sid,
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

static int inval_cfg_tlbs(struct smmuv3_dev *smmu)
{
	int ret;

	assert(smmu != NULL);

	ret = prepare_send_command(smmu, CMD_CFGI_ALL, 0UL, 0UL);
	if (ret != 0) {
		SMMU_ERROR(smmu, "Failed to send CMD_%s\n", "CFGI_ALL");
		return ret;
	}

	ret = prepare_send_command(smmu, CMD_TLBI_EL2_ALL, 0UL, 0UL);
	if (ret != 0) {
		SMMU_ERROR(smmu, "Failed to send CMD_%s\n", "TLBI_EL2_ALL");
		return ret;
	}

	ret = prepare_send_command(smmu, CMD_TLBI_NSNH_ALL, 0UL, 0UL);
	if (ret != 0) {
		SMMU_ERROR(smmu, "Failed to send CMD_%s\n", "TLBI_NSNH_ALL");
		return ret;
	}

	ret = prepare_send_command(smmu, CMD_SYNC, 0UL, 0UL);
	if (ret != 0) {
		SMMU_ERROR(smmu, "Failed to send CMD_%s\n", "SYNC");
		return ret;
	}

	return wait_cmdq_empty(smmu);
}

static int enable_smmu(struct smmuv3_dev *smmu)
{
	uint32_t cr0, cr2 = SMMU_R_CR2_INIT;
	int ret;

	assert(smmu != NULL);

	write32(SMMU_R_CR1_INIT, (void *)((uintptr_t)smmu->r_base +
							SMMU_R_CR1));
	if ((smmu->config.features & FEAT_BTM) != 0U) {
		/*
		 * 1: The SMMU is not required to invalidate
		 * any local TLB entries on receipt of broadcast
		 * TLB maintenance operations for Realm translation regimes.
		 */
		cr2 |= R_CR2_PTM_BIT;
	}
	write32(cr2, (void *)((uintptr_t)smmu->r_base + SMMU_R_CR2));

	cr0 = SMMU_R_CR0_INIT | R_CR0_CMDQEN_BIT;

	/* Initialise and enable the Command queue */
	write32(cr0, (void *)((uintptr_t)smmu->r_base + SMMU_R_CR0));
	ret = wait_for_ack(smmu, SMMU_R_CR0ACK, cr0, cr0);
	if (ret != 0) {
		SMMU_ERROR(smmu, "Failed to enable %s queue\n", "Command");
		return ret;
	}

	cr0 |= R_CR0_EVTQEN_BIT;

	/* Enable the Event queue */
	write32(cr0, (void *)((uintptr_t)smmu->r_base + SMMU_R_CR0));
	ret = wait_for_ack(smmu, SMMU_R_CR0ACK, R_CR0ACK_EVTQEN_BIT, cr0);
	if (ret != 0) {
		SMMU_ERROR(smmu, "Failed to enable %s queue\n", "Event");
		return ret;
	}

	/* Invalidate cached configurations and TLBs */
	ret = inval_cfg_tlbs(smmu);
	if (ret != 0) {
		SMMU_ERROR(smmu, "Failed to invalidate TLBs\n");
		return ret;
	}

	/* Enable SMMU translation */
	cr0 |= R_CR0_SMMUEN_BIT;
	write32(cr0, (void *)((uintptr_t)smmu->r_base + SMMU_R_CR0));
	ret = wait_for_ack(smmu, SMMU_R_CR0ACK, R_CR0ACK_SMMUEN_BIT, cr0);
	if (ret != 0) {
		SMMU_ERROR(smmu, "Failed to enable\n");
	}

	return ret;
}

static int get_features(struct smmuv3_dev *smmu)
{
	uint32_t aidr, idr0, r_idr0, r_idr3;
	uint32_t val;

	assert(smmu != NULL);

	/* All configuration features are cleared as part of initialisation */

	aidr = read32((void *)((uintptr_t)smmu->ns_base + SMMU_AIDR));
	/* cppcheck-suppress misra-c2012-12.2 */
	val = EXTRACT32(AIDR_ARCH_MINOR_REV, aidr);
	smmu->config.minor_rev = val;
	SMMU_DEBUG("SMMUv3: architecture revision 3.%u\n", val);

	idr0 = read32((void *)((uintptr_t)smmu->ns_base + SMMU_IDR0));
	/* cppcheck-suppress misra-c2012-12.2 */
	val = EXTRACT32(IDR0_ST_LEVEL, idr0);
	if (val == TWO_LVL_STR_TABLE) {
		smmu->config.features |= FEAT_2_LVL_STRTAB;
		SMMU_DEBUG("\t2-level Stream table\n");
	} else {
		assert(val == LINEAR_STR_TABLE);
		SMMU_ERROR(smmu, "2-level Stream table not supported\n");
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
		SMMU_ERROR(smmu, "Unsupported translation table format %u\n", val);
		return -ENOTSUP;
	}

	if ((idr0 & IDR0_BTM_BIT) != 0U) {
		smmu->config.features |= FEAT_BTM;
		SMMU_DEBUG("\tBroadcast TLB maintenance\n");
	} else {
		g_driver->broadcast_tlb = false;
	}

	if ((idr0 & IDR0_S1P_BIT) != 0U) {
		smmu->config.features |= FEAT_S1P;
		SMMU_DEBUG("\tStage %u translation\n", 1);
	}

	if ((idr0 & IDR0_S2P_BIT) != 0U) {
		SMMU_DEBUG("\tStage %u translation\n", 2);
	} else {
		SMMU_ERROR(smmu, "Stage 2 translation not supported\n");
		return -ENOTSUP;
	}

	if ((idr0 & IDR0_VMW_BIT) != 0U) {
		SMMU_DEBUG("\tVMW\n");
	} else {
		SMMU_ERROR(smmu, "VMID wildcard-matching is not supported\n");
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
		SMMU_ERROR(smmu, "16-bit VMID is not supported\n");
		return -ENOTSUP;
	}

	r_idr0 = read32((void *)((uintptr_t)smmu->r_base + SMMU_R_IDR0));
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

	r_idr3 = read32((void *)((uintptr_t)smmu->r_base + SMMU_R_IDR3));
	if ((r_idr3 & R_IDR3_DPT_BIT) != 0U) {
		smmu->config.realm_features |= FEAT_R_DPT;
		SMMU_DEBUG("\tDPT\n");
	}

	if ((r_idr3 & R_IDR3_MEC_BIT) != 0U) {
		smmu->config.realm_features |= FEAT_R_MEC;
		SMMU_DEBUG("\tMEC\n");
	} else if (is_feat_mec_present()) {
		SMMU_ERROR(smmu, "MEC is not supported\n");
		return -ENOTSUP;
	}

	return 0;
}

static int disable_smmu(struct smmuv3_dev *smmu)
{
	uint32_t cr0;
	int ret;

	assert(smmu != NULL);
	cr0 = read32((void *)((uintptr_t)smmu->r_base + SMMU_R_CR0));
	cr0 &= ~R_CR0_SMMUEN_BIT;

	write32(cr0, (void *)((uintptr_t)smmu->r_base + SMMU_R_CR0));
	ret = wait_for_ack(smmu, SMMU_R_CR0ACK, R_CR0ACK_SMMUEN_BIT, cr0);
	if (ret != 0) {
		SMMU_ERROR(smmu, "Failed to disable, ret=%d\n", ret);
	}

	return ret;
}

struct smmuv3_dev *get_by_index(unsigned long smmu_idx, unsigned int sid)
{
	struct smmuv3_dev *smmu;

	assert(g_driver != NULL);

	/* The caller is responsible to ensure that SMMU index and SID are valid */
	if (smmu_idx >= g_driver->num_smmus) {
		SMMU_DEBUG("SMMUv3: Illegal SMMU ID %lu\n", smmu_idx);
		return NULL;
	}

	assert(g_smmus != NULL);
	smmu = &g_smmus[smmu_idx];

	if (sid > ((U(1) << smmu->config.streamid_bits) - 1U)) {
		SMMU_DEBUG("Illegal StreamID 0x%x\n", sid);
		return NULL;
	}

	return smmu;
}

static int change_ste(unsigned long smmu_idx, unsigned int sid, bool enable)
{
	struct smmuv3_dev *smmu;
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
	struct smmuv3_dev *smmu;
	unsigned int l1_idx;
	bool leaf;
	int ret;

	SMMU_DEBUG("%s(0x%x)\n", __func__, sid);

	smmu = get_by_index(smmu_idx, sid);
	if (smmu == NULL) {
		return -EINVAL;
	}

	/* L1STD index */
	l1_idx = L1_IDX(sid);

	spinlock_acquire(&smmu->lock);

	assert(smmu->l1std_cnt[l1_idx] < (STRTAB_L1_STE_MAX - 1U));

	/* Check that the StreamID is available */
	ret = bitmap_update(smmu->sids, sid, smmu->sids_size, true);
	if (ret != 0) {
		spinlock_release(&smmu->lock);
		return -ENOMEM;
	}

	/* Is L1STD already set? */
	if (smmu->l1std_cnt[l1_idx]++ == 0U) {
		/* Set L2 table */
		void *l2ptr_pa = &smmu->l2strtab_base_pa[l1_idx];

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
	struct smmuv3_dev *smmu;
	struct ste_entry *ste_ptr;
	unsigned int l1_idx;
	bool leaf;
	int ret;

	SMMU_DEBUG("%s(0x%x)\n", __func__, sid);

	smmu = get_by_index(smmu_idx, sid);
	if (smmu == NULL) {
		return -EINVAL;
	}

	l1_idx = L1_IDX(sid);

	spinlock_acquire(&smmu->lock);

	ste_ptr = sid_to_ste(smmu, sid);

	/* Check that STE is not valid, e.g. smmuv3_disable_ste() was called */
	if ((ste_ptr->ste[0] & STE0_V_BIT) != 0UL) {
		spinlock_release(&smmu->lock);
		SMMU_ERROR(smmu, "Cannot release valid STE with SID 0x%x\n", sid);
		return -EINVAL;
	}

	assert(smmu->l1std_cnt[l1_idx] != 0U);

	/* Check that the StreamID was allocated */
	ret = bitmap_update(smmu->sids, sid, smmu->sids_size, false);
	if (ret != 0) {
		spinlock_release(&smmu->lock);
		SMMU_ERROR(smmu, "Not allocated SID 0x%x\n, ret=%d", sid, ret);
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
		/* Remove L1STD */
		write_strtab_l1std(&smmu->strtab_base[l1_idx], NULL);
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
	struct smmuv3_dev *smmu;
	struct ste_entry *ste_ptr;
	int ret;

	assert(s2_cfg != NULL);

	SMMU_DEBUG("%s(0x%x) s2ttb 0x%lx vtcr 0x%lx vmid 0x%x\n",
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
		SMMU_ERROR(smmu, "Cannot configure valid STE with SID 0x%x\n", sid);
		return -EINVAL;
	}

	ret = configure_ste(smmu, sid, ste_ptr, s2_cfg);
	spinlock_release(&smmu->lock);
	return ret;
}

static int allocate_smmu_resources(struct smmuv3_dev *smmu)
{
	int ret;
	uintptr_t addr;
	uintptr_t va;
	size_t size __unused;

	assert(smmu != NULL);

	/* Allocate command queue based on detected size */
	size = (1UL << smmu->config.cmdq_log2size) * CMD_RECORD_SIZE;
	assert(size <= GRANULE_SIZE);

	ret = rmm_el3_ifc_reserve_memory(GRANULE_SIZE, 0, GRANULE_SIZE, &addr);
	if (ret != 0) {
		SMMU_ERROR(smmu, "Failed to reserve memory for Command queue\n");
		return -ENOMEM;
	}

	va = xlat_low_va_map(GRANULE_SIZE, MT_RW_DATA | MT_REALM, addr, true);
	if ((va == 0UL) || (addr == 0UL)) {
		SMMU_ERROR(smmu, "Failed to map Command queue\n");
		return -ENOMEM;
	}

	smmu->cmdq.q_base = (void *)va;
	smmu->cmdq.q_base_pa = (void *)addr;

	SMMU_DEBUG("CMDQ: va 0x%lx pa 0x%lx size 0x%lx\n",
		   (uintptr_t)smmu->cmdq.q_base,
		   (uintptr_t)smmu->cmdq.q_base_pa,
		   size);

	/* Allocate event queue based on detected size */
	size = (1UL << smmu->config.evtq_log2size) * EVT_RECORD_SIZE;
	assert(size <= GRANULE_SIZE);

	ret = rmm_el3_ifc_reserve_memory(GRANULE_SIZE, 0, GRANULE_SIZE, &addr);
	if (ret != 0) {
		SMMU_ERROR(smmu, "Failed to reserve memory for Event queue\n");
		return -ENOMEM;
	}

	va = xlat_low_va_map(GRANULE_SIZE, MT_RW_DATA | MT_REALM, addr, true);
	if ((va == 0UL) || (addr == 0UL)) {
		SMMU_ERROR(smmu, "Failed to map Event queue\n");
		return -ENOMEM;
	}

	smmu->evtq.q_base = (void *)va;
	smmu->evtq.q_base_pa = (void *)addr;

	SMMU_DEBUG("EVTQ: va 0x%lx pa 0x%lx size 0x%lx\n",
		   (uintptr_t)smmu->evtq.q_base,
		   (uintptr_t)smmu->evtq.q_base_pa,
		   size);

	/* Allocate stream table (L1) based on num of L1 entries */
	size = smmu->num_l1_ents * STRTAB_L1_DESC_SIZE;
	size = round_up(size, GRANULE_SIZE);

	ret = rmm_el3_ifc_reserve_memory(size, 0, size, &addr);
	if (ret != 0) {
		SMMU_ERROR(smmu, "Failed to reserve memory for L1 stream table\n");
		return -ENOMEM;
	}

	va = xlat_low_va_map(size, MT_RW_DATA | MT_REALM, addr, true);
	if ((va == 0UL) || (addr == 0UL)) {
		SMMU_ERROR(smmu, "Failed to map L1 stream table\n");
		return -ENOMEM;
	}

	smmu->strtab_base = (uint64_t *)va;
	smmu->strtab_base_pa = (uint64_t *)addr;

	SMMU_DEBUG("STRTAB L1: va 0x%lx pa 0x%lx size 0x%lx\n",
		   (uintptr_t)smmu->strtab_base,
		   (uintptr_t)smmu->strtab_base_pa,
		   size);

	/*
	 * Allocate L2 stream tables based on num of L1 entries.
	 * Note that size of L2 tables will be GRANULE_ALIGNED.
	 */
	size = smmu->num_l1_ents * sizeof(struct l2tab);
	ret = rmm_el3_ifc_reserve_memory(size, 0, GRANULE_SIZE, &addr);
	if (ret != 0) {
		SMMU_ERROR(smmu, "Failed to reserve memory for L2 stream tables\n");
		return -ENOMEM;
	}

	va = xlat_low_va_map(size, MT_RW_DATA | MT_REALM, addr, true);
	if ((va == 0UL) || (addr == 0UL)) {
		SMMU_ERROR(smmu, "Failed to map L2 stream tables\n");
		return -ENOMEM;
	}

	smmu->l2strtab_base = (struct l2tab *)va;
	smmu->l2strtab_base_pa = (void *)addr;

	SMMU_DEBUG("STRTAB L2: va 0x%lx pa 0x%lx size 0x%lx\n",
		   (uintptr_t)smmu->l2strtab_base,
		   (uintptr_t)smmu->l2strtab_base_pa,
		   size);

	/* Allocate SID bitmap */
	smmu->sids_size = ((U(1) << smmu->config.streamid_bits) + BITS_PER_UL - 1U) / BITS_PER_UL;
	size = round_up(smmu->sids_size * sizeof(unsigned long), GRANULE_SIZE);

	ret = rmm_el3_ifc_reserve_memory(size, 0, GRANULE_SIZE, &addr);
	if (ret != 0) {
		SMMU_ERROR(smmu, "Failed to reserve memory for SID bitmap\n");
		return -ENOMEM;
	}

	va = xlat_low_va_map(size, MT_RW_DATA | MT_REALM, addr, true);
	if ((va == 0UL) || (addr == 0UL)) {
		SMMU_ERROR(smmu, "Failed to map SID bitmap\n");
		return -ENOMEM;
	}

	smmu->sids = (unsigned long *)va;
	smmu->sids_pa = (unsigned long *)addr;

	SMMU_DEBUG("SID bitmap: va 0x%lx pa 0x%lx size 0x%lx\n",
		   (uintptr_t)smmu->sids,
		   (uintptr_t)smmu->sids_pa,
		   size);

	/* Allocate l1std_cnt array */
	size = round_up(smmu->num_l1_ents * sizeof(*(smmu->l1std_cnt)), GRANULE_SIZE);
	ret = rmm_el3_ifc_reserve_memory(size, 0, GRANULE_SIZE, &addr);
	if (ret != 0) {
		SMMU_ERROR(smmu, "Failed to reserve memory for l1std_cnt\n");
		return -ENOMEM;
	}

	va = xlat_low_va_map(size, MT_RW_DATA | MT_REALM, addr, true);
	if ((va == 0UL) || (addr == 0UL)) {
		SMMU_ERROR(smmu, "Failed to map l1std_cnt\n");
		return -ENOMEM;
	}

	smmu->l1std_cnt = (unsigned short *)va;
	smmu->l1std_cnt_pa = (unsigned short *)addr;

	SMMU_DEBUG("l1std_cnt: va 0x%lx pa 0x%lx size 0x%lx\n",
		   (uintptr_t)smmu->l1std_cnt,
		   (uintptr_t)smmu->l1std_cnt_pa,
		   size);

	return 0;
}

int smmuv3_init(uintptr_t driv_hdl, size_t hdl_sz)
{
	unsigned long num_smmus;
	int ret;
	struct smmuv3_dev *smmu;

	if ((driv_hdl == 0U) || (hdl_sz < sizeof(struct smmuv3_driv))) {
		SMMU_DEBUG("Invalid SMMUv3 driver handle\n");
		return -EINVAL;
	}

	assert(g_driver == NULL);

	g_driver = (struct smmuv3_driv *)driv_hdl;
	g_smmus = g_driver->smmuv3_devs;

	/* No SMMUs in the system */
	if (g_driver->num_smmus == 0UL) {
		return -ENODEV;
	}

	if (g_driver->is_init) {
		SMMU_DEBUG("SMMUv3 driver already initialized\n");
		return 0;
	}

	/* Initialize broadcast_tlb to true, will be set to false if any SMMU doesn't support it */
	g_driver->broadcast_tlb = true;

	num_smmus = g_driver->num_smmus;
	assert(g_smmus != NULL);

	/* Init the SMMUv3 instances */
	for (unsigned long i = 0U; i < num_smmus; i++) {
		smmu = &g_smmus[i];

		/* SMMU registers, Page 0 */
		smmu->ns_base = (void *)xlat_low_va_map(SZ_64K, (MT_RW_DEV | MT_NS),
						(uintptr_t)smmu->ns_base_pa, false);
		if (smmu->ns_base == NULL) {
			SMMU_ERROR(smmu, "Failed to map SMMU NS base 0x%lx\n",
				   (uintptr_t)smmu->ns_base_pa);
			ret = -ENOMEM;
			goto err;
		}

		/* SMMU registers, Realm Page 0 and 1 */
		smmu->r_base = (void *)xlat_low_va_map(2U * SZ_64K, (MT_RW_DEV | MT_REALM),
						(uintptr_t)smmu->r_base_pa, false);
		if (smmu->r_base == NULL) {
			SMMU_ERROR(smmu, "Failed to map SMMU R base 0x%lx\n",
				   (uintptr_t)smmu->r_base_pa);
			ret = -ENOMEM;
			goto err;
		}

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

		/* Allocate resources dynamically */
		ret = allocate_smmu_resources(smmu);
		if (ret != 0) {
			goto err;
		}

		configure_queue(smmu, CMDQ, smmu->cmdq.q_base_pa);
		configure_queue(smmu, EVTQ, smmu->evtq.q_base_pa);
		configure_strtab(smmu, smmu->strtab_base_pa);

		ret = enable_smmu(smmu);
		if (ret != 0) {
			goto err;
		}

		SMMU_DEBUG("SMMUv3[%lu] initialized and remapped NS base at 0x%lx,"
			   " R base at 0x%lx\n",
			   i, (uintptr_t)smmu->ns_base, (uintptr_t)smmu->r_base);

	}

	g_driver->is_init = true;
	return 0;
err:
	g_driver->num_smmus = 0UL;
	return ret;
}
