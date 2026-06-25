/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors
 */

#include <arch_features.h>
#include <assert.h>
#include <bitmap.h>
#include <errno.h>
#include <granule.h>
#include <mec.h>
#include <mmio.h>
#include <rmm_el3_ifc.h>
#include <smc-rmi.h>
#include <smmuv3.h>
#include <smmuv3_arch.h>
#include <smmuv3_priv.h>
#include <utils_def.h>
#include <xlat_tables.h>

COMPILER_ASSERT_NO_CBMC(STRTAB_L1_STE_MAX == PSMMU_ST_L2_REFCOUNT_MAX);
COMPILER_ASSERT_NO_CBMC(STRTAB_L2_SIZE == GRANULE_SIZE);

/*
 * SMMU_IDR5.OAS, bits [2:0].
 * Size of physical address output from SMMU.
 */
static const unsigned int idr5_oas[] = {
	32U, 36U, 40U, 42U, 44U, 48U, 52U, 56U
};

/*
 * SMMU_IDR5.VAX, bits [11:10].
 * The value 0b11 is reserved; therefore, the last entry is a dummy.
 */
static const unsigned int idr5_vax[] = {48U, 52U, 56U, 0U};

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
 * Calculate the number of bits required for the maximum StreamID.
 * Ensure the result is at least SMMU_STRTAB_SPLIT, the minimum
 * StreamID size required for two-level SMMUv3 Stream Tables.
 */
static unsigned int calc_streamid_bits(unsigned int sid_max)
{
	if (sid_max != 0U) {
		unsigned int bits = 32U - (unsigned int)__builtin_clz(sid_max);

		return MAX(bits, SMMU_STRTAB_SPLIT);
	}

	return SMMU_STRTAB_SPLIT;
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
 *	 must be <= GRANULE_SIZE (typically 4KB).
 */

/* cppcheck-suppress misra-c2012-8.7 */
uintptr_t smmuv3_driver_setup(struct smmu_list *plat_smmu_list,
				uintptr_t *out_pa, size_t *out_sz)
{
	struct smmuv3_dev *smmu;
	struct smmuv3_driv *driver;
	uintptr_t va;
	size_t devs_size, size;
	int ret;

	assert(plat_smmu_list != NULL);
	assert(out_pa != NULL);
	assert(out_sz != NULL);

	/*
	 * Allow driver setup to proceed even if 'num_smmus' is zero.
	 *
	 * In that case, smmuv3_init() will detect the invalid configuration,
	 * return an error, and disable DA accordingly.
	 */
	assert((plat_smmu_list->num_smmus == 0UL) ||
				(plat_smmu_list->smmus != NULL));

	/* Size of SMMUv3 device records */
	devs_size = plat_smmu_list->num_smmus * sizeof(struct smmuv3_dev);

	/*
	 * Ensure the driver structure and all SMMUv3 device records
	 * fit in one granule.
	 */
	size = devs_size + sizeof(struct smmuv3_driv);

	if (size > GRANULE_SIZE) {
		*out_pa = 0UL;
		*out_sz = 0UL;
		ERROR("Not enough space to allocate SMMUv3 data of 0x%lx bytes\n",
			size);
		return 0UL;
	}

	ret = rmm_el3_ifc_reserve_memory(GRANULE_SIZE, 0U, GRANULE_SIZE, out_pa);
	if (ret != 0) {
		ERROR("Failed to reserve memory for smmu_layout\n");
		*out_pa = 0UL;
		*out_sz = 0UL;
		return 0UL;
	}

	va = smmuv3_arch_map(GRANULE_SIZE, MT_RW_DATA | MT_REALM, *out_pa, true);
	if (va == 0UL) {
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

	/* Setup smmuv3_dev array after `smmuv3_driver` */
	driver->smmuv3_devs = (struct smmuv3_dev *)((uintptr_t)driver +
						 sizeof(struct smmuv3_driv));

	/* Init smmuv3_dev fields based on SMMU info structures */
	smmu = driver->smmuv3_devs;
	for (uint64_t i = 0UL; i < plat_smmu_list->num_smmus; i++) {
		unsigned int sid_max;

		/* Get the top of BDF mappings (inclusive) */
		if (rmm_el3_ifc_sid_max((unsigned int)i, &sid_max) != E_RMM_OK) {
			ERROR("Invalid SMMU info data\n");
			return 0UL;
		}

		/* Calculate the maximum number of bits in StreamID */
		smmu[i].strtab_sid_bits = calc_streamid_bits(sid_max);

		smmu[i].ns_base_pa = plat_smmu_list->smmus[i].smmu_base;
		smmu[i].r_base_pa = plat_smmu_list->smmus[i].smmu_r_base;
		SMMU_DEBUG("SMMUv3[%lu]: NS base addr: 0x%lx, R base addr: 0x%lx\n",
			   i, smmu[i].ns_base_pa, smmu[i].r_base_pa);
	}

	return va;
}

/* Get address of STE */
static inline struct ste_entry *sid_to_ste(struct smmuv3_dev *smmu, unsigned int sid)
{
	struct l2tab *ptr;

	ptr = (struct l2tab *)smmu_l2tab_va(smmu, (unsigned long)L1STD_IDX(sid));
	assert(ptr != NULL);
	return &ptr->l2tab_entry[L2STE_IDX(sid)];
}

void configure_strtab(struct smmuv3_dev *smmu, uintptr_t strtab_base_pa)
{
	uint32_t reg;
	uint64_t reg64;

	reg  = INPLACE32(STRTAB_BASE_CFG_LOG2SIZE, smmu->strtab_sid_bits);
	reg |= INPLACE32(STRTAB_BASE_CFG_SPLIT, SMMU_STRTAB_SPLIT);
	reg |= INPLACE32(STRTAB_BASE_CFG_FMT, TWO_LVL_STR_TABLE);
	write32(reg, (void *)(smmu->r_base + SMMU_R_STRTAB_BASE_CFG));

	reg64 = strtab_base_pa | RAWA_BIT;
	write64(reg64, (void *)(smmu->r_base + SMMU_R_STRTAB_BASE));
}

void configure_queue(struct smmuv3_dev *smmu, enum queue_type type,
			uintptr_t queue_base_pa)
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

	base_reg = queue_base_pa | RAWA_BIT;
	base_reg |= INPLACE(SMMU_R_BASE_LOG2SIZE, log2size);

	queue->cons_reg = (void *)(smmu->r_base + cons_offset);
	queue->prod_reg = (void *)(smmu->r_base + prod_offset);

	write64(base_reg, (void *)(smmu->r_base + base_offset));

	/* Queue RD/WR indexes = 0 */
	write32(0U, queue->cons_reg);
	write32(0U, queue->prod_reg);
}

static int init_config(struct smmuv3_dev *smmu)
{
	uint32_t idr1 = read32((void *)(smmu->ns_base + SMMU_IDR1));
	unsigned int log2size;
	unsigned long num_l1_ents;
	size_t size;

	if ((idr1 & (IDR1_QUEUES_PRESET_BIT | IDR1_TABLES_PRESET_BIT)) != 0U) {
		SMMU_ERROR(smmu,
			"Driver doesn't support TABLES_PRESET and QUEUES_PRESET\n");
		return -ENOTSUP;
	}

	/* Command queue */
	/* cppcheck-suppress misra-c2012-12.2 */
	log2size = EXTRACT32(IDR1_CMDQS, idr1);

	/* Limit the queue size to the configured maximum */
	if (log2size > SMMU_MAX_LOG2_CMDQ_SIZE) {
		log2size = SMMU_MAX_LOG2_CMDQ_SIZE;
	}

	/* Use hardware-detected value bounded by max */
	smmu->config.cmdq_log2size = log2size;
	size = (1UL << log2size) * CMD_RECORD_SIZE;
	smmu->cmdq_size = round_up(size, GRANULE_SIZE);
	SMMU_DEBUG("\tCMDQ log2 %u size 0x%lx\n",
			smmu->config.cmdq_log2size, smmu->cmdq_size);

	/* Event queue */
	/* cppcheck-suppress misra-c2012-12.2 */
	log2size = EXTRACT32(IDR1_EVTQS, idr1);

	/* Limit the queue size to the configured maximum */
	if (log2size > SMMU_MAX_LOG2_EVTQ_SIZE) {
		log2size = SMMU_MAX_LOG2_EVTQ_SIZE;
	}

	/* Use hardware-detected value bounded by max */
	smmu->config.evtq_log2size = log2size;
	size = (1UL << log2size) * EVT_RECORD_SIZE;
	smmu->evtq_size = round_up(size, GRANULE_SIZE);
	SMMU_DEBUG("\tEVTQ log2 %u size 0x%lx\n",
		smmu->config.evtq_log2size, smmu->evtq_size);

	/* Max bits of SubstreamID */
	/* cppcheck-suppress misra-c2012-12.2 */
	log2size = EXTRACT32(IDR1_SSIDSIZE, idr1);

	smmu->config.substreamid_bits = log2size;
	SMMU_DEBUG("\tSubstreamID max bits %u\n", log2size);

	/* Max bits of StreamID */
	/* cppcheck-suppress misra-c2012-12.2 */
	log2size = EXTRACT32(IDR1_SIDSIZE, idr1);

	/* Get hardware-detected value */
	smmu->config.streamid_bits = log2size;
	SMMU_DEBUG("\tStreamID max bits %u\n", log2size);

	if (smmu->config.streamid_bits < SMMU_STRTAB_SPLIT) {
		SMMU_ERROR(smmu, "StreamID max bits %u < SMMU_STRTAB_SPLIT %u\n",
				smmu->config.streamid_bits, SMMU_STRTAB_SPLIT);
		return -ENOTSUP;
	}

	/*
	 * Check against the maximum number of bits in StreamID
	 * obtained from the BDF scan.
	 */
	if (smmu->config.streamid_bits < smmu->strtab_sid_bits) {
		SMMU_ERROR(smmu, "StreamID max bits %u < BDF SID size %u\n",
				smmu->config.streamid_bits, smmu->strtab_sid_bits);
		return -ENOTSUP;
	}

	/* Use calculated value derived from the platform confgiration */
	num_l1_ents = (1UL << (smmu->strtab_sid_bits - SMMU_STRTAB_SPLIT));
	size = num_l1_ents * STRTAB_L1_DESC_SIZE;
	smmu->strtab_size = round_up(size, GRANULE_SIZE);

	SMMU_DEBUG("\tNumber of L1 Stream Table entries %lu, size 0x%lx\n",
			num_l1_ents, smmu->strtab_size);
	return 0;
}

static int wait_for_ack(struct smmuv3_dev *smmu, uint32_t offset,
			uint32_t mask, uint32_t expected)
{
	return smmuv3_arch_wait_for_ack(smmu->r_base, offset, mask, expected);
}

static int check_cmdq_err(struct smmuv3_dev *smmu)
{
	uint32_t gerror_reg = read32((void *)(smmu->r_base + SMMU_R_GERROR));
	uint32_t gerror_n_reg = read32((void *)(smmu->r_base + SMMU_R_GERRORN));
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
	write32(gerror_n_reg, (void *)(smmu->r_base + SMMU_R_GERRORN));

	return -EIO;
}

int wait_cmdq_empty(struct smmuv3_dev *smmu)
{
	uint32_t prod_reg, cons_reg;
	unsigned int retries = 0U;

	assert(smmu->cmdq.prod_reg != NULL);
	assert(smmu->cmdq.cons_reg != NULL);

	/* On fake_host, simulate instant command processing */
	smmuv3_arch_sync_cmdq(smmu->cmdq.prod_reg, smmu->cmdq.cons_reg);

	prod_reg = read32(smmu->cmdq.prod_reg);

	/* Wait until Command queue is empty */
	do {
		cons_reg = read32(smmu->cmdq.cons_reg);

		/*
		 * The SMMU_R_GERROR.CMDQ_ERR global error has already been checked
		 * and is not active.
		 *
		 * Therefore, the value in SMMU_R_CMDQ_CONS.ERR bits [30:24] is UNKNOWN
		 * and may be masked.
		 */
		cons_reg &= ~MASK32(CMDQ_CONS_ERR);

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

		/*
		 * Wait for a wake-up event generated by CMD_SYNC, if the SMMU
		 * and system support WFE wake-up events.
		 *
		 * Note: with WFE, an iteration may block until an event occurs,
		 * including a spurious wake-up. Therefore, MAX_RETRIES is a bound
		 * on the number of wake-up attempts, not on a fixed busy-spin duration.
		 */
		if ((smmu->config.features & FEAT_SEV) != 0U) {
			wfe();
		}

	} while (++retries < MAX_RETRIES);

	SMMU_ERROR(smmu, "Timeout processing commands CONS: 0x%x PROD: 0x%x\n",
			cons_reg, prod_reg);
	return -ETIMEDOUT;
}

static int send_cmd(struct smmuv3_dev *smmu, uint128_t cmd)
{
	uint32_t wrap_bit = U(1) << smmu->config.cmdq_log2size;
	uint32_t prod_reg;
	unsigned int retries = MAX_RETRIES;

	assert(smmu_va_is_committed(smmu->cmdq.q_base));
	assert(smmu->cmdq.prod_reg != NULL);
	assert(smmu->cmdq.cons_reg != NULL);

	prod_reg = read32(smmu->cmdq.prod_reg);

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
		/*
		 * Send an event to the PE (similar to SEV)
		 * if the SMMU and system support WFE wake-up events.
		 */
		if ((smmu->config.features & FEAT_SEV) != 0U) {
			cmd |= (uint128_t)COMPOSE(CS, SIG_SEV);
		} else {
			cmd |= (uint128_t)COMPOSE(CS, SIG_NONE);
		}
		FALLTHROUGH;
	case CMD_TLBI_EL2_ALL:
		FALLTHROUGH;
	case CMD_TLBI_NSNH_ALL:
		break;
	case CMD_TLBI_S2_IPA:
		cmd |= (uint128_t)param0;
		cmd |= (uint128_t)param1 << 64;
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

int inval_cached_ste(struct smmuv3_dev *smmu, unsigned long sid,
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

static void clear_ste(struct ste_entry *ste_ptr)
{
	assert(ste_ptr != NULL);

	ste_ptr->ste[0] = 0UL;
	ste_ptr->ste[1] = 0UL;
	ste_ptr->ste[2] = 0UL;
	ste_ptr->ste[3] = 0UL;
	ste_ptr->ste[4] = 0UL;
	dsb(ish);
}

static void configure_ste(struct ste_entry *ste_ptr,
			  const struct smmu_stg2_config *s2_cfg)
{
	unsigned long ds, sl2;

	assert(ste_ptr != NULL);
	assert(s2_cfg != NULL);

	ds = EXTRACT(VTCR_DS, s2_cfg->vtcr);
	sl2 = EXTRACT(VTCR_SL2, s2_cfg->vtcr);

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
			/*
			 * Program STE[178:160] fields:
			 *   S2PS, S2TG, S2SH0, S2OR0, S2IR0, S2SL0, S2T0SZ
			 * using the corresponding VTCR_EL2[18:0] fields:
			 *   PS, TG0, SH0, ORGN0, IRGN0, SL0, T0SZ.
			 */
			  COMPOSE(STE2_VTCR, s2_cfg->vtcr) |
			  STE2_S2PTW_BIT | STE2_S2AA64_BIT | STE2_S2R_BIT;
	/* STE[255:192] */
	ste_ptr->ste[3] = INPLACE(STE3_S2SL0_2, sl2) | INPLACE(STE3_S2DS, ds) |
			  INPLACE(STE3_S2TTB, s2_cfg->s2ttb >> STE3_S2TTB_SHIFT);
	/* STE[319:256] */
	if (is_feat_mec_present()) {
		ste_ptr->ste[4] = INPLACE(STE4_MECID,
					(unsigned long)s2_cfg->mecid);
	}

	SMMU_DEBUG("STE[319:0] %lx:%lx:%lx:%lx:%lx\n",
			ste_ptr->ste[4], ste_ptr->ste[3],
			ste_ptr->ste[2], ste_ptr->ste[1], ste_ptr->ste[0]);
	dsb(ish);
}

static int inval_cfg_tlbs(struct smmuv3_dev *smmu)
{
	int ret;

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

/*
 * Initialize and enable the SMMUv3 device.
 *
 * This function programs the core control registers, configures optional
 * features (such as BTM and MEC), and brings the SMMU into an operational
 * state. It performs the following steps:
 *   - Programs CR1/CR2 with initial configuration.
 *   - Optionally enables broadcast TLB maintenance behaviour (BTM).
 *   - Configures MECID for Realm accesses if supported.
 *   - Enables the Command Queue (CMDQ) and waits for acknowledgment.
 *   - Enables the Event Queue (EVTQ) and waits for acknowledgment.
 *   - Invalidates cached configurations and TLBs.
 *   - Enables SMMU translation (SMMUEN) and waits for acknowledgment.
 *
 * Returns:
 *   0 on success, or a negative error code if any step fails.
 */
int smmu_on(struct smmuv3_dev *smmu)
{
	uint32_t cr0, cr2 = SMMU_R_CR2_INIT;
	int ret;

	assert(smmu != NULL);
	assert(smmu->r_base != 0UL);

	write32(SMMU_R_CR1_INIT, (void *)(smmu->r_base + SMMU_R_CR1));

	if ((smmu->config.features & FEAT_BTM) != 0U) {
		/*
		 * 1: The SMMU is not required to invalidate
		 * any local TLB entries on receipt of broadcast
		 * TLB maintenance operations for Realm translation regimes.
		 */
		cr2 |= R_CR2_PTM_BIT;
	}
	write32(cr2, (void *)(smmu->r_base + SMMU_R_CR2));

	/*
	 * Configure the MECID value for global SMMU-originated accesses to
	 * the Realm PA space, if MEC for the Realm programming interface is
	 * supported.
	 */
	if (is_feat_mec_present()) {
		write32(RESERVED_MECID_SYSTEM, (void *)(smmu->r_base + SMMU_R_GMECID));
	}

	cr0 = SMMU_R_CR0_INIT | R_CR0_CMDQEN_BIT;

	/* Initialise and enable the Command queue */
	write32(cr0, (void *)(smmu->r_base + SMMU_R_CR0));
	ret = wait_for_ack(smmu, SMMU_R_CR0ACK, cr0, cr0);
	if (ret != 0) {
		SMMU_ERROR(smmu, "Failed to enable %s\n", "CMDQ");
		return ret;
	}

	cr0 |= R_CR0_EVTQEN_BIT;

	/* Enable the Event queue */
	write32(cr0, (void *)(smmu->r_base + SMMU_R_CR0));
	ret = wait_for_ack(smmu, SMMU_R_CR0ACK, R_CR0ACK_EVTQEN_BIT, cr0);
	if (ret != 0) {
		SMMU_ERROR(smmu, "Failed to enable %s\n", "EVTQ");
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
	write32(cr0, (void *)(smmu->r_base + SMMU_R_CR0));
	ret = wait_for_ack(smmu, SMMU_R_CR0ACK, R_CR0ACK_SMMUEN_BIT, cr0);
	if (ret != 0) {
		SMMU_ERROR(smmu, "Failed to enable, %d\n", ret);
	}
	return ret;
}

void smmu_off(struct smmuv3_dev *smmu)
{
	uint32_t cr0;
	int ret;

	assert(smmu != NULL);

	/*
	 * Best-effort deactivation: log errors but continue through
	 * all steps to ensure the SMMU is fully disabled.
	 */

	ret = prepare_send_command(smmu, CMD_SYNC, 0UL, 0UL);
	if (ret != 0) {
		SMMU_ERROR(smmu, "Failed to send CMD_%s\n", "SYNC");
	}

	if (ret == 0) {
		ret = wait_cmdq_empty(smmu);
	}

	if (ret == 0) {
		/* Invalidate cached configurations and TLBs */
		ret = inval_cfg_tlbs(smmu);
		if (ret != 0) {
			SMMU_ERROR(smmu, "Failed to invalidate TLBs\n");
		}
	}

	cr0 = read32((void *)(smmu->r_base + SMMU_R_CR0));

	/* Disable SMMU translation */
	cr0 &= ~R_CR0_SMMUEN_BIT;
	write32(cr0, (void *)(smmu->r_base + SMMU_R_CR0));
	ret = wait_for_ack(smmu, SMMU_R_CR0ACK, R_CR0ACK_SMMUEN_BIT, cr0);
	if (ret != 0) {
		SMMU_ERROR(smmu, "Failed to disable, %d\n", ret);
	}

	/* Disable the Command queue */
	cr0 &= ~R_CR0_CMDQEN_BIT;
	write32(cr0, (void *)(smmu->r_base + SMMU_R_CR0));
	ret = wait_for_ack(smmu, SMMU_R_CR0ACK, cr0, cr0);
	if (ret != 0) {
		SMMU_ERROR(smmu, "Failed to disable %s\n", "CMDQ");
	}

	/* Disable the Event queue */
	cr0 &= ~R_CR0_EVTQEN_BIT;
	write32(cr0, (void *)(smmu->r_base + SMMU_R_CR0));
	ret = wait_for_ack(smmu, SMMU_R_CR0ACK, R_CR0ACK_EVTQEN_BIT, cr0);
	if (ret != 0) {
		SMMU_ERROR(smmu, "Failed to disable %s\n", "EVTQ");
	}
}

static int disable_smmu(struct smmuv3_dev *smmu)
{
	uint32_t cr0;
	int ret;

	assert(smmu != NULL);
	cr0 = read32((void *)(smmu->r_base + SMMU_R_CR0));
	cr0 &= ~R_CR0_SMMUEN_BIT;

	write32(cr0, (void *)(smmu->r_base + SMMU_R_CR0));
	ret = wait_for_ack(smmu, SMMU_R_CR0ACK, R_CR0ACK_SMMUEN_BIT, cr0);
	if (ret != 0) {
		SMMU_ERROR(smmu, "Failed to disable, %d\n", ret);
	}
	return ret;
}

static int get_features(struct smmuv3_dev *smmu)
{
	uint32_t aidr, idr0, idr3 __unused, idr5, r_idr0, r_idr3;
	uint32_t val;

	/* All configuration features are cleared as part of initialisation */

	aidr = read32((void *)(smmu->ns_base + SMMU_AIDR));
	/* cppcheck-suppress misra-c2012-12.2 */
	val = EXTRACT32(AIDR_ARCH_MINOR_REV, aidr);
	smmu->config.minor_rev = val;
	SMMU_DEBUG("SMMUv3: architecture revision 3.%u\n", val);

	idr0 = read32((void *)(smmu->ns_base + SMMU_IDR0));
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
		SMMU_ERROR(smmu, "VMID wildcard-matching not supported\n");
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
		SMMU_ERROR(smmu, "16-bit VMID not supported\n");
		return -ENOTSUP;
	}

	if ((idr0 & IDR0_SEV_BIT) != 0U) {
		smmu->config.features |= FEAT_SEV;
		SMMU_DEBUG("\tSEV\n");
	}

	/*
	 * Range-based invalidation and level hint are mandatory
	 * for implementations of SMMUv3.2 or later.
	 */
	idr3 = read32((void *)(smmu->ns_base + SMMU_IDR3));
	assert((idr3 & IDR3_RIL_BIT) != 0U);

	idr5 = read32((void *)(smmu->ns_base + SMMU_IDR5));
	if ((idr5 & IDR5_GRAN4K_BIT) == 0U) {
		SMMU_ERROR(smmu, "4KB translation granule not supported\n");
		return -ENOTSUP;
	}

	assert(EXTRACT32(IDR5_VAX, idr5) <= IDR5_VAX_56_MAX);
	SMMU_DEBUG("\tVirtual Address eXtend %u bits\n",
			idr5_vax[EXTRACT32(IDR5_VAX, idr5)]);

	if ((idr5 & IDR5_DS_BIT) != 0U) {
		smmu->config.features |= FEAT_DS;
		SMMU_DEBUG("\tDS\n");
	}

	val = EXTRACT32(IDR5_OAS, idr5);

	if (((smmu->config.features & FEAT_DS) != 0U) && (val >= IDR5_OAS_52)) {
		SMMU_DEBUG("\t52-bit address sizes supported\n");
	} else if (is_feat_lpa2_4k_2_present()) {
		SMMU_ERROR(smmu, "52-bit address sizes not supported\n");
		return -ENOTSUP;
	}

	/* Size of physical address output from SMMU */
	smmu->config.pa_size = idr5_oas[val];
	SMMU_DEBUG("\tOutput address size %u bits\n", smmu->config.pa_size);

	/*
	 * Check that 128-bit VMSAv9-128 descriptors are supported
	 * by both the PE and the SMMUv3.
	 */
	if ((idr5 & IDR5_D128_BIT) != 0U) {
		smmu->config.features |= FEAT_D128;
		SMMU_DEBUG("\tD128\n");
	} else if (is_feat_d128_present()) {
		SMMU_ERROR(smmu, "VMSAv9-128 descriptors not supported\n");
		return -ENOTSUP;
	}

	r_idr0 = read32((void *)(smmu->r_base + SMMU_R_IDR0));

	/* When SMMU_IDR0.ATS = 0, SMMU_IDR0.PRI field is RES0 */
	if ((r_idr0 & R_IDR0_ATS_BIT) != 0U) {
		smmu->config.features |= FEAT_ATS;
		SMMU_DEBUG("\tPCIe ATS\n");
	}

	if ((r_idr0 & R_IDR0_MSI_BIT) != 0U) {
		smmu->config.features |= FEAT_MSI;
		SMMU_DEBUG("\tMSI\n");
	}

	if ((r_idr0 & R_IDR0_PRI_BIT) != 0U) {
		smmu->config.features |= FEAT_PRI;
		SMMU_DEBUG("\tPRI\n");
	}

	r_idr3 = read32((void *)(smmu->r_base + SMMU_R_IDR3));
	if ((r_idr3 & R_IDR3_DPT_BIT) != 0U) {
		smmu->config.features |= FEAT_DPT;
		SMMU_DEBUG("\tDPT\n");
	}

	if ((r_idr3 & R_IDR3_MEC_BIT) != 0U) {
		SMMU_DEBUG("\tMEC\n");
	} else if (is_feat_mec_present()) {
		SMMU_ERROR(smmu, "MEC not supported\n");
		return -ENOTSUP;
	}

	if (is_feat_mec_present()) {
		uint32_t r_mecidr = read32((void *)(smmu->r_base + SMMU_R_MECIDR));
		unsigned int mecidwidth = (unsigned int)EXTRACT(MECIDR_MECIDWIDTHM1,
							read_mecidr_el2());
		unsigned int smmu_mecidwidth = EXTRACT32(SMMU_R_MECIDR_MECIDSIZE, r_mecidr);

		/*
		 * Check that MECID bit width supported by the SMMU matches
		 * or exceeds the width supported by the PEs in the system.
		 */
		if (smmu_mecidwidth < mecidwidth) {
			SMMU_ERROR(smmu,
				"SMMU_R_MECIDR.MECIDSIZE %u < MECIDR_EL2.MECIDWidthm1 %u\n",
				smmu_mecidwidth, mecidwidth);
			return -ENOTSUP;
		}
	}

	return 0;
}

struct smmuv3_dev *get_by_index(unsigned int smmu_idx, unsigned int sid)
{
	struct smmuv3_dev *smmu;

	assert(g_driver != NULL);

	/* The caller is responsible to ensure that SMMU index and SID are valid */
	if (smmu_idx >= (unsigned int)g_driver->num_smmus) {
		SMMU_DEBUG("SMMUv3: Illegal SMMU ID %u\n", smmu_idx);
		return NULL;
	}

	assert(g_smmus != NULL);
	smmu = &g_smmus[smmu_idx];

	if (sid >= (U(1) << smmu->strtab_sid_bits)) {
		SMMU_DEBUG("Illegal StreamID 0x%x\n", sid);
		return NULL;
	}

	return smmu;
}

static int change_ste(unsigned int smmu_idx, unsigned int sid, bool enable)
{
	struct smmuv3_dev *smmu;
	struct ste_entry *ste_ptr;
	unsigned int l1_idx;
	bool valid;
	int ret;

	smmu = get_by_index(smmu_idx, sid);
	if (smmu == NULL) {
		return -EINVAL;
	}

	/* L1STD index in L1 table */
	l1_idx = L1STD_IDX(sid);

	spinlock_acquire(&smmu->lock);

	if (smmu->state != PSMMU_ACTIVE) {
		SMMU_ERROR(smmu, "PSMMU not active (state=%u) for SID 0x%x\n",
				smmu->state, sid);
		spinlock_release(&smmu->lock);
		return -EINVAL;
	}

	assert(smmu_va_is_committed(smmu->strtab_base));

	/* Check that L2 table is allocated */
	if (smmu->strtab_base[l1_idx] == 0UL) {
		spinlock_release(&smmu->lock);
		SMMU_ERROR(smmu, "STRTAB L2 for SID 0x%x not found\n", sid);
		return -EINVAL;
	}

	ste_ptr = sid_to_ste(smmu, sid);
	assert(ste_ptr != NULL);

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

int smmuv3_release_ste(unsigned int smmu_idx, unsigned int sid)
{
	struct smmuv3_dev *smmu;
	struct ste_entry *ste_ptr;
	struct granule *g_l2tab;
	unsigned int l1_idx;
	uintptr_t l2tab_pa;
	int ret;

	SMMU_DEBUG("%s(0x%x)\n", __func__, sid);

	smmu = get_by_index(smmu_idx, sid);
	if (smmu == NULL) {
		return -EINVAL;
	}

	/* L1STD index in L1 table */
	l1_idx = L1STD_IDX(sid);

	spinlock_acquire(&smmu->lock);

	if (smmu->state != PSMMU_ACTIVE) {
		SMMU_ERROR(smmu, "PSMMU not active (state=%u) for SID 0x%x\n",
				smmu->state, sid);
		spinlock_release(&smmu->lock);
		return -EINVAL;
	}

	assert(smmu_va_is_committed(smmu->strtab_base));

	/* Check that L2 table was allocated */
	if (smmu->strtab_base[l1_idx] == 0UL) {
		spinlock_release(&smmu->lock);
		SMMU_ERROR(smmu, "STRTAB L2 for SID 0x%x not found\n", sid);
		return -EINVAL;
	}

	l2tab_pa = smmu_l1std_l2tab_pa(smmu, l1_idx);
	g_l2tab = find_lock_granule(l2tab_pa, GRANULE_STATE_PSMMU_ST_L2);
	assert(g_l2tab != NULL);

	if (granule_refcount_read(g_l2tab) == 0U) {
		granule_unlock(g_l2tab);
		spinlock_release(&smmu->lock);
		SMMU_ERROR(smmu, "No STEs in STRTAB L2 for SID 0x%x\n", sid);
		return -EINVAL;
	}

	ste_ptr = sid_to_ste(smmu, sid);
	assert(ste_ptr != NULL);

	/* Check that STE is not valid, e.g. smmuv3_disable_ste() was called */
	if ((ste_ptr->ste[0] & STE0_V_BIT) != 0UL) {
		granule_unlock(g_l2tab);
		spinlock_release(&smmu->lock);
		SMMU_ERROR(smmu, "Cannot release valid STE with SID 0x%x\n", sid);
		return -EINVAL;
	}

	/*
	 * STE is not valid, STE.V == 0.
	 * Ensure that the context can no longer be used.
	 * Clear S2 STE fields.
	 */
	clear_ste(ste_ptr);

	/* Decrement number of configured STEs */
	atomic_granule_put(g_l2tab);
	granule_unlock(g_l2tab);

	/* Invalidate configuration structure */
	ret = inval_cached_ste(smmu, sid, true);
	spinlock_release(&smmu->lock);
	return ret;
}

int smmuv3_enable_ste(unsigned int smmu_idx, unsigned int sid)
{
	SMMU_DEBUG("%s(0x%x)\n", __func__, sid);

	return change_ste(smmu_idx, sid, true);
}

int smmuv3_disable_ste(unsigned int smmu_idx, unsigned int sid)
{
	SMMU_DEBUG("%s(0x%x)\n", __func__, sid);

	return change_ste(smmu_idx, sid, false);
}

int smmuv3_configure_stream(unsigned long ecam_addr, unsigned int tdi_id,
			    struct smmu_stg2_config *s2_cfg,
			    unsigned int *sid_ptr, unsigned int *idx_ptr)
{
	struct smmuv3_dev *smmu;
	struct ste_entry *ste_ptr;
	struct granule *g_l2tab;
	unsigned int l1_idx, smmu_idx, sid;
	uintptr_t l2tab_pa;
	int ret;

	assert(s2_cfg != NULL);
	assert(sid_ptr != NULL);
	assert(idx_ptr != NULL);

	SMMU_DEBUG("%s(0x%lx, 0x%x) s2ttb 0x%lx vtcr 0x%lx vmid 0x%x mecid 0x%x\n",
			__func__, ecam_addr, tdi_id, s2_cfg->s2ttb, s2_cfg->vtcr,
			s2_cfg->vmid, s2_cfg->mecid);

	if (rmm_el3_ifc_bdf_to_smmu(ecam_addr, tdi_id, &smmu_idx, &sid) != E_RMM_OK) {
		ERROR("TDI id 0x%x not found\n", tdi_id);
		return -EINVAL;
	}

	smmu = get_by_index(smmu_idx, sid);
	if (smmu == NULL) {
		return -EINVAL;
	}

	assert((s2_cfg->vmid < (U(1) << 8)) ||
		((smmu->config.features & FEAT_VMID16) != 0U));

	/* L1STD index in L1 table */
	l1_idx = L1STD_IDX(sid);

	spinlock_acquire(&smmu->lock);

	/* Check that PSMMU is active (stream table allocated and SMMU enabled) */
	if (smmu->state != PSMMU_ACTIVE) {
		SMMU_ERROR(smmu, "PSMMU not active (state=%u) for SID 0x%x\n",
				smmu->state, sid);
		spinlock_release(&smmu->lock);
		return -EINVAL;
	}

	assert(smmu_va_is_committed(smmu->strtab_base));

	/* Check that L2 table is allocated */
	if (smmu->strtab_base[l1_idx] == 0UL) {
		spinlock_release(&smmu->lock);
		SMMU_ERROR(smmu, "STRTAB L2 for SID 0x%x not found\n", sid);
		return -EINVAL;
	}

	ste_ptr = sid_to_ste(smmu, sid);
	assert(ste_ptr != NULL);

	/* Check that STE is not already set */
	if (ste_ptr->ste[0] != 0UL) {
		spinlock_release(&smmu->lock);
		SMMU_ERROR(smmu, "STE for SID 0x%x already configured\n", sid);
		return -EINVAL;
	}

	l2tab_pa = smmu_l1std_l2tab_pa(smmu, l1_idx);
	g_l2tab = find_lock_granule(l2tab_pa, GRANULE_STATE_PSMMU_ST_L2);
	assert(g_l2tab != NULL);

	assert(granule_refcount_read(g_l2tab) < STRTAB_L1_STE_MAX);
	/* Increment number of configured STEs */
	atomic_granule_get(g_l2tab);
	granule_unlock(g_l2tab);

	configure_ste(ste_ptr, s2_cfg);

	/* Invalidate configuration structure */
	ret = inval_cached_ste(smmu, sid, true);
	if (ret == 0) {
		*sid_ptr = sid;
		*idx_ptr = smmu_idx;
	} else {
		clear_ste(ste_ptr);

		/* Roll back the refcount taken before writing the STE fields */
		atomic_granule_put_release(g_l2tab);
	}

	spinlock_release(&smmu->lock);
	return ret;
}

int smmuv3_init(uintptr_t driv_hdl, size_t hdl_sz)
{
	struct smmuv3_dev *smmu;
	unsigned long num_smmus;
	unsigned long num_l1_ents;
	uintptr_t reserved_va;
	int ret;

	if ((driv_hdl == 0U) || (hdl_sz < sizeof(struct smmuv3_driv))) {
		SMMU_DEBUG("Invalid SMMUv3 driver handle\n");
		return -EINVAL;
	}

	assert(g_driver == NULL);

	g_driver = (struct smmuv3_driv *)driv_hdl;

	if (g_driver->is_init) {
		SMMU_DEBUG("SMMUv3 driver already initialized\n");
		return 0;
	}

	num_smmus = g_driver->num_smmus;

	/* No SMMUs in the system */
	if (num_smmus == 0UL) {
		return -ENODEV;
	}

	/* Initialize broadcast_tlb to true, will be set to false if any SMMU doesn't support it */
	g_driver->broadcast_tlb = true;

	g_smmus = g_driver->smmuv3_devs;
	assert(g_smmus != NULL);

	/* Init the SMMUv3 instances */
	for (unsigned long i = 0U; i < num_smmus; i++) {
		smmu = &g_smmus[i];

		/* SMMU registers, Page 0 */
		smmu->ns_base = smmuv3_arch_map(SZ_64K, (MT_RW_DEV | MT_NS),
						smmu->ns_base_pa, false);
		if (smmu->ns_base == 0UL) {
			SMMU_ERROR(smmu, "Failed to map SMMU NS base 0x%lx\n",
					smmu->ns_base_pa);
			ret = -ENOMEM;
			goto err;
		}

		/* SMMU registers, Realm Page 0 and 1 */
		smmu->r_base = smmuv3_arch_map(2U * SZ_64K, (MT_RW_DEV | MT_REALM),
						smmu->r_base_pa, false);
		if (smmu->r_base == 0UL) {
			SMMU_ERROR(smmu, "Failed to map SMMU R base 0x%lx\n",
					smmu->r_base_pa);
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

		/* Reserve VA space for runtime structures */

		/* L1 Stream Table */
		ret = smmuv3_arch_reserve(smmu->strtab_size,
						&reserved_va);
		if (ret != 0) {
			SMMU_ERROR(smmu, "Failed to reserve VA for %s\n", "L1 StrTab");
			goto err;
		}
		smmu->strtab_base = (uint64_t *)smmu_va_mark_reserved(reserved_va);

		/* Command queue */
		ret = smmuv3_arch_reserve(smmu->cmdq_size, &reserved_va);
		if (ret != 0) {
			SMMU_ERROR(smmu, "Failed to reserve VA for %s\n", "CMDQ");
			goto err;
		}
		smmu->cmdq.q_base = smmu_va_mark_reserved(reserved_va);

		/* Event queue */
		ret = smmuv3_arch_reserve(smmu->evtq_size, &reserved_va);
		if (ret != 0) {
			SMMU_ERROR(smmu, "Failed to reserve VA for %s\n", "EVTQ");
			goto err;
		}
		smmu->evtq.q_base = smmu_va_mark_reserved(reserved_va);

		/* Number of L2 Tables */
		num_l1_ents = (1UL << (smmu->strtab_sid_bits - SMMU_STRTAB_SPLIT));

		/* L2 Tables pool */
		ret = smmuv3_arch_reserve(num_l1_ents * GRANULE_SIZE, &smmu->l2_pool_va);
		if (ret != 0) {
			SMMU_ERROR(smmu, "Failed to reserve VA for %s\n", "L2 pool");
			goto err;
		}

		smmu->state = PSMMU_INACTIVE;

		SMMU_DEBUG("SMMUv3[%lu] initialized and remapped NS base at 0x%lx,"
			   " R base at 0x%lx\n", i, smmu->ns_base, smmu->r_base);
	}

	g_driver->is_init = true;
	return 0;
err:
	g_driver->num_smmus = 0UL;
	return ret;
}
