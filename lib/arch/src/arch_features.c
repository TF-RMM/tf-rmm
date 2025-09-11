/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch.h>
#include <arch_features.h>
#include <arch_helpers.h>
#include <assert.h>
#include <el3_feat_status.h>
#include <smc.h>
#include <stdint.h>
#include <utils_def.h>

#define WRITE_EL3_FEAT_EN_STATUS(obj, bitmask, value)	((obj).bitmask = (value))
#define READ_EL3_FEAT_EN_STATUS(obj, bitmask)		((obj).bitmask)

/* DEFINE_SYSREG_READ_FUNC(id_aa64afr0_el1) */
/* DEFINE_SYSREG_READ_FUNC(id_aa64afr1_el1) */
DEFINE_SYSREG_READ_FUNC(id_aa64dfr0_el1)
DEFINE_SYSREG_READ_FUNC(id_aa64dfr1_el1)
DEFINE_RENAME_SYSREG_READ_FUNC(id_aa64dfr2_el1, ID_AA64DFR2_EL1)
/* DEFINE_RENAME_SYSREG_READ_FUNC(id_aa64fpfr0_el1, ID_AA64FPFR0_EL1) */
DEFINE_SYSREG_READ_FUNC(id_aa64isar0_el1)
DEFINE_SYSREG_READ_FUNC(id_aa64isar1_el1)
DEFINE_RENAME_SYSREG_READ_FUNC(id_aa64isar2_el1, ID_AA64ISAR2_EL1)
DEFINE_RENAME_SYSREG_READ_FUNC(id_aa64isar3_el1, ID_AA64ISAR3_EL1)
DEFINE_SYSREG_READ_FUNC(id_aa64mmfr0_el1)
DEFINE_SYSREG_READ_FUNC(id_aa64mmfr1_el1)
DEFINE_SYSREG_READ_FUNC(id_aa64mmfr2_el1)
DEFINE_RENAME_SYSREG_READ_FUNC(id_aa64mmfr3_el1, ID_AA64MMFR3_EL1)
DEFINE_RENAME_SYSREG_READ_FUNC(id_aa64mmfr4_el1, ID_AA64MMFR4_EL1)
DEFINE_SYSREG_READ_FUNC(id_aa64pfr0_el1)
DEFINE_SYSREG_READ_FUNC(id_aa64pfr1_el1)
DEFINE_RENAME_SYSREG_READ_FUNC(id_aa64pfr2_el1, ID_AA64PFR2_EL1)
/* DEFINE_RENAME_SYSREG_READ_FUNC(id_aa64smfr0_el1, ID_AA64SMFR0_EL1) */
DEFINE_RENAME_SYSREG_READ_FUNC(id_aa64zfr0_el1, ID_AA64ZFR0_EL1)

static struct el3_feat_en_status el3_feat_enb_status = {
	.scr_bitmask = UINT64_MAX,
	.cptr_bitmask = UINT64_MAX,
	.mdcr_bitmask = UINT64_MAX,
	.mpam3_bitmask = UINT64_MAX
};

/* cppcheck-suppress misra-c2012-8.4 */
struct cached_idreg_info cached_idreg = {0};

/*
 * Cache the ID registers and enable support only for the features
 * available in R-EL2. R-EL1 accesses only the cached values and,
 * as a result, can only detect the features supported by R-EL2.
 */
static void update_id_aa64dfr0_el1(struct cached_idreg_info *ptr)
{
	unsigned long value;

	assert(ptr != NULL);

	/*************************************************************
	 * Cache and update IDAA64DFR0_EL1 based on supported features
	 * Bit[55-52] - BRBE
	 * Bit[47-44] - TraceBuffer
	 * Bit[43-40] - TraceFilt
	 * Bit[35-32] - PMSVer
	 * Bit[11-8]  - PMUVer
	 **************************************************************/

	value = READ_EL3_FEAT_EN_STATUS(el3_feat_enb_status, mdcr_bitmask);

	if (EXTRACT_BIT(SMC_FEAT_MDCR_BRBE, value) == 0U) {
		ptr->id_aa64dfr0_el1 &= ~MASK(ID_AA64DFR0_EL1_BRBE);
	}
}

static void update_id_aa64mmfr0_el1(struct cached_idreg_info *ptr)
{
	unsigned long value;

	assert(ptr != NULL);

	value = READ_EL3_FEAT_EN_STATUS(el3_feat_enb_status, scr_bitmask);

	/*************************************************************
	 * Cache and update IDAA64MMFR0_EL1 based on supported features
	 * Bit[59-56] - FEAT_FGT/FEAT_FGT2
	 **************************************************************/

	if ((EXTRACT_BIT(SMC_FEAT_SCR_FGT, value) == 0U) &&
		(EXTRACT_BIT(SMC_FEAT_SCR_FGT2, value) == 0U)) {
		ptr->id_aa64mmfr0_el1 &= ~MASK(ID_AA64MMFR0_EL1_FGT);
	}
}

static void update_id_aa64mmfr3_el1(struct cached_idreg_info *ptr)
{
	unsigned long value;

	assert(ptr != NULL);

	value = READ_EL3_FEAT_EN_STATUS(el3_feat_enb_status, scr_bitmask);

	/*************************************************************
	 * Cache and update IDAA64MMFR3_EL1 based on supported features
	 * Bit[19-16] - S1POE
	 * Bit[11-8]  - S1PIE
	 * Bit[7-4] - SCTLRx
	 * Bit[3-0] - TCRx
	 **************************************************************/

	if (EXTRACT_BIT(SMC_FEAT_SCR_S1PIE, value) == 0U) {
		ptr->id_aa64mmfr3_el1 &= ~MASK(ID_AA64MMFR3_EL1_S1POE);
		ptr->id_aa64mmfr3_el1 &= ~MASK(ID_AA64MMFR3_EL1_S1PIE);
	}

	if (EXTRACT_BIT(SMC_FEAT_SCR_SCTLR2, value) == 0U) {
		ptr->id_aa64mmfr3_el1 &= ~MASK(ID_AA64MMFR3_EL1_SCTLRX);
	}

	if (EXTRACT_BIT(SMC_FEAT_SCR_TCR2, value) == 0U) {
		ptr->id_aa64mmfr3_el1 &= ~MASK(ID_AA64MMFR3_EL1_TCRX);
	}

	if (EXTRACT_BIT(SMC_FEAT_SCR_MEC, value) == 0U) {
		ptr->id_aa64mmfr3_el1 &= ~MASK(ID_AA64MMFR3_EL1_MEC);
	}
}

static void update_id_aa64pfr0_el1(struct cached_idreg_info *ptr)
{

	assert(ptr != NULL);

	unsigned long value;

	/* Read SCR mask value */
	value = READ_EL3_FEAT_EN_STATUS(el3_feat_enb_status, scr_bitmask);

	/*************************************************************
	 * Cache and update IDAA64PFR0_EL1 based on supported features
	 * Bit[56-59] - CSV2
	 * Bit[32-35] - SVE
	 **************************************************************/

	if (EXTRACT_BIT(SMC_FEAT_SCR_CSV2_2, value) == 0U) {
		ptr->id_aa64pfr0_el1 &= ~MASK(ID_AA64PFR0_EL1_CSV2);
	}

	/* Read CPTR mask value */
	value = READ_EL3_FEAT_EN_STATUS(el3_feat_enb_status, cptr_bitmask);

	if (EXTRACT_BIT(SMC_FEAT_CPTR_SVE, value) == 0U) {
		ptr->id_aa64pfr0_el1 &= ~MASK(ID_AA64PFR0_EL1_SVE);
	}
}

static void update_id_aa64pfr1_el1(struct cached_idreg_info *ptr)
{

	assert(ptr != NULL);

	unsigned long value;

	value = READ_EL3_FEAT_EN_STATUS(el3_feat_enb_status, scr_bitmask);

	/*************************************************************
	 * Cache and update IDAA64PFR1_EL1 based on supported features
	 * Bit[27-24] - SME
	 **************************************************************/

	if (EXTRACT_BIT(SMC_FEAT_SCR_SME, value) == 0U) {
		ptr->id_aa64pfr1_el1 &= ~MASK(ID_AA64PFR1_EL1_SME);
	}

	if (EXTRACT_BIT(SMC_FEAT_SCR_RNG_TRAP, value) == 0U) {
		ptr->id_aa64pfr1_el1 &= ~MASK(ID_AA64PFR1_EL1_RNDR_TRAP);
	}
}

/*
 * Update the cached ID registers based on the features supported
 * in EL3. This is determined from the SMCCC_ARCH_FEATURE_AVAILABILITY.
 */

static void update_cached_idreg_info(void)
{

	/*
	 * Some ID regs are to be 0'ed as they are IMPDEF or
	 * corresponds to features which are disabled for Realm World.
	 */
	cached_idreg.id_aa64afr0_el1 = 0ULL;
	cached_idreg.id_aa64afr1_el1 = 0ULL;

	cached_idreg.id_aa64dfr0_el1 = ((read_id_aa64dfr0_el1()) & ID_AA64DFR0_EL1_HW_MASK);
	cached_idreg.id_aa64dfr1_el1 = ((read_id_aa64dfr1_el1()) & ID_AA64DFR1_EL1_HW_MASK);
	cached_idreg.id_aa64dfr2_el1 = ((read_id_aa64dfr2_el1()) & ID_AA64DFR2_EL1_HW_MASK);

	cached_idreg.id_aa64fpfr0_el1 = 0ULL;

	cached_idreg.id_aa64isar0_el1 = ((read_id_aa64isar0_el1()) & ID_AA64ISAR0_EL1_HW_MASK);
	cached_idreg.id_aa64isar1_el1 = ((read_id_aa64isar1_el1()) & ID_AA64ISAR1_EL1_HW_MASK);
	cached_idreg.id_aa64isar2_el1 = ((read_id_aa64isar2_el1()) & ID_AA64ISAR2_EL1_HW_MASK);
	cached_idreg.id_aa64isar3_el1 = ((read_id_aa64isar3_el1()) & ID_AA64ISAR3_EL1_HW_MASK);

	cached_idreg.id_aa64mmfr0_el1 = ((read_id_aa64mmfr0_el1()) & ID_AA64MMFR0_EL1_HW_MASK);
	cached_idreg.id_aa64mmfr1_el1 = ((read_id_aa64mmfr1_el1()) & ID_AA64MMFR1_EL1_HW_MASK);
	cached_idreg.id_aa64mmfr2_el1 = ((read_id_aa64mmfr2_el1()) & ID_AA64MMFR2_EL1_HW_MASK);
	cached_idreg.id_aa64mmfr3_el1 = ((read_id_aa64mmfr3_el1()) & ID_AA64MMFR3_EL1_HW_MASK);
	cached_idreg.id_aa64mmfr4_el1 = ((read_id_aa64mmfr4_el1()) & ID_AA64MMFR4_EL1_HW_MASK);

	cached_idreg.id_aa64pfr0_el1 = ((read_id_aa64pfr0_el1()) & ID_AA64PFR0_EL1_HW_MASK);
	cached_idreg.id_aa64pfr1_el1 = ((read_id_aa64pfr1_el1()) & ID_AA64PFR1_EL1_HW_MASK);
	cached_idreg.id_aa64pfr2_el1 = ((read_id_aa64pfr2_el1()) & ID_AA64PFR2_EL1_HW_MASK);

	cached_idreg.id_aa64smfr0_el1 = 0ULL;

	cached_idreg.id_aa64zfr0_el1 = ((read_id_aa64zfr0_el1()) & ID_AA64ZFR0_EL1_HW_MASK);

	/* ID_AA64DFR1_EL1: Update cached copy */
	update_id_aa64dfr0_el1(&cached_idreg);

	/* ID_AA64MMFR0_EL1: Update cached copy */
	update_id_aa64mmfr0_el1(&cached_idreg);

	/* ID_AA64MMFR3_EL1: Update cached copy */
	update_id_aa64mmfr3_el1(&cached_idreg);

	/* ID_AA64PFR0_EL1: Update cached copy */
	update_id_aa64pfr0_el1(&cached_idreg);

	/* ID_AA64PFR1_EL1: Update cached copy */
	update_id_aa64pfr1_el1(&cached_idreg);

}

void arch_features_query_el3_support(void)
{
	unsigned long val;
	struct smc_result smc_res = {0};

	assert(!is_mmu_enabled());

	/* check if arch_feature_availability is supported */
	val = monitor_call(SMCCC_ARCH_FEATURES,
			      SMCCC_ARCH_FEATURE_AVAILABILITY,
			      0UL, 0UL, 0UL, 0UL, 0UL);

	if (val != SMC_SUCCESS) {
		goto smc_failed;
	}
	monitor_call_with_res(SMCCC_ARCH_FEATURE_AVAILABILITY,
			      SCR_EL3_OPCODE,
			      0UL, 0UL, 0UL, 0UL, 0UL,
			      &smc_res);

	if (smc_res.x[0] == SMC_SUCCESS) {
		WRITE_EL3_FEAT_EN_STATUS(el3_feat_enb_status, scr_bitmask, smc_res.x[1]);
	}

	monitor_call_with_res(SMCCC_ARCH_FEATURE_AVAILABILITY,
			      CPTR_EL3_OPCODE,
			      0UL, 0UL, 0UL, 0UL, 0UL,
			      &smc_res);

	if (smc_res.x[0] == SMC_SUCCESS) {
		WRITE_EL3_FEAT_EN_STATUS(el3_feat_enb_status, cptr_bitmask, smc_res.x[1]);
	}

	monitor_call_with_res(SMCCC_ARCH_FEATURE_AVAILABILITY,
			      MDCR_EL3_OPCODE,
			      0UL, 0UL, 0UL, 0UL, 0UL,
			      &smc_res);

	if (smc_res.x[0] == SMC_SUCCESS) {
		WRITE_EL3_FEAT_EN_STATUS(el3_feat_enb_status, mdcr_bitmask, smc_res.x[1]);
	}

	monitor_call_with_res(SMCCC_ARCH_FEATURE_AVAILABILITY,
			      MPAM3_EL3_OPCODE,
			      0UL, 0UL, 0UL, 0UL, 0UL,
			      &smc_res);

	if (smc_res.x[0] == SMC_SUCCESS) {
		WRITE_EL3_FEAT_EN_STATUS(el3_feat_enb_status, mpam3_bitmask, smc_res.x[1]);
	}

smc_failed:
	update_cached_idreg_info();
	inv_dcache_range((uintptr_t)&el3_feat_enb_status, sizeof(el3_feat_enb_status));
	inv_dcache_range((uintptr_t)&cached_idreg, sizeof(cached_idreg));
	return;
}

#ifndef CBMC
/*
 * Return the PA width supported by the current system.
 */
unsigned int arch_feat_get_pa_width(void)
{
	/*
	 * Physical Address ranges supported in the AArch64 Memory Model.
	 * Each array index is a valid PARange [0:3] in ID_AA64MMFR0_EL1.
	 */
	const unsigned int pa_range_bits_arr[] = {
		[0x0] = PARANGE_WIDTH_32BITS,
		[0x1] = PARANGE_WIDTH_36BITS,
		[0x2] = PARANGE_WIDTH_40BITS,
		[0x3] = PARANGE_WIDTH_42BITS,
		[0x4] = PARANGE_WIDTH_44BITS,
		[0x5] = PARANGE_WIDTH_48BITS,
		[0x6] = PARANGE_WIDTH_52BITS
	};

	unsigned long pa_range = EXTRACT(ID_AA64MMFR0_EL1_PARANGE,
					READ_CACHED_REG(id_aa64mmfr0_el1));

	/*
	 * If a valid encoding is not found in the ID reg, default to a
	 * sensible value. This can happen if RMM is running on a version of
	 * Architecture which is not supported yet. If LPA2 is present,
	 * default to 52 bit PA range else to 48 bit PA range. Assume
	 * both Stage 1 and Stage 2 have identical LPA2 support.
	 */
	/* cppcheck-suppress [misra-c2012-17.3] */
	if (pa_range >= ARRAY_SIZE(pa_range_bits_arr)) {
		return (is_feat_lpa2_4k_present() ?
			PARANGE_WIDTH_52BITS : PARANGE_WIDTH_48BITS);
	}

	return pa_range_bits_arr[pa_range];
}
#endif
