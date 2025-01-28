/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef ARCH_FEATURES_H
#define ARCH_FEATURES_H

#include <arch_helpers.h>
#include <stdbool.h>

#define DEFINE_CONDITIONAL_SYSREG_READ_FUNC_(_name, _cond_name,		\
					     _cond_checker, _default)	\
static inline u_register_t read_ ## _name ## _ ## _cond_name(void)	\
{									\
	if (_cond_checker() == true) {					\
		return read_ ## _name();				\
	}								\
	return _default;						\
}

#define DEFINE_CONDITIONAL_SYSREG_WRITE_FUNC_(_name, _cond_name,	\
					      _cond_checker)		\
static inline void write_ ## _name ## _ ## _cond_name(u_register_t v)	\
{									\
	if (_cond_checker() == true) {					\
		write_ ## _name(v);					\
	}								\
}

/* Define conditional read function for system register */
#define DEFINE_CONDITIONAL_SYSREG_READ_FUNC(_name, _cond_name,		\
					    _cond_checker, _default)	\
	DEFINE_CONDITIONAL_SYSREG_READ_FUNC_(_name, _cond_name,		\
					     _cond_checker, _default)

/* Define conditional read & write functions for system register */
#define DEFINE_CONDITIONAL_SYSREG_RW_FUNCS(_name, _cond_name,		\
					   _cond_checker, _default)	\
	DEFINE_CONDITIONAL_SYSREG_READ_FUNC_(_name, _cond_name,		\
					     _cond_checker, _default)	\
	DEFINE_CONDITIONAL_SYSREG_WRITE_FUNC_(_name, _cond_name, _cond_checker)

/*
 * Extract architectural features supported from the ID registers.
 * Values are used to configure runtime behavior based on detected features.
 */
struct cached_idreg_info {
	u_register_t id_aa64afr0_el1;
	u_register_t id_aa64afr1_el1;
	u_register_t id_aa64dfr0_el1;
	u_register_t id_aa64dfr1_el1;
	u_register_t id_aa64dfr2_el1;
	u_register_t id_aa64fpfr0_el1;
	u_register_t id_aa64isar0_el1;
	u_register_t id_aa64isar1_el1;
	u_register_t id_aa64isar2_el1;
	u_register_t id_aa64isar3_el1;
	u_register_t id_aa64mmfr0_el1;
	u_register_t id_aa64mmfr1_el1;
	u_register_t id_aa64mmfr2_el1;
	u_register_t id_aa64mmfr3_el1;
	u_register_t id_aa64mmfr4_el1;
	u_register_t id_aa64pfr0_el1;
	u_register_t id_aa64pfr1_el1;
	u_register_t id_aa64pfr2_el1;
	u_register_t id_aa64smfr0_el1;
	u_register_t id_aa64zfr0_el1;
};

/* cppcheck-suppress misra-c2012-8.4 */
extern struct cached_idreg_info cached_idreg;

#define READ_CACHED_REG(reg)		cached_idreg.reg

/*
 * Called once during cold boot on the primary CPU
 * before any features are queried in RMM.
 */
void arch_features_query_el3_support(void);

/**************************************************************************
 * Mask macro for ID registers.
 *
 * Some ID registers contain fields that must be read with a mask
 * applied. For these registers, these macros defines the appropriate
 * mask.
 *
 * Registers that are read unmasked have a mask defined as UINT64_MAX,
 * as all bits are considered valid in those cases.
 *
 * ID registers that are to be 0'ed do not have a mask defined here.
 *************************************************************************/

/*
 * ID_AA64DFR0_EL1:
 */
#define ID_AA64DFR0_EL1_HW_MASK				  \
	(MASK(ID_AA64DFR0_EL1_DebugVer)			| \
	MASK(ID_AA64DFR0_EL1_PMUVer)			| \
	MASK(ID_AA64DFR0_EL1_BRPs)			| \
	MASK(ID_AA64DFR0_EL1_WRPs)			| \
	MASK(ID_AA64DFR0_EL1_BRBE)			| \
	MASK(ID_AA64DFR0_EL1_HPMN0))

/*
 * ID_AA64DFR1_EL1:
 */
#define ID_AA64DFR1_EL1_HW_MASK				  \
	(MASK(ID_AA64DFR1_EL1_BRPs)			| \
	MASK(ID_AA64DFR1_EL1_WRPs)			| \
	MASK(ID_AA64DFR1_EL1_ABLE)			| \
	MASK(ID_AA64DFR1_EL1_ABL_CMPS))

/*
 * ID_AA64DFR2_EL1:
 */
#define ID_AA64DFR2_EL1_HW_MASK				  \
	(MASK(ID_AA64DFR2_EL1_BWE))

/*
 * ID_AA64ISAR0_EL1:
 */
#define ID_AA64ISAR0_EL1_HW_MASK			UINT64_MAX

/*
 * ID_AA64ISAR1_EL1:
 */
#define ID_AA64ISAR1_EL1_HW_MASK			UINT64_MAX

/*
 * ID_AA64ISAR2_EL1:
 */
#define ID_AA64ISAR2_EL1_HW_MASK			UINT64_MAX

/*
 * ID_AA64ISAR3_EL1:
 */
#define ID_AA64ISAR3_EL1_HW_MASK			UINT64_MAX

/*
 * ID_AA64MMFR0_EL1:
 */
#define ID_AA64MMFR0_EL1_HW_MASK			UINT64_MAX

/*
 * ID_AA64MMFR1_EL1:
 */
#define ID_AA64MMFR1_EL1_HW_MASK			UINT64_MAX

/*
 * ID_AA64MMFR2_EL1:
 */
#define ID_AA64MMFR2_EL1_HW_MASK			UINT64_MAX

/*
 * ID_AA64MMFR3_EL1:
 */
#define ID_AA64MMFR3_EL1_HW_MASK			  \
	(MASK(ID_AA64MMFR3_EL1_TCRX)			| \
	MASK(ID_AA64MMFR3_EL1_SCTLRX)			| \
	MASK(ID_AA64MMFR3_EL1_S1PIE)			| \
	MASK(ID_AA64MMFR3_EL1_S1POE)			| \
	MASK(ID_AA64MMFR3_EL1_MEC)			| \
	MASK(ID_AA64MMFR3_EL1_SNERR)			| \
	MASK(ID_AA64MMFR3_EL1_ANERR)			| \
	MASK(ID_AA64MMFR3_EL1_SDERR)			| \
	MASK(ID_AA64MMFR3_EL1_ADERR)			| \
	MASK(ID_AA64MMFR3_EL1_FPACC))

/*
 * ID_AA64MMFR4_EL1:
 */
#define ID_AA64MMFR4_EL1_HW_MASK			  \
	(MASK(ID_AA64MMFR4_EL1_POPS)			| \
	MASK(ID_AA64MMFR4_EL1_EIESB)			| \
	MASK(ID_AA64MMFR4_EL1_ASID2)			| \
	MASK(ID_AA64MMFR4_EL1_HACDBS)			| \
	MASK(ID_AA64MMFR4_EL1_FGWTE3)			| \
	MASK(ID_AA64MMFR4_EL1_NV_FRAC)			| \
	MASK(ID_AA64MMFR4_EL1_E2H0)			| \
	MASK(ID_AA64MMFR4_EL1_RMEGDI)			| \
	MASK(ID_AA64MMFR4_EL1_E3DSE))

/*
 * ID_AA64PFR0_EL1:
 */
#define ID_AA64PFR0_EL1_HW_MASK				UINT64_MAX

/*
 * ID_AA64PFR1_EL1:
 */
#define ID_AA64PFR1_EL1_HW_MASK				  \
	(MASK(ID_AA64PFR1_EL1_BT)			| \
	MASK(ID_AA64PFR1_EL1_SSBS)			| \
	MASK(ID_AA64PFR1_EL1_RAS_F)			| \
	MASK(ID_AA64PFR1_EL1_MPAM_F)			| \
	MASK(ID_AA64PFR1_EL1_SME)			| \
	MASK(ID_AA64PFR1_EL1_RNDR_TRAP)			| \
	MASK(ID_AA64PFR1_EL1_CSV2_F)			| \
	MASK(ID_AA64PFR1_EL1_NMI)			| \
	MASK(ID_AA64PFR1_EL1_DF2))

/*
 * ID_AA64PFR2_EL1:
 */
#define ID_AA64PFR2_EL1_HW_MASK				  \
	(MASK(ID_AA64PFR2_EL1_UINJ))

/*
 * ID_AA64ZFR0_EL1:
 */
#define ID_AA64ZFR0_EL1_HW_MASK				UINT64_MAX

static inline bool is_armv8_4_ttst_present(void)
{
	return (EXTRACT(ID_AA64MMFR2_EL1_ST,
		READ_CACHED_REG(id_aa64mmfr2_el1)) == 1U);
}

/*
 * Check if SVE is enabled
 * ID_AA64PFR0_EL1.SVE, bits [35:32]:
 * 0b0000 SVE architectural state and programmers' model are not implemented.
 * 0b0001 SVE architectural state and programmers' model are implemented.
 */
static inline bool is_feat_sve_present(void)
{
	return (EXTRACT(ID_AA64PFR0_EL1_SVE,
		READ_CACHED_REG(id_aa64pfr0_el1)) != 0UL);
}

/*
 * Check if SME is enabled
 * ID_AA64PFR1_EL1.SME, bits [27:24]:
 * 0b0000 SME architectural state and programmers' model are not implemented.
 * 0b0001 SME architectural state and programmers' model are implemented.
 * 0b0010 SME2 implemented. As 0b0001, plus the SME2 ZT0 register.
 */
static inline bool is_feat_sme_present(void)
{
	return (EXTRACT(ID_AA64PFR1_EL1_SME,
		READ_CACHED_REG(id_aa64pfr1_el1)) != 0UL);
}

/*
 * Check if RNDR is available
 */
static inline bool is_feat_rng_present(void)
{
	return (EXTRACT(ID_AA64ISAR0_EL1_RNDR,
		READ_CACHED_REG(id_aa64isar0_el1)) != 0UL);
}

/*
 * Check if FEAT_VMID16 is implemented
 * ID_AA64MMFR1_EL1.VMIDBits, bits [7:4]:
 * 0b0000 8 bits.
 * 0b0010 16 bits.
 * All other values are reserved.
 */
static inline bool is_feat_vmid16_present(void)
{
	return (EXTRACT(ID_AA64MMFR1_EL1_VMIDBits,
		READ_CACHED_REG(id_aa64mmfr1_el1)) == ID_AA64MMFR1_EL1_VMIDBits_16);
}

/*
 * Check if FEAT_LPA2 is implemented for stage 1.
 * 4KB granule at stage 1 supports 52-bit input and output addresses:
 * ID_AA64MMFR0_EL1.TGran4 bits [31:28]: 0b0001
 */
static inline bool is_feat_lpa2_4k_present(void)
{
	return (EXTRACT(ID_AA64MMFR0_EL1_TGRAN4,
		READ_CACHED_REG(id_aa64mmfr0_el1)) == ID_AA64MMFR0_EL1_TGRAN4_LPA2);
}

/*
 * Check if FEAT_LPA2 is implemented for stage 2.
 * 4KB granule at stage 2 supports 52-bit input and output addresses:
 * ID_AA64MMFR0_EL1.TGran4_2 bits [43:40]: 0b0011 ||
 * (ID_AA64MMFR0_EL1.TGran4_2 bits [43:40]: 0b0000 &&
 *  ID_AA64MMFR0_EL1.TGran4 bits [31:28]: 0b0001 &&
 */
static inline bool is_feat_lpa2_4k_2_present(void)
{
	u_register_t id_aa64mmfr0_el1 = READ_CACHED_REG(id_aa64mmfr0_el1);

	return ((EXTRACT(ID_AA64MMFR0_EL1_TGRAN4_2, id_aa64mmfr0_el1) ==
		ID_AA64MMFR0_EL1_TGRAN4_2_LPA2) ||
		 ((EXTRACT(ID_AA64MMFR0_EL1_TGRAN4_2, id_aa64mmfr0_el1) ==
		ID_AA64MMFR0_EL1_TGRAN4_2_TGRAN4) && is_feat_lpa2_4k_present()));
}

/*
 * Returns Performance Monitors Extension version.
 * ID_AA64DFR0_EL1.PMUVer, bits [11:8]:
 * 0b0000: Performance Monitors Extension not implemented
 */
static inline unsigned int read_pmu_version(void)
{
	return (unsigned int)EXTRACT(ID_AA64DFR0_EL1_PMUVer, READ_CACHED_REG(id_aa64dfr0_el1));
}

/*
 * Check if FEAT_HPMN0 is implemented.
 * ID_AA64DFR0_EL1.HPMN0, bits [63:60]:
 * 0b0001: Setting MDCR_EL2.HPMN to zero has defined behavior
 */
static inline bool is_feat_hpmn0_present(void)
{
	return (EXTRACT(ID_AA64DFR0_EL1_HPMN0,
		READ_CACHED_REG(id_aa64dfr0_el1)) == 1UL);
}

/*
 * Check if FEAT_DoubleFault2 is implemented.
 * ID_AA64PFR1_EL1.DF2, bits [59:56]:
 * 0b0000: FEAT_DoubleFault2 is not implemented
 * 0b0001: FEAT_DoubleFault2 is implemented
 * All other values: Reserved
 */
static inline bool is_feat_double_fault2_present(void)
{
	return (EXTRACT(ID_AA64PFR1_EL1_DF2,
		READ_CACHED_REG(id_aa64pfr1_el1)) == 1UL);
}

/*
 * Check if FEAT_SCTLR2X is implemented.
 * ID_AA64MMFR3_EL1.SCTLRX, bits [7:4]:
 * 0b0000: FEAT_SCTLR2X is not implemented.
 * 0b0001: FEAT_SCTLR2X is implemented.
 * All other values: Reserved.
 */
static inline bool is_feat_sctlr2x_present(void)
{
	return (EXTRACT(ID_AA64MMFR3_EL1_SCTLRX,
		READ_CACHED_REG(id_aa64mmfr3_el1)) == 1UL);
}

DEFINE_CONDITIONAL_SYSREG_RW_FUNCS(sctlr2_el12, if_present,		\
				   is_feat_sctlr2x_present, 0UL)

/*
 * Check if FEAT_MTE2 is implemented.
 * ID_AA64PFR1_EL1.MTE, bits [11:8]:
 * 0b0000 FEAT_MTE is not implemented.
 * 0b0001 FEAT_MTE is implemented.
 * 0b0010 FEAT_MTE2 is implemented.
 * 0b0011 FEAT_MTE3 is implemented.
 */
static inline bool is_feat_mte2_present(void)
{
	unsigned long mte = EXTRACT(ID_AA64PFR1_EL1_MTE,
				READ_CACHED_REG(id_aa64pfr1_el1));

	return ((mte >= ID_AA64PFR1_EL1_MTE2) && (mte <= ID_AA64PFR1_EL1_MTE3));
}

/*
 * Check if FEAT_SSBS is implemented.
 * ID_AA64PFR1_EL1, bits [7:4]:
 * 0b0000: FEAT_SSBS is not implemented.
 * 0b0001: FEAT_SSBS is implemented.
 * 0b0010: FEAT_SSBS2 is implemented.
 */
static inline bool is_feat_ssbs_present(void)
{
	unsigned long ssbs = EXTRACT(ID_AA64PFR1_EL1_SSBS,
				READ_CACHED_REG(id_aa64pfr1_el1));

	return ((ssbs >= ID_AA64PFR1_EL1_FEAT_SSBS) &&
		(ssbs <= ID_AA64PFR1_EL1_FEAT_SSBS2));
}

/*
 * Check if FEAT_NMI is implemented.
 * ID_AA64PFR1_EL1, bits [39:36]:
 * 0b0000: FEAT_NMI is not implemented.
 * 0b0001: FEAT_NMI is implemented.
 */
static inline bool is_feat_nmi_present(void)
{
	return (EXTRACT(ID_AA64PFR1_EL1_NMI,
		READ_CACHED_REG(id_aa64pfr1_el1)) == 1UL);
}

/*
 * Check if FEAT_EBEP is implemented.
 * ID_AA64DFR1_EL1, bits [51:48]:
 * 0b0000: FEAT_EBEP is not implemented.
 * 0b0001: FEAT_EBEP is implemented.
 */
static inline bool is_feat_ebep_present(void)
{
	return (EXTRACT(ID_AA64DFR1_EL1_EBEP,
		READ_CACHED_REG(id_aa64dfr1_el1)) == 1UL);
}

/*
 * Check if FEAT_SEBEP is implemented.
 * ID_AA64DFR0_EL1, bits [27:24]:
 * 0b0000: FEAT_SEBEP is not implemented.
 * 0b0001: FEAT_SEBEP is implemented.
 */
static inline bool is_feat_sebep_present(void)
{
	return (EXTRACT(ID_AA64DFR0_EL1_SEBEP,
		READ_CACHED_REG(id_aa64dfr0_el1)) == 1UL);
}

/*
 * Check if FEAT_GCS is implemented.
 * ID_AA64PFR1_EL1, bits [47:44]:
 * 0b0000: FEAT_GCS is not implemented.
 * 0b0001: FEAT_GCS is implemented.
 */
static inline bool is_feat_gcs_present(void)
{
	return (EXTRACT(ID_AA64PFR1_EL1_GCS,
		READ_CACHED_REG(id_aa64pfr1_el1)) == 1UL);
}

/*
 * Check if FEAT_MPAM is implemented, regardless of the version.
 *
 * The implemented FEAT_MPAM version is determined by:
 *
 *	ID_AA64PFR0_EL1, bits [43:40]: Major version.
 *	ID_AA64PFR1_EL1, bits [19:16]: Minor version.
 *
 * with the following encoding:
 *
 *	Major  - Minor
 *	0b0000 - 0b0000: FEAT_MPAM is not implemented.
 *	0b0000 - 0b0001: FEAT_MPAM v0.1 is implemented.
 *	0b0001 - 0b0000: FEAT_MPAM v1.0 is implemented.
 *	0b0001 - 0b0001: FEAT_MPAM v1.1 is implemented.
 */
static inline bool is_feat_mpam_present(void)
{
	return ((EXTRACT(ID_AA64PFR0_EL1_MPAM, READ_CACHED_REG(id_aa64pfr0_el1)) != 0UL) ||
		(EXTRACT(ID_AA64PFR1_EL1_MPAM_F, READ_CACHED_REG(id_aa64pfr1_el1)) != 0UL));
}

/*
 * Check if FEAT_BRBE is implemented.
 * ID_AA64DFR0_EL1, bits [55:52]:
 * 0b0000: FEAT_BRBE is not implemented.
 * 0b0001: FEAT_BRBE is implemented.
 */
static inline bool is_feat_brbe_present(void)
{
	bool result = false;

	result = (EXTRACT(ID_AA64DFR0_EL1_BRBE, READ_CACHED_REG(id_aa64dfr0_el1)) != 0UL);
	return result;
}

/*
 * Check if FEAT_FGT is implemented.
 * ID_AA64MMFR0_EL1, bits [59:56]:
 * 0b0000: FEAT_FGT controls are not implemented.
 * 0b0001/0b0002: FEAT_FGT controls are implemented.
 */
static inline bool is_feat_fgt_present(void)
{
	return (EXTRACT(ID_AA64MMFR0_EL1_FGT, READ_CACHED_REG(id_aa64mmfr0_el1)) != 0UL);
}

/*
 * Check if FEAT_TCR2 is implemented.
 * ID_AA64MMFR3_EL1, bits [3:0]:
 * 0b0000: FEAT_TCR2 is not implemented.
 * 0b0001: FEAT_TCR2 is implemented.
 */
static inline bool is_feat_tcr2_present(void)
{
	return (EXTRACT(ID_AA64MMFR3_EL1_TCRX, READ_CACHED_REG(id_aa64mmfr3_el1)) != 0UL);
}

DEFINE_CONDITIONAL_SYSREG_RW_FUNCS(tcr2_el12, if_present,		\
				   is_feat_tcr2_present, 0UL)

/*
 * Check if FEAT_MEC is implemented.
 * ID_AA64MMFR3_EL1.MEC, bits [31:28]:
 * 0b0000: Memory Encryption Contexts is not implemented
 * 0b0001: Memory Encryption Contexts is implemented
 */
static inline bool is_feat_mec_present(void)
{
	return (EXTRACT(ID_AA64MMFR3_EL1_MEC,
		READ_CACHED_REG(id_aa64mmfr3_el1)) != 0UL);
}

/*
 * Check if S1PIE is implemented
 * ID_AA64MMFR3_EL1.S1PIE, bits [11:8]:
 * 0b0000 Stage 1 permission indirection extension arch. feature is not implemented.
 * 0b0001 Stage 1 permission indirection extension arch. feature is implemented.
 */
static inline bool is_feat_s1pie_present(void)
{
	return (EXTRACT(ID_AA64MMFR3_EL1_S1PIE,
		READ_CACHED_REG(id_aa64mmfr3_el1)) != 0UL);
}

/*
 * Check if S1POE is implemented
 * ID_AA64MMFR3_EL1.S1POE, bits [19:16]:
 * 0b0000 Stage 1 permission overlay extension arch. feature is not implemented.
 * 0b0001 Stage 1 permission overlay extension arch. feature is implemented.
 */
static inline bool is_feat_s1poe_present(void)
{
	return (EXTRACT(ID_AA64MMFR3_EL1_S1POE,
		READ_CACHED_REG(id_aa64mmfr3_el1)) != 0UL);
}

DEFINE_CONDITIONAL_SYSREG_RW_FUNCS(pir_el12, if_present,		\
				   is_feat_s1pie_present, 0UL)

DEFINE_CONDITIONAL_SYSREG_RW_FUNCS(pire0_el12, if_present,		\
				   is_feat_s1pie_present, 0UL)

DEFINE_CONDITIONAL_SYSREG_RW_FUNCS(por_el12, if_present,		\
				   is_feat_s1poe_present, 0UL)

/*
 * Check if S2PIE is enabled
 * ID_AA64MMFR3_EL1.S2PIE, bits [15:12]:
 * 0b0000 Stage 2 permission indirection extension arch. feature is not implemented.
 * 0b0001 Stage 2 permission indirection extension arch. feature is implemented.
 */
static inline bool is_feat_s2pie_present(void)
{
	return (EXTRACT(ID_AA64MMFR3_EL1_S2PIE,
			READ_CACHED_REG(id_aa64mmfr3_el1)) != 0UL);
}

/*
 * Check if S2POE is enabled
 * ID_AA64MMFR3_EL1.S2POE, bits [23:20]:
 * 0b0000 Stage 2 permission overlay extension arch. feature is not implemented.
 * 0b0001 Stage 2 permission overlay extension arch. feature is implemented.
 */
static inline bool is_feat_s2poe_present(void)
{
	return (EXTRACT(ID_AA64MMFR3_EL1_S2POE,
			READ_CACHED_REG(id_aa64mmfr3_el1)) != 0UL);
}

static inline bool are_feat_s2pie_and_s2poe_present(void)
{
	return is_feat_s2pie_present() && is_feat_s2poe_present();
}

unsigned int arch_feat_get_pa_width(void);

#endif /* ARCH_FEATURES_H */
