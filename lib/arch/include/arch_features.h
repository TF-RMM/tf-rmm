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

static inline bool is_armv8_4_ttst_present(void)
{
	return (EXTRACT(ID_AA64MMFR2_EL1_ST,
		read_id_aa64mmfr2_el1()) == 1U);
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
		read_id_aa64pfr0_el1()) != 0UL);
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
	return (EXTRACT(ID_AA64PFR1_EL1_SME, read_id_aa64pfr1_el1()) != 0UL);
}

/*
 * Check if RNDR is available
 */
static inline bool is_feat_rng_present(void)
{
	return (EXTRACT(ID_AA64ISAR0_EL1_RNDR,
		read_id_aa64isar0_el1()) != 0UL);
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
		read_id_aa64mmfr1_el1()) == ID_AA64MMFR1_EL1_VMIDBits_16);
}

/*
 * Check if FEAT_LPA2 is implemented for stage 1.
 * 4KB granule at stage 1 supports 52-bit input and output addresses:
 * ID_AA64MMFR0_EL1.TGran4 bits [31:28]: 0b0001
 */
static inline bool is_feat_lpa2_4k_present(void)
{
	return (EXTRACT(ID_AA64MMFR0_EL1_TGRAN4,
		read_id_aa64mmfr0_el1()) == ID_AA64MMFR0_EL1_TGRAN4_LPA2);
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
	u_register_t id_aa64mmfr0_el1 = read_id_aa64mmfr0_el1();

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
	return (unsigned int)EXTRACT(ID_AA64DFR0_EL1_PMUVer,
					read_id_aa64dfr0_el1());
}

/*
 * Check if FEAT_HPMN0 is implemented.
 * ID_AA64DFR0_EL1.HPMN0, bits [63:60]:
 * 0b0001: Setting MDCR_EL2.HPMN to zero has defined behavior
 */
static inline bool is_feat_hpmn0_present(void)
{
	return (EXTRACT(ID_AA64DFR0_EL1_HPMN0,
		read_id_aa64dfr0_el1()) == 1UL);
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
		read_id_aa64pfr1_el1()) == 1UL);
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
		read_id_aa64mmfr3_el1()) == 1UL);
}

DEFINE_CONDITIONAL_SYSREG_RW_FUNCS(sctlr2_el12, if_present,		\
				   is_feat_sctlr2x_present, 0UL)

unsigned int arch_feat_get_pa_width(void);

#endif /* ARCH_FEATURES_H */
