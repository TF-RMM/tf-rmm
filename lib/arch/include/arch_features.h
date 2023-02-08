/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef ARCH_FEATURES_H
#define ARCH_FEATURES_H

#include <arch_helpers.h>
#include <stdbool.h>

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
 * Check if FEAT_LPA2 is implemented.
 * 4KB granule  at stage 2 supports 52-bit input and output addresses:
 * ID_AA64MMFR0_EL1.TGran4_2 bits [43:40]: 0b0011
 */
static inline bool is_feat_lpa2_4k_present(void)
{
	return (EXTRACT(ID_AA64MMFR0_EL1_TGRAN4_2,
		read_id_aa64mmfr0_el1()) == ID_AA64MMFR0_EL1_TGRAN4_2_LPA2);
}

unsigned int arch_feat_get_pa_width(void);

#endif /* ARCH_FEATURES_H */
