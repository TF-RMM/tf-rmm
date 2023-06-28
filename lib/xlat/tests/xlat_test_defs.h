/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef XLAT_TEST_DEFS_H
#define XLAT_TEST_DEFS_H

#include <utils_def.h>
#include <xlat_defs_private.h>
#include <xlat_tables.h>

/*
 * All the definitions on this file are as per Issue G.a of the
 * Arm Architecture Reference Manual for Armv8-A architecture profile.
 * Section D5: The AArch64 Virtual Memory System Architecture (VMSA)
 */

/*
 * Maximum PA space size supported by the architecture, in bits.
 *
 * Note that the value on this macro is regardless of the maximum
 * PA size supported by the platform, reported through
 * id_aa64mmfr0_el1 register.
 */
#define XLAT_TESTS_MAX_PA_BITS		(48U)
/* Maximum PA space size */
#define XLAT_TESTS_MAX_PA_SIZE		(1ULL << XLAT_TESTS_MAX_PA_BITS)
/* PA address mask */
#define XLAT_TESTS_PA_MASK		(XLAT_TESTS_MAX_PA_SIZE - 1ULL)

/* Same as above, but with FEAT_LPA2 enabled (PA size up to 52 bits) */
#define XLAT_TESTS_MAX_PA_BITS_LPA2	(52U)
/* Maximum PA space size */
#define XLAT_TESTS_MAX_PA_SIZE_LPA2	(1ULL << XLAT_TESTS_MAX_PA_BITS_LPA2)
/* PA address mask */
#define XLAT_TESTS_PA_MASK_LPA2		(XLAT_TESTS_MAX_PA_SIZE_LPA2 - 1ULL)

/* Bitmask for a low region VA */
#define XLAT_TESTS_LOW_REGION_MASK	(~(HIGH_REGION_MASK))

/*
 * The xlat library only supports 4KB of granularity so the lowest level
 * table descriptor that support block translation is Level 1 (or 0 if
 * FEAT_LPA2 is supported). The following macro specifies the biggest
 * block size that can be mapped by the xlat library.
 */
#define XLAT_TESTS_MAX_BLOCK_SIZE				\
				XLAT_BLOCK_SIZE(XLAT_MIN_BLOCK_LVL())

#define XLAT_TESTS_IS_DESC(tte, desc)				\
	(((tte) & (DESC_MASK)) == (desc))

/*****************************************************
 * Following definitions are as per RMM xlat library
 ****************************************************/

#define XLAT_TESTS_IS_TRANSIENT_DESC(_x)			\
	((_x) & (1ULL << TRANSIENT_FLAG_SHIFT))

#endif /* XLAT_TEST_DEFS_H */
