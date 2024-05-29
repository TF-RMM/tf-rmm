/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef MEASUREMENT_DESCS_H
#define MEASUREMENT_DESCS_H

#include <measurement.h>
#include <utils_def.h>

/* RmmMeasurementDescriptorData type as per RMM spec */
struct measurement_desc_data {
	/* Measurement descriptor type, value 0x0 */
	SET_MEMBER(unsigned char desc_type, 0x0, 0x8);
	/* Length of this data structure in bytes */
	SET_MEMBER(unsigned long len, 0x8, 0x10);
	/* Current RIM value */
	SET_MEMBER(unsigned char rim[MAX_MEASUREMENT_SIZE], 0x10, 0x50);
	/* IPA at which the DATA Granule is mapped in the Realm */
	SET_MEMBER(unsigned long ipa, 0x50, 0x58);
	/* Flags provided by Host */
	SET_MEMBER(unsigned long flags, 0x58, 0x60);
	/*
	 * Hash of contents of DATA Granule, or zero if flags indicate DATA
	 * Granule contents are unmeasured
	 */
	SET_MEMBER(unsigned char content[MAX_MEASUREMENT_SIZE], 0x60, 0x100);
};
COMPILER_ASSERT_NO_CBMC(sizeof(struct measurement_desc_data) == 0x100UL);

COMPILER_ASSERT_NO_CBMC(U(offsetof(struct measurement_desc_data, desc_type)) == 0x0U);
COMPILER_ASSERT_NO_CBMC(U(offsetof(struct measurement_desc_data, len)) == 0x8U);
COMPILER_ASSERT_NO_CBMC(U(offsetof(struct measurement_desc_data, rim)) == 0x10U);
COMPILER_ASSERT_NO_CBMC(U(offsetof(struct measurement_desc_data, ipa)) == 0x50U);
COMPILER_ASSERT_NO_CBMC(U(offsetof(struct measurement_desc_data, flags)) == 0x58U);
COMPILER_ASSERT_NO_CBMC(U(offsetof(struct measurement_desc_data, content)) == 0x60U);

/* RmmMeasurementDescriptorRec type as per RMM spec */
struct measurement_desc_rec {
	/* Measurement descriptor type, value 0x1 */
	SET_MEMBER(unsigned char desc_type, 0x0, 0x8);
	/* Length of this data structure in bytes */
	SET_MEMBER(unsigned long len, 0x8, 0x10);
	/* Current RIM value */
	SET_MEMBER(unsigned char rim[MAX_MEASUREMENT_SIZE], 0x10, 0x50);
	/* Hash of 4KB page which contains REC parameters data structure */
	SET_MEMBER(unsigned char content[MAX_MEASUREMENT_SIZE], 0x50, 0x100);
};
COMPILER_ASSERT_NO_CBMC(sizeof(struct measurement_desc_rec) == 0x100UL);

COMPILER_ASSERT_NO_CBMC(U(offsetof(struct measurement_desc_rec, desc_type)) == 0x0U);
COMPILER_ASSERT_NO_CBMC(U(offsetof(struct measurement_desc_rec, len)) == 0x8U);
COMPILER_ASSERT_NO_CBMC(U(offsetof(struct measurement_desc_rec, rim)) == 0x10U);
COMPILER_ASSERT_NO_CBMC(U(offsetof(struct measurement_desc_rec, content)) == 0x50U);

/* RmmMeasurementDescriptorRipas type as per RMM spec */
struct measurement_desc_ripas {
	/* Measurement descriptor type, value 0x2 */
	SET_MEMBER(unsigned char desc_type, 0x0, 0x8);
	/* Length of this data structure in bytes */
	SET_MEMBER(unsigned long len, 0x8, 0x10);
	/* Current RIM value */
	SET_MEMBER(unsigned char rim[MAX_MEASUREMENT_SIZE], 0x10, 0x50);
	/* Base IPA at which the RIPAS change occurred */
	SET_MEMBER(unsigned long base, 0x50, 0x58);
	/* Top IPA at which the RIPAS change occurred */
	SET_MEMBER(unsigned long top, 0x58, 0x100);
};
COMPILER_ASSERT_NO_CBMC(sizeof(struct measurement_desc_ripas) == 0x100UL);

COMPILER_ASSERT_NO_CBMC(U(offsetof(struct measurement_desc_ripas, desc_type)) == 0x0U);
COMPILER_ASSERT_NO_CBMC(U(offsetof(struct measurement_desc_ripas, len)) == 0x8U);
COMPILER_ASSERT_NO_CBMC(U(offsetof(struct measurement_desc_ripas, rim)) == 0x10U);
COMPILER_ASSERT_NO_CBMC(U(offsetof(struct measurement_desc_ripas, base)) == 0x50U);
COMPILER_ASSERT_NO_CBMC(U(offsetof(struct measurement_desc_ripas, top)) == 0x58U);

#endif /* MEASUREMENT_DESCS_H */
