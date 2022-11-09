/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef FEATURE_H
#define FEATURE_H

#include <arch.h>

#define	RMM_FEATURE_MIN_IPA_SIZE		PARANGE_0000_WIDTH

#define RMM_FEATURE_REGISTER_0_INDEX		UL(0)

#define RMM_FEATURE_REGISTER_0_S2SZ_SHIFT	UL(0)
#define RMM_FEATURE_REGISTER_0_S2SZ_WIDTH	UL(8)

#define RMM_FEATURE_REGISTER_0_LPA2_SHIFT	UL(8)
#define RMM_FEATURE_REGISTER_0_LPA2_WIDTH	UL(1)

#define	RMI_NO_LPA2				UL(0)
#define	RMI_LPA2				UL(1)

#define RMM_FEATURE_REGISTER_0_HASH_SHA_256_SHIFT	UL(28)
#define RMM_FEATURE_REGISTER_0_HASH_SHA_256_WIDTH	UL(1)

#define RMM_FEATURE_REGISTER_0_HASH_SHA_512_SHIFT	UL(29)
#define RMM_FEATURE_REGISTER_0_HASH_SHA_512_WIDTH	UL(1)

bool validate_feature_register(unsigned long index, unsigned long value);

#endif /* FEATURE_H */
