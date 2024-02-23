/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch.h>
#include <arch_features.h>
#include <arch_helpers.h>
#include <assert.h>
#include <stdint.h>
#include <utils_def.h>

#ifndef CBMC
/*
 * Return the PA width supported by the current system.
 */
unsigned int arch_feat_get_pa_width(void)
{
	/*
	 * Physical Address ranges supported in the AArch64 Memory Model.
	 * Value 0b110 is supported in ARMv8.2 onwards but not used in RMM.
	 */
	const unsigned int pa_range_bits_arr[] = {
		PARANGE_0000_WIDTH, PARANGE_0001_WIDTH, PARANGE_0010_WIDTH,
		PARANGE_0011_WIDTH, PARANGE_0100_WIDTH, PARANGE_0101_WIDTH,
		PARANGE_0110_WIDTH
	};

	u_register_t pa_range = EXTRACT(ID_AA64MMFR0_EL1_PARANGE,
					read_id_aa64mmfr0_el1());

	assert(pa_range < ARRAY_SIZE(pa_range_bits_arr));

	return pa_range_bits_arr[pa_range];
}

#endif
