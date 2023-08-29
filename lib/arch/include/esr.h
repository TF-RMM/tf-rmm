/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef ESR_H
#define ESR_H

#include <arch.h>
#include <assert.h>
#include <stdbool.h>
#include <utils_def.h>

static inline unsigned int esr_srt(unsigned long esr)
{
	return (unsigned int)EXTRACT(ESR_EL2_ABORT_SRT, esr);
}

static inline bool esr_is_write(unsigned long esr)
{
	return ((esr & ESR_EL2_ABORT_WNR_BIT) != 0UL);
}

static inline bool esr_sign_extend(unsigned long esr)
{
	return ((esr & ESR_EL2_ABORT_SSE_BIT) != 0UL);
}

static inline bool esr_sixty_four(unsigned long esr)
{
	return ((esr & ESR_EL2_ABORT_SF_BIT) != 0UL);
}

static inline unsigned int esr_sas(unsigned long esr)
{
	return (unsigned int)EXTRACT(ESR_EL2_ABORT_SAS, esr);
}

static inline unsigned int access_len(unsigned long esr)
{
	switch (esr_sas(esr)) {
	case ESR_EL2_ABORT_SAS_BYTE_VAL:
		return 1U;
	case ESR_EL2_ABORT_SAS_HWORD_VAL:
		return 2U;
	case ESR_EL2_ABORT_SAS_WORD_VAL:
		return 4U;
	default:
		assert(esr_sas(esr) == ESR_EL2_ABORT_SAS_DWORD_VAL);
		return 8U;
	}
}

static inline unsigned long access_mask(unsigned long esr)
{
	switch (esr_sas(esr)) {
	case ESR_EL2_ABORT_SAS_BYTE_VAL:
		return 0xffUL;
	case ESR_EL2_ABORT_SAS_HWORD_VAL:
		return 0xffffUL;
	case ESR_EL2_ABORT_SAS_WORD_VAL:
		return 0xffffffffUL;
	default:
		assert(esr_sas(esr) == ESR_EL2_ABORT_SAS_DWORD_VAL);
		return ~(0UL);
	}
}

#endif /* ESR_H */
