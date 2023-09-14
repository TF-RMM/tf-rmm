/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <buffer.h>
#include <xlat_tables.h>

/*
 * The VA space size for the high region, which maps the slot buffers,
 * needs to be a power of two, so round NR_CPU_SLOTS up to the closest
 * power of two.
 */
#define ROUNDED_NR_CPU_SLOTS	(1ULL << (64U - \
	(unsigned int)__builtin_clzll(((unsigned long long)NR_CPU_SLOTS) - 1U)))

#define RMM_SLOT_BUF_VA_SIZE	((ROUNDED_NR_CPU_SLOTS) * (GRANULE_SIZE))

#define SLOT_VIRT		((ULL(0xffffffffffffffff) - \
				 RMM_SLOT_BUF_VA_SIZE + ULL(1)))

struct xlat_llt_info *get_cached_llt_info(void);
uintptr_t slot_to_va(enum buffer_slot slot);
