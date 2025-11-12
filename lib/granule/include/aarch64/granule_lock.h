/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef GRANULE_LOCK_H
#define GRANULE_LOCK_H

#include <granule_types.h>

static inline void granule_bitlock_acquire(struct granule *g)
{
	/* To avoid misra-c2012-2.7 warnings */
	(void)g;
	uint32_t tmp;
	uint32_t mask = GRN_LOCK_BIT;

	/* cppcheck-suppress misra-c2012-17.3 */
	asm volatile(
	"1:	ldsetah	%w[mask], %w[tmp], %[lock]\n"
	"	tbz	%w[tmp], #%c[bit], 2f\n"
	"	ldxrh	%w[tmp], %[lock]\n"
	"	tbz	%w[tmp], #%c[bit], 1b\n"
	"	wfe\n"
	"	b	1b\n"
	"2:\n"
	: [lock] "+Q" (g->descriptor),
	  [tmp] "=&r" (tmp)
	: [mask] "r" (mask),
	  [bit] "i" (GRN_LOCK_SHIFT)
	: "memory"
	);
}

static inline void granule_bitlock_release(struct granule *g)
{
	/* To avoid misra-c2012-2.7 warnings */
	(void)g;
	uint32_t mask = GRN_LOCK_BIT;

	/* cppcheck-suppress misra-c2012-17.3 */
	asm volatile(
	"	stclrlh	%w[mask], %[lock]\n"
	: [lock] "+Q" (g->descriptor)
	: [mask] "r" (mask)
	: "memory"
	);
}

static inline void dev_granule_bitlock_acquire(struct dev_granule *g)
{
	/* To avoid misra-c2012-2.7 warnings */
	(void)g;
	uint32_t tmp;
	uint32_t mask = DEV_GRN_LOCK_BIT;

	/* cppcheck-suppress misra-c2012-17.3 */
	asm volatile(
	"1:	ldsetab	%w[mask], %w[tmp], %[lock]\n"
	"	tbz	%w[tmp], #%c[bit], 2f\n"
	"	ldxrb	%w[tmp], %[lock]\n"
	"	tbz	%w[tmp], #%c[bit], 1b\n"
	"	wfe\n"
	"	b	1b\n"
	"2:\n"
	: [lock] "+Q" (g->descriptor),
	  [tmp] "=&r" (tmp)
	: [mask] "r" (mask),
	  [bit] "i" (DEV_GRN_LOCK_SHIFT)
	: "memory"
	);
}

static inline void dev_granule_bitlock_release(struct dev_granule *g)
{
	/* To avoid misra-c2012-2.7 warnings */
	(void)g;
	uint32_t mask = DEV_GRN_LOCK_BIT;

	/* cppcheck-suppress misra-c2012-17.3 */
	asm volatile(
	"	stclrlb	%w[mask], %[lock]\n"
	: [lock] "+Q" (g->descriptor)
	: [mask] "r" (mask)
	: "memory"
	);
}

#endif /* GRANULE_LOCK_H */
