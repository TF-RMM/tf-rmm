/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef SPINLOCK_H
#define SPINLOCK_H

/*
 * Trivial spinlock implementations, per ARM DDI 0487J.a, section K13.3.1
 */

/* 32-bit spinlock */
typedef struct {
	unsigned int val;
} spinlock_t;

static inline void spinlock_acquire(spinlock_t *l)
{
	unsigned int tmp;

	/* To avoid misra-c2012-2.7 warnings */
	(void)l;

	asm volatile(
	"	sevl\n"
	"	prfm	pstl1keep, %[lock]\n"
	"1:\n"
	"	wfe\n"
	"	ldaxr	%w[tmp], %[lock]\n"
	"	cbnz	%w[tmp], 1b\n"
	"	stxr	%w[tmp], %w[one], %[lock]\n"
	"	cbnz	%w[tmp], 1b\n"
	: [lock] "+Q" (l->val),
	  [tmp] "=&r" (tmp)
	: [one] "r" (1)
	: "memory"
	);
}

static inline void spinlock_release(spinlock_t *l)
{
	/* To avoid misra-c2012-2.7 warnings */
	(void)l;

	asm volatile(
	"	stlr	wzr, %[lock]\n"
	: [lock] "+Q" (l->val)
	:
	: "memory"
	);
}

/* 8-bit spinlock */
typedef struct {
	unsigned char val;
} byte_spinlock_t;

static inline void byte_spinlock_acquire(byte_spinlock_t *l)
{
	unsigned int tmp;

	/* To avoid misra-c2012-2.7 warnings */
	(void)l;

	asm volatile(
	"	sevl\n"
	"	prfm	pstl1keep, %[lock]\n"
	"1:\n"
	"	wfe\n"
	"	ldaxrb	%w[tmp], %[lock]\n"
	"	cbnz	%w[tmp], 1b\n"
	"	stxrb	%w[tmp], %w[one], %[lock]\n"
	"	cbnz	%w[tmp], 1b\n"
	: [lock] "+Q" (l->val),
	  [tmp] "=&r" (tmp)
	: [one] "r" (1)
	: "memory"
	);
}

static inline void byte_spinlock_release(byte_spinlock_t *l)
{
	/* To avoid misra-c2012-2.7 warnings */
	(void)l;

	asm volatile(
	"	stlrb	wzr, %[lock]\n"
	: [lock] "+Q" (l->val)
	:
	: "memory"
	);
}

#endif /* SPINLOCK_H */
