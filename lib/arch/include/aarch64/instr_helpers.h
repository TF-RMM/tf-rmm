/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef INSTR_HELPERS_H
#define INSTR_HELPERS_H

#include <arch.h>
#include <types.h>
#include <utils_def.h>

/**********************************************************************
 * Macros which create inline functions to read or write CPU system
 * registers
 *********************************************************************/

/* Force inline */
#define DEFINE_SYSREG_READ_FUNC_(_name, _reg_name)		\
__attribute__((__always_inline__))				\
static inline u_register_t read_ ## _name(void)			\
{								\
	u_register_t v;						\
	__asm__ volatile ("mrs %0, " #_reg_name : "=r" (v));	\
	return v;						\
}

#define DEFINE_SYSREG_WRITE_FUNC_(_name, _reg_name)		\
__attribute__((__always_inline__))				\
static inline void write_ ## _name(u_register_t v)		\
{								\
	(void)v; /* To avoid MISRA-C:2012-2.7 warnings */ \
	__asm__ volatile ("msr " #_reg_name ", %0" : : "r" (v));\
}

#define SYSREG_WRITE_CONST(_reg_name, v)			\
	__asm__ volatile ("msr " #_reg_name ", %0" : : "i" (v))

/*
 * The following macros define accessors for 128-bit registers.
 */

/*
 * Fixed opcode for AArch64 instruction
 * MRRS x0, x1, <sysreg>
 * where <sysreg> is left as all zeros.
 */
#define MRRS_OPCODE		(UL(0xD5700000))
#define DEFINE_SYSREG128_READ_FUNC_(_name, _reg_encoding)		\
	_DEFINE_SYSREG128_READ_FUNC_(_name,				\
			/* mrrs x0, x1, _reg_encoding */		\
			(MRRS_OPCODE | SYSREG_ ## _reg_encoding))	\

#define _DEFINE_SYSREG128_READ_FUNC_(_name, _mrrs)			\
__attribute__((__always_inline__))					\
static inline struct reg128 read128_ ## _name(void)			\
{									\
	struct reg128 retval;						\
									\
	/* mrrs needs contiguous registers, so we manually select them */ \
	register uint64_t __lo asm("x0");				\
	register uint64_t __hi asm("x1");				\
									\
	__asm__ volatile (						\
		".inst %c2\n"	/* mrrs x0, x1, _reg_encoding */	\
		: "=r"(__lo), "=r"(__hi)				\
		: "i"(_mrrs)						\
		: "memory"						\
	);								\
									\
	retval.lo = __lo;						\
	retval.hi = __hi;						\
									\
	return retval;							\
}

/*
 * Fixed opcode for AArch64 instruction
 * MSRR <sysreg>, x0, x1
 * where <sysreg> is left as all zeros.
 */
#define MSRR_OPCODE		(UL(0xD5500000))
#define DEFINE_SYSREG128_WRITE_FUNC_(_name, _reg_encoding)		\
	_DEFINE_SYSREG128_WRITE_FUNC_(_name,				\
			/* msrr _reg_encoding, x0, x1 */		\
			(MSRR_OPCODE | SYSREG_ ## _reg_encoding))	\

#define _DEFINE_SYSREG128_WRITE_FUNC_(_name, _msrr)			\
__attribute__((__always_inline__))					\
static inline void write128_ ## _name(struct reg128 *v)			\
{									\
	/* msrr needs contiguous registers, so we manually select them */ \
	register uint64_t __lo asm("x0") = (uint64_t)v->lo;		\
	register uint64_t __hi asm("x1") = (uint64_t)v->hi;		\
									\
	__asm__ volatile (						\
		".inst %c2\n"	/* msrr _reg_encoding, x0, x1 */	\
		: : "r"(__lo), "r"(__hi), "i"(_msrr)			\
		:							\
	);								\
}

/**********************************************************************
 * Macro to read general purpose register
 *********************************************************************/
#define READ_REGISTER(v, _reg_name)				\
	__asm__ volatile ("mov %0, " #_reg_name : "=r" (v) :)

/**********************************************************************
 * Macros to create inline functions for system instructions
 *********************************************************************/

/* Define function for simple system instruction */
#define DEFINE_SYSOP_FUNC(_op)				\
__attribute__((__always_inline__))			\
static inline void (_op)(void)				\
{							\
	__asm__ (#_op);					\
}

/* Define function for system instruction with register parameter */
#define DEFINE_SYSOP_PARAM_FUNC(_op)			\
__attribute__((__always_inline__))			\
static inline void (_op)(uint64_t v)			\
{							\
	(void)v; /* To avoid MISRA-C:2012-2.7 warnings */ \
	 __asm__ (#_op "  %0" : : "r" (v));		\
}

/* Define function for system instruction with type specifier */
#define DEFINE_SYSOP_TYPE_FUNC(_op, _type)		\
__attribute__((__always_inline__))			\
static inline void (_op ## _type)(void)			\
{							\
	__asm__ (#_op " " #_type : : : "memory");			\
}

/* Define function for system instruction with register parameter */
#define DEFINE_SYSOP_TYPE_PARAM_FUNC(_op, _type)	\
__attribute__((__always_inline__))			\
static inline void (_op ## _type)(uint64_t v)		\
{							\
	(void)v; /* To avoid MISRA-C:2012-2.7 warnings */ \
	 __asm__ (#_op " " #_type ", %0" : : "r" (v));	\
}

#define dsb(scope) asm volatile("dsb " #scope : : : "memory")
#define dmb(scope) asm volatile("dmb " #scope : : : "memory")

/*
 * These additional defines allow Arch-specific implementations different
 * from the common template.
 */

/* DC ZVA, Data Cache Zero by VA instruction */
#define DEFINE_SYSOP_DCZVA	DEFINE_SYSOP_TYPE_PARAM_FUNC(dc, zva)

#define DCCIPAE_NS_BIT		(1UL << 63)
#define DCCIPAE_NSE_BIT		(1UL << 62)

/*
 * DC CIPAE, Data or unified Cache line Clean and Invalidate by PA to
 * PoE.
 */
#define DEFINE_SYSOP_DCCIPAE					\
__attribute((__always_inline__))				\
static inline void dccipae(uint64_t pa)				\
{								\
								\
	(void)pa; /* To avoid MISRA-C:2012-2.7 warnings */	\
	pa |= (DCCIPAE_NS_BIT | DCCIPAE_NSE_BIT);		\
	__asm__ ("sys #4, c7, c14, #0, %0" : : "r" (pa));	\
}

#endif /* INSTR_HELPERS_H */
