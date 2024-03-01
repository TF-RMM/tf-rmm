/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef INSTR_HELPERS_H
#define INSTR_HELPERS_H

#include <host_harness.h>
#include <stddef.h>

#ifdef __cplusplus
/*
 * Disable write-strings warnings when building C++ code (used for unit
 * testing) as ISO C++ forbits converting a string constant to char*,
 * which is actually done by DEFINE_SYSREG_{READ, WRITE}_FUNC macros.
 */

#ifdef __clang__
	#pragma clang diagnostic ignored "-Wwrite-strings"
#else
	#pragma GCC diagnostic ignored "-Wwrite-strings"
#endif /* __clang__ */
#endif /* __cplusplus__ */

/**********************************************************************
 * Macros which create inline functions to read or write CPU system
 * registers
 *********************************************************************/
#define DEFINE_SYSREG_READ_FUNC_(_name, _reg_name)		\
static inline u_register_t read_ ## _name(void)			\
{								\
	return host_read_sysreg(#_name);			\
}

#define DEFINE_SYSREG_WRITE_FUNC_(_name, _reg_name)		\
static inline void write_ ## _name(u_register_t v)		\
{								\
	host_write_sysreg(#_name, v);				\
}

#define SYSREG_WRITE_CONST(_reg_name, v)			\
		host_write_sysreg(#_reg_name, v)

/**********************************************************************
 * Macro to read general purpose register
 *********************************************************************/
#define READ_REGISTER(v, _reg_name)				\
	v = host_read_sysreg(#_reg_name)

/**********************************************************************
 * Macros to create inline functions for system instructions
 *********************************************************************/

/* Define function for simple system instruction */
#define DEFINE_SYSOP_FUNC(_op)				\
static inline void (_op)(void)				\
{							\
	(void)(_op);					\
}

/* Define function for system instruction with register parameter */
#define DEFINE_SYSOP_PARAM_FUNC(_op)			\
static inline void (_op)(uint64_t v)			\
{							\
	(void)v; /* To avoid MISRA-C:2012-2.7 warnings */ \
}

/* Define function for system instruction with type specifier */
#define DEFINE_SYSOP_TYPE_FUNC(_op, _type)		\
static inline void (_op ## _type)(void)			\
{							\
}

/* Define function for system instruction with register parameter */
#define DEFINE_SYSOP_TYPE_PARAM_FUNC(_op, _type)	\
static inline void (_op ## _type)(uint64_t v)		\
{							\
	(void)v; /* To avoid MISRA-C:2012-2.7 warnings */ \
}

#define dsb(scope)
#define dmb(scope)

/*
 * These additional defines allow Arch-specific implementations different
 * from the common template.
 */

/* DC ZVA, Data Cache Zero by VA instruction */
#define DEFINE_SYSOP_DCZVA
void dczva(uint64_t addr);

#endif /* INSTR_HELPERS_H */
