/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 * SPDX-FileCopyrightText: Copyright NVIDIA Corporation.
 */

#ifndef UTILS_DEF_H
#define UTILS_DEF_H

#if !(defined(__ASSEMBLER__) || defined(__LINKER__))
#include <stdint.h>
#endif

/*
 * For those constants to be shared between C and other sources, apply a 'U',
 * 'UL', 'ULL', 'L' or 'LL' suffix to the argument only in C, to avoid
 * undefined or unintended behaviour.
 *
 * The GNU assembler and linker do not support these suffixes (it causes the
 * build process to fail) therefore the suffix is omitted when used in linker
 * scripts and assembler files.
 */
#if defined(__ASSEMBLER__) || defined(__LINKER__)
# define   U(_x)	(_x)
# define  UL(_x)	(_x)
# define ULL(_x)	(_x)
# define   L(_x)	(_x)
# define  LL(_x)	(_x)
#else
# define   U(_x)	(unsigned int)(_x)
# define  UL(_x)	(unsigned long)(_x)
# define ULL(_x)	(unsigned long long)(_x)
# define   L(_x)	(long)(_x)
# define  LL(_x)	(long long)(_x)
#endif /* __ASSEMBLER__ */

/* Short forms for commonly used attributes */
#define __dead2		__attribute__((__noreturn__))
#define __deprecated	__attribute__((__deprecated__))
#define __packed	__attribute__((__packed__))
#define __used		__attribute__((__used__))
#define __unused	__attribute__((__unused__))
#define __aligned(x)	__attribute__((__aligned__(x)))
#define __section(x)	__attribute__((__section__(x)))

#define __printflike(fmtarg, firstvararg) \
		__attribute__((__format__ (__printf__, fmtarg, firstvararg)))

/*
 * The round_up() macro rounds up a value to the given boundary in a
 * type-agnostic yet type-safe manner. The boundary must be a power of two.
 * In other words, it computes the smallest multiple of boundary which is
 * greater than or equal to value.
 *
 * round_down() is similar but rounds the value down instead.
 */
#define round_boundary(value, boundary)		\
	((__typeof__(value))((boundary) - 1))

#define round_up(value, boundary)		\
	((((value) - 1) | round_boundary(value, boundary)) + 1)

#define round_down(value, boundary)		\
	((value) & ~round_boundary(value, boundary))

/* Size of a 'm_' member of 's_' structure */
/* cppcheck-suppress [misra-c2012-20.7] */
#define SIZE_OF(s_, m_)		(sizeof(((struct s_ *)NULL)->m_))

/* Compute the number of elements in the given array */
#define ARRAY_SIZE(_a)	\
	((sizeof(_a) / sizeof((_a)[0])) + CHECK_TYPE_IS_ARRAY(_a))

/*
 * Macro checks types of array and variable/value to write
 * and reports compilation error if they mismatch.
 */
#define CHECK_ARRAY_TYPE(_a, _v)	\
	_Static_assert(__builtin_types_compatible_p(typeof((_a)[0]), typeof(_v)), \
	"array type mismatch")

/*
 * Array read/write macros with boundary and types checks
 * _a: name of array
 * _i: index
 * _v: variable/value to write
 */
#define SAFE_ARRAY_READ(_a, _i, _v)	\
({					\
	CHECK_ARRAY_TYPE(_a, _v);	\
	if ((_i) >= ARRAY_SIZE(_a)) {	\
		panic();		\
	}				\
	(_v) = (_a)[_i];			\
})

#define SAFE_ARRAY_WRITE(_a, _i, _v)	\
({					\
	CHECK_ARRAY_TYPE(_a, _v);	\
	if ((_i) >= ARRAY_SIZE(_a)) {	\
		panic();		\
	}				\
	(_a)[_i] = (_v);			\
})

#define COMPILER_ASSERT(_condition)	\
			extern char compiler_assert[(_condition) ? 1 : -1]

/*
 * If _expr is false, this will result in a compile time error as it tries to
 * define a bitfield of size -1 in that case.  Otherwise, it will define a
 * bitfield of size 0, which is valid, and not create a compiler warning.
 *
 * The return value is only relevant when the compilation succeeds, and by
 * subtracting the size of the same struct, this should always return 0 as a
 * value and can be included in other expressions.
 */
#define COMPILER_ASSERT_ZERO(_expr) (sizeof(struct { unsigned char: (-!(_expr)); }) \
				- sizeof(struct { unsigned char: 0; }))

#ifndef __cplusplus
#define CHECK_TYPE_IS_ARRAY(_v) \
	COMPILER_ASSERT_ZERO(!__builtin_types_compatible_p(typeof(_v),	\
							typeof(&((_v)[0]))))
#else
#define CHECK_TYPE_IS_ARRAY(_v)		0U
#endif

#ifdef CBMC
#define COMPILER_ASSERT_NO_CBMC(_condition)	COMPILER_ASSERT(0 == 0)
#else /* CBMC */
#define COMPILER_ASSERT_NO_CBMC(_condition)	COMPILER_ASSERT(_condition)
#endif /* CBMC */

#define IS_POWER_OF_TWO(x)			\
	((((x) + UL(0)) & ((x) - UL(1))) == UL(0))

#define COMPILER_BARRIER() __asm__ volatile ("" ::: "memory")

#define ALIGNED(_size, _alignment)		\
			(((unsigned long)(_size) % (_alignment)) == UL(0))

#define GRANULE_ALIGNED(_addr) ALIGNED((void *)(_addr), GRANULE_SIZE)
#define ALIGNED_TO_ARRAY(_addr, _array)		\
			(((uintptr_t)(_addr) >= (uintptr_t)&(_array)[0]) && \
			 ((((uintptr_t)(_addr) - (uintptr_t)&(_array)[0]) % \
						sizeof((_array)[0])) == UL(0)))

#define GRANULE_SIZE	(UL(1) << GRANULE_SHIFT)
#define GRANULE_MASK	(~(GRANULE_SIZE - 1U))

#define HAS_MPAM 0

#if HAS_MPAM
#define MPAM(_x...) _x
#else
#define MPAM(_x...)
#endif

#define HAS_SPE 0

#if HAS_SPE
#define SPE(_x...) _x
#else
#define SPE(_x...)
#endif

#if !(defined(__ASSEMBLER__) || defined(__LINKER__))

/*
 * System register field definitions.
 *
 * For any register field we define:
 * - <register>_<field>_SHIFT
 *   The bit offset of the LSB of the field.
 * - <register>_<field>_WIDTH
 *   The width of the field in bits.
 *
 * For single bit fields, we define:
 * - <register>_<field>_BIT
 *   The in-place value of the field with the bit set.
 *
 * For multi-bit fields, we define:
 * - <register>_<field>_<enum>
 *   The in-place value of the field set to the value corresponding to the
 *   enumeration name.
 *
 * For any register field, we define:
 * - INPLACE(<register>_<field>, val)
 *   The in-place value of the field set to val, handling any necessary type
 *   promotion to avoid truncation of val.
 * - MASK(<register>_<field)
 *   An in-place bitmask covering all bits of the field.
 * - EXTRACT(<register_field> <register_value>)
 *   A macro to extract the value of a register field shifted down so the
 *   value can be evaluated directly.
 * - EXTRACT_BIT(<register_field> <register_value>)
 *   A macro to extract the value of a register bit shifted down so the
 *   value can be evaluated directly.
 */
#define INPLACE(regfield, val) \
	(((val) + UL(0)) << (regfield##_SHIFT))

#define MASK(regfield) \
	((~0UL >> (64UL - (regfield##_WIDTH))) << (regfield##_SHIFT))

#define EXTRACT(regfield, reg) \
	(((reg) & MASK(regfield)) >> (regfield##_SHIFT))

#define EXTRACT_BIT(regfield, reg) \
	(((reg) >> (regfield##_SHIFT)) & UL(1))

/*
 * Generates an unsigned long long (64-bit) value where the bits @_msb
 * through @_lsb (inclusive) are set to one and all other bits are zero.  The
 * parameters can hold values from 0 through 63 and if _msb == _lsb a single
 * bit is set at that location.
 */
#define BIT_MASK_ULL(_msb, _lsb) \
	((~ULL(0) >> (63UL - (_msb))) & (~ULL(0) << (_lsb)))

/*
 * Stringify the result of expansion of a macro argument
 */
#ifndef __XSTRING
#define __STRING(x)	#x
#define __XSTRING(x)	__STRING(x)
#endif

/*
 * Defines member of structure and reserves space
 * for the next member with specified offset.
 */
/* cppcheck-suppress [misra-c2012-20.7] */
#define SET_MEMBER(member, start, end)	\
	union {				\
		member;			\
		unsigned char reserved##end[((end) - (start))]; \
	}

#define FALLTHROUGH	__attribute__((fallthrough))

/*
 * Helper macros for making code parts to be conditionally compiled, depending
 * on the current build being a CBMC build or not.
 */
#ifdef CBMC
#define IF_NCBMC(x)
#define IF_CBMC(x)	x
#else /* CBMC */
#define IF_NCBMC(x)	x
#define IF_CBMC(x)
#endif /* CBMC */

#endif /* !(defined(__ASSEMBLER__) || defined(__LINKER__)) */

#endif /* UTILS_DEF_H */
