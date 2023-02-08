/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef FPU_HELPERS_H
#define FPU_HELPERS_H

#include <arch_helpers.h>
#include <assert.h>
#include <cpuid.h>
#include <stdbool.h>

/* The FPU and SIMD register bank is 32 quadword (128 bits) Q registers. */
#define FPU_Q_SIZE		16U
#define FPU_Q_COUNT		32U

/* These defines are needed by assembly code to access the context. */
#define FPU_CTX_OFFSET_Q	0U
#define FPU_CTX_OFFSET_FPSR	512U
#define FPU_CTX_OFFSET_FPCR	520U

#ifdef RMM_FPU_USE_AT_REL2
#define FPU_ALLOW(expression) \
	do { \
		assert(fpu_is_my_state_saved(my_cpuid())); \
		write_cptr_el2( \
			(read_cptr_el2() & ~MASK(CPTR_EL2_FPEN)) | \
			(INPLACE(CPTR_EL2_FPEN, CPTR_EL2_FPEN_NO_TRAP_11))); \
		isb(); \
		expression; \
		write_cptr_el2( \
			(read_cptr_el2() & ~MASK(CPTR_EL2_FPEN)) | \
			(INPLACE(CPTR_EL2_FPEN, CPTR_EL2_FPEN_TRAP_ALL_00))); \
		isb(); \
	} while (false)

#define IS_FPU_ALLOWED() \
	(fpu_is_my_state_saved(my_cpuid()) && is_fpen_enabled())

#else /* RMM_FPU_USE_AT_REL2 */
#define FPU_ALLOW(expression) \
	do { \
		expression; \
	} while (false)

#define IS_FPU_ALLOWED() (true)

#endif /* RMM_FPU_USE_AT_REL2 */

struct fpu_state {
	unsigned __int128 q[FPU_Q_COUNT];
	unsigned long fpsr;
	unsigned long fpcr;
};

/* Since we use these offsets in assembly code make sure they are correct. */
COMPILER_ASSERT(__builtin_offsetof(struct fpu_state, q) ==
	FPU_CTX_OFFSET_Q);
COMPILER_ASSERT(__builtin_offsetof(struct fpu_state, fpsr) ==
	FPU_CTX_OFFSET_FPSR);
COMPILER_ASSERT(__builtin_offsetof(struct fpu_state, fpcr) ==
	FPU_CTX_OFFSET_FPCR);

/*
 * Save/restore FPU context to/from the `fpu_state` passed as parameter. The FPU
 * instruction trap needs to be disabled before calling these functions.
 * Can be used for context switching.
 */
void fpu_save_state(struct fpu_state *fpu);
void fpu_restore_state(struct fpu_state *fpu);

/*
 * Save/restore FPU state to/from a per-cpu buffer allocated within the
 * library. The FPU instruction trap is disabled by this function during the
 * access to the FPU registers.
 * These functions are expected to be called before FPU is used by RMM to save
 * the incoming FPU context.
 */
void fpu_save_my_state(void);
void fpu_restore_my_state(void);

/*
 * Return true iff an fpu state is saved in the per-cpu buffer in this library.
 *
 * After calling 'fpu_save_my_state' this function returns true. After calling
 * 'fpu_restore_my_state' this function returns false.
 */
bool fpu_is_my_state_saved(unsigned int cpu_id);

#endif /* FPU_HELPERS_H */
