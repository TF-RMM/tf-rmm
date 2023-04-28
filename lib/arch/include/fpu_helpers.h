/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef FPU_HELPERS_H
#define FPU_HELPERS_H

#include <arch.h>
#include <assert.h>
#include <stddef.h>

/* Size of one FPU vector register in bytes */
#define FPU_VEC_REG_SIZE	U(16)
#define FPU_VEC_REG_NUM		U(32)
#define FPU_REGS_SIZE		(FPU_VEC_REG_SIZE * FPU_VEC_REG_NUM)

/* These defines are required by compiler assert to check offsets */
#define FPU_CTX_OFFSET_Q	0U
#define FPU_CTX_OFFSET_FPSR	(FPU_REGS_SIZE)
#define FPU_CTX_OFFSET_FPCR	(FPU_CTX_OFFSET_FPSR + sizeof(uint64_t))

struct fpu_state {
	__uint128_t q[FPU_VEC_REG_NUM];
	uint64_t fpsr;
	uint64_t fpcr;
};

/* Since we use these offsets in assembly code make sure they are correct. */
COMPILER_ASSERT(__builtin_offsetof(struct fpu_state, q) == FPU_CTX_OFFSET_Q);
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
void fpu_restore_state(const struct fpu_state *fpu);

#endif /* FPU_HELPERS_H */
