/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef SIMD_H
#define SIMD_H

#include <arch.h>
#include <arch_features.h>
#include <assert.h>
#include <stddef.h>

/* Size of one FPU vector register in bytes */
#define FPU_VEC_REG_SIZE	16U
#define FPU_VEC_REG_NUM		32U
#define FPU_REGS_SIZE		(FPU_VEC_REG_SIZE * FPU_VEC_REG_NUM)

/* These defines are required by compiler assert to check offsets */
#define FPU_CTX_OFFSET_Q	0x0U
#define FPU_CTX_OFFSET_FPSR	(FPU_REGS_SIZE)
#define FPU_CTX_OFFSET_FPCR	(FPU_CTX_OFFSET_FPSR + 8U)

/*
 * Size of SVE Z, Predicate (P), First Fault predicate Register (FFR) registers
 * in bytes for vector length 128 bits (0 vq). P and FFR registers are 1/8 of
 * Z register.
 */
#define SVE_Z_REG_MIN_SIZE	U(16)
#define SVE_P_REG_MIN_SIZE	(SVE_Z_REG_MIN_SIZE / 8)
#define SVE_FFR_REG_MIN_SIZE	(SVE_Z_REG_MIN_SIZE / 8)

/* Number of Z, P, FFR registers */
#define SVE_Z_REG_NUM		U(32)
#define SVE_P_REG_NUM		U(16)
#define SVE_FFR_REG_NUM		U(1)

#define SVE_Z_REGS_SIZE(vq)	((vq + 1) * (SVE_Z_REG_MIN_SIZE * SVE_Z_REG_NUM))
#define SVE_P_REGS_SIZE(vq)	((vq + 1) * (SVE_P_REG_MIN_SIZE * SVE_P_REG_NUM))
#define SVE_FFR_REGS_SIZE(vq)	((vq + 1) * (SVE_FFR_REG_MIN_SIZE * \
					     SVE_FFR_REG_NUM))

/* SVE vq architecture limit */
#define SVE_VQ_ARCH_MAX		((1U << ZCR_EL2_LEN_WIDTH) - 1U)

/* These defines are required by compiler assert to check offsets */
#define SVE_STATE_OFFSET_Z	0x0U
#define SVE_STATE_OFFSET_P	(SVE_Z_REGS_SIZE(SVE_VQ_ARCH_MAX))
#define SVE_STATE_OFFSET_FFR	(SVE_STATE_OFFSET_P + \
				 SVE_P_REGS_SIZE(SVE_VQ_ARCH_MAX))
#define SVE_STATE_OFFSET_ZCR_EL12	(SVE_STATE_OFFSET_FFR + \
				 SVE_FFR_REGS_SIZE(SVE_VQ_ARCH_MAX))
#define SVE_STATE_OFFSET_FPSR	(SVE_STATE_OFFSET_ZCR_EL12 + 8U)
#define SVE_STATE_OFFSET_FPCR	(SVE_STATE_OFFSET_FPSR + 8U)

typedef enum {
	SIMD_NONE,
	SIMD_FPU,
	SIMD_SVE
} simd_t;

struct fpu_state {
	uint8_t q[FPU_REGS_SIZE];
	uint64_t fpsr;
	uint64_t fpcr;
};

/* SVE state for architecture max supported vector length of 2048 bits */
struct sve_state {
	uint8_t z[SVE_Z_REGS_SIZE(SVE_VQ_ARCH_MAX)];
	uint8_t p[SVE_P_REGS_SIZE(SVE_VQ_ARCH_MAX)];
	uint8_t ffr[SVE_FFR_REGS_SIZE(SVE_VQ_ARCH_MAX)];
	uint64_t zcr_el12;
	/*
	 * Include FPU status and control registers. FPU vector registers are
	 * shared with Z regs
	 */
	uint64_t fpsr;
	uint64_t fpcr;
	/* Holds the SVE VQ for this SVE state. Not saved/restored */
	uint8_t vq;
};

struct simd_state {
	union {
		struct fpu_state fpu;
		struct sve_state sve;
	} t;
	simd_t simd_type;
};

/*
 * Since we access fpu_state and sve_state in assembly code make sure the
 * offset of all fields are correct.
 *
 * TODO: Auto generate header file simd-asm-offsets.h during build and use it
 * in assembly routines.
 */
COMPILER_ASSERT(__builtin_offsetof(struct fpu_state, q) == FPU_CTX_OFFSET_Q);
COMPILER_ASSERT(__builtin_offsetof(struct fpu_state, fpsr) ==
		FPU_CTX_OFFSET_FPSR);
COMPILER_ASSERT(__builtin_offsetof(struct fpu_state, fpcr) ==
		FPU_CTX_OFFSET_FPCR);

COMPILER_ASSERT(__builtin_offsetof(struct sve_state, z) == SVE_STATE_OFFSET_Z);
COMPILER_ASSERT(__builtin_offsetof(struct sve_state, p) == SVE_STATE_OFFSET_P);
COMPILER_ASSERT(__builtin_offsetof(struct sve_state, ffr) ==
		SVE_STATE_OFFSET_FFR);
COMPILER_ASSERT(__builtin_offsetof(struct sve_state, zcr_el12) ==
		SVE_STATE_OFFSET_ZCR_EL12);
COMPILER_ASSERT(__builtin_offsetof(struct sve_state, fpsr) ==
		SVE_STATE_OFFSET_FPSR);
COMPILER_ASSERT(__builtin_offsetof(struct sve_state, fpcr) ==
		SVE_STATE_OFFSET_FPCR);

/* Initialize simd layer based on CPU support for FPU or SVE */
void simd_init(void);

/* Return the max SVE vq discovered by RMM */
unsigned int simd_sve_get_max_vq(void);

/* Save SIMD state to memory pointed by 'simd' based on simd 'type'. */
void simd_save_state(simd_t type, struct simd_state *simd);

/* Restore SIMD state from memory pointed by 'simd' based on simd 'type'. */
void simd_restore_state(simd_t type, struct simd_state *simd);

/*
 * Initialize the simd_state before using this first time for a REC. The 'sve_vq'
 * parameter will be used to initialize SVE VQ length in case the simd type is
 * SVE or else it is ignored.
 */
void simd_state_init(simd_t type, struct simd_state *simd, uint8_t sve_vq);

/*
 * Save NS FPU or SVE state from registers to memory. This function dynamically
 * determines the SIMD type based on CPU SIMD capability.
 * TODO: Cater for SVE hint bit.
 */
void simd_save_ns_state(void);

/*
 * Restore NS FPU or SVE state from memory to registers. This function
 * dynamically determines the SIMD type based on CPU SIMD capability.
 * TODO: Cater for SVE hint bit.
 */
void simd_restore_ns_state(void);

/*
 * Returns 'true' if the current CPU's SIMD (FPU/SVE) live state is saved in
 * memory else 'false'.
 */
bool simd_is_state_saved(void);

/* Allow FPU and/or SVE access */
static inline void simd_enable(simd_t type)
{
	unsigned long cptr;

	cptr = read_cptr_el2();
	cptr &= ~(MASK(CPTR_EL2_VHE_FPEN) | MASK(CPTR_EL2_VHE_ZEN));

	switch (type) {
	case SIMD_SVE:
		assert(is_feat_sve_present());

		cptr |= INPLACE(CPTR_EL2_VHE_ZEN, CPTR_EL2_VHE_ZEN_NO_TRAP_11);
		cptr |= INPLACE(CPTR_EL2_VHE_FPEN, CPTR_EL2_VHE_FPEN_NO_TRAP_11);
		break;
	case SIMD_FPU:
		cptr |= INPLACE(CPTR_EL2_VHE_ZEN, CPTR_EL2_VHE_ZEN_TRAP_ALL_00);
		cptr |= INPLACE(CPTR_EL2_VHE_FPEN, CPTR_EL2_VHE_FPEN_NO_TRAP_11);
		break;
	default:
		assert(false);
	}

	write_cptr_el2(cptr);
	isb();
}

/* Deny FPU and SVE access */
static inline void simd_disable(void)
{
	unsigned long cptr;

	cptr = read_cptr_el2();
	cptr &= ~(MASK(CPTR_EL2_VHE_FPEN) | MASK(CPTR_EL2_VHE_ZEN));

	cptr |= INPLACE(CPTR_EL2_VHE_ZEN, CPTR_EL2_VHE_ZEN_TRAP_ALL_00);
	cptr |= INPLACE(CPTR_EL2_VHE_FPEN, CPTR_EL2_VHE_FPEN_TRAP_ALL_00);

	write_cptr_el2(cptr);
	isb();
}

/*
 * RMM support to use SIMD (FPU) at REL2
 */
#ifdef RMM_FPU_USE_AT_REL2
#define SIMD_FPU_ALLOW(expression)				\
	do {							\
		assert(simd_is_state_saved() == true);		\
		simd_enable(SIMD_FPU);				\
		expression;					\
		simd_disable();					\
	} while (false)

#define SIMD_IS_FPU_ALLOWED()	(simd_is_state_saved() && is_fpen_enabled())

#else /* !RMM_FPU_USE_AT_REL2 */
#define SIMD_FPU_ALLOW(expression)				\
	do {							\
		expression;					\
	} while (false)

#define SIMD_IS_FPU_ALLOWED() (true)

#endif /* RMM_FPU_USE_AT_REL2 */

#endif /* SIMD_H */
