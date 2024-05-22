/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef SIMD_H
#define SIMD_H

#include <arch.h>

/* Size of one FPU vector register in bytes */
#define FPU_VEC_REG_SIZE	16U
#define FPU_VEC_REG_NUM		32U
#define FPU_REGS_SIZE		(FPU_VEC_REG_SIZE * FPU_VEC_REG_NUM)

/* These defines are required by compiler assert to check offsets */
#define FPU_REGS_OFFSET_Q	0x0U

/*
 * Size of SVE Z, Predicate (P), First Fault predicate Register (FFR) registers
 * in bytes for vector length 128 bits (0 vq). P and FFR registers are 1/8 of
 * Z register.
 */
#define SVE_Z_REG_MIN_SIZE	U(16)
#define SVE_P_REG_MIN_SIZE	(SVE_Z_REG_MIN_SIZE / 8U)
#define SVE_FFR_REG_MIN_SIZE	(SVE_Z_REG_MIN_SIZE / 8U)

/* Number of Z, P, FFR registers */
#define SVE_Z_REG_NUM		U(32)
#define SVE_P_REG_NUM		U(16)
#define SVE_FFR_REG_NUM		U(1)

#define SVE_Z_REGS_SIZE(vq)	(((vq) + 1U) * (SVE_Z_REG_MIN_SIZE * SVE_Z_REG_NUM))
#define SVE_P_REGS_SIZE(vq)	(((vq) + 1U) * (SVE_P_REG_MIN_SIZE * SVE_P_REG_NUM))
#define SVE_FFR_REGS_SIZE(vq)	(((vq) + 1U) * (SVE_FFR_REG_MIN_SIZE * \
					     SVE_FFR_REG_NUM))

/* SVE vq architecture limit */
#define SVE_VQ_ARCH_MAX		((1U << ZCR_EL2_LEN_WIDTH) - 1U)

/* These defines are required by compiler assert to check offsets */
#define SVE_REGS_OFFSET_Z	0x0U
#define SVE_REGS_OFFSET_P	(SVE_Z_REGS_SIZE(SVE_VQ_ARCH_MAX))
#define SVE_REGS_OFFSET_FFR	(SVE_REGS_OFFSET_P + \
				 SVE_P_REGS_SIZE(SVE_VQ_ARCH_MAX))

#ifndef __ASSEMBLER__
#include <arch_features.h>
#include <assert.h>
#include <stddef.h>

/* Flags for SIMD type */
#define SIMD_TFLAG_SVE		(U(1) << 0)
#define SIMD_TFLAG_SME		(U(1) << 1)

/* Flags for SIMD status */
#define SIMD_SFLAG_INIT_DONE	(U(1) << 0)
#define SIMD_SFLAG_SAVED	(U(1) << 1)
#define SIMD_SFLAG_SVE_HINT	(U(1) << 2)

/*
 * SIMD context owner.
 * SIMD_OWNER_NWD: Context belongs to NS world
 * SIMD_OWNER_REL1: Context belongs to Realm
 */
typedef enum {
	SIMD_OWNER_NWD = 1U,
	SIMD_OWNER_REL1 = 2U,
} simd_owner_t;

/*
 * The fpu_state is saved or restored across simd context switch if SIMD type
 * is SIMD_FPU.
 */
struct fpu_regs {
	uint8_t q[FPU_REGS_SIZE];
} __aligned(sizeof(__uint128_t));

/*
 * SVE registers for architecture max supported vector length of 2048 bits.
 * This whole sve_regs is saved or restored across simd context switch if SIMD
 * type flags has SIMD_TFLAG_SVE set.
 */
struct sve_regs {
	uint8_t z[SVE_Z_REGS_SIZE(SVE_VQ_ARCH_MAX)];
	uint8_t p[SVE_P_REGS_SIZE(SVE_VQ_ARCH_MAX)];
	uint8_t ffr[SVE_FFR_REGS_SIZE(SVE_VQ_ARCH_MAX)];
} __aligned(sizeof(__uint128_t));

/* SIMD configuration */
struct simd_config {
	/* SVE enabled flag */
	bool sve_en;

	/*
	 * SVE vector length represented in quads. Can range from 0x0 to 0xf,
	 * each increment adds 128 bits to the vector length.
	 * 0x0 - 128 bits VL (arch min)
	 * 0xf - 2048 bits VL (arch max)
	 */
	uint32_t sve_vq;

	/* SME enabled flag */
	bool sme_en;
};

/* This structure holds the SIMD related EL2 registers */
struct simd_el2_regs {
	uint64_t zcr_el2;
};

struct simd_context {
	/* Owner of this context, can be SIMD_OWNER_NWD or SIMD_OWNER_REL1 */
	simd_owner_t owner;

	/* Bitwise OR of type flags */
	uint32_t tflags;

	/* Bitwise OR of status flags */
	uint32_t sflags;

	/* EL2 trap register for this context */
	uint64_t cptr_el2;

	/*
	 * SME specific Streaming vector control register. Contains CPU global
	 * PSTATE.SM and PSTATE.ZA flags.
	 */
	uint64_t svcr;

	/*
	 * EL2 config registers.
	 * SIMD_OWNER_NWD: RMM intializes based on CPU supported configuration
	 * SIMD_OWNER_REL1: RMM intializes based on Realm configuration
	 *
	 * These registers are written to system before save or restoring
	 * vector registers.
	 */
	struct simd_el2_regs el2_regs;

	/*
	 * Other world (NS) EL2 Registers:
	 * RMM will save and restore NS world EL2 registers since EL3 is not
	 * saving it (only for SIMD_OWNER_NWD).
	 */
	struct simd_el2_regs ns_el2_regs;

	/*
	 * SIMD related control and status sysregs. These registers need to be
	 * handled separately from the actual SIMD vector registers. Saved and
	 * restored across context switch.
	 */
	struct {
		/* FPU control and status system registers */
		uint64_t fpsr;
		uint64_t fpcr;

		/* SVE control register (EL1) */
		uint64_t zcr_el12;
	} ctl_status_regs;

	/*
	 * SIMD data registers:
	 * - CPU FPU Q registers.
	 * - CPU SVE scalable vector registers. Currently 'sve_regs' structure
	 *   reserves space for max supported vector length by the architecture.
	 */
	union {
		struct fpu_regs fpu;
		struct sve_regs sve;
	} vregs;
};

/*
 * Since we access fpu_state and sve_state in assembly code make sure the
 * offset of all fields are correct.
 *
 * TODO: Auto generate header file simd-asm-offsets.h during build and use it
 * in assembly routines.
 */
COMPILER_ASSERT_NO_CBMC((U(offsetof(struct fpu_regs, q))) == FPU_REGS_OFFSET_Q);
COMPILER_ASSERT_NO_CBMC((U(offsetof(struct sve_regs, z))) == SVE_REGS_OFFSET_Z);
COMPILER_ASSERT_NO_CBMC((U(offsetof(struct sve_regs, p))) == SVE_REGS_OFFSET_P);
COMPILER_ASSERT_NO_CBMC((U(offsetof(struct sve_regs, ffr))) == SVE_REGS_OFFSET_FFR);

/* Initialize SIMD layer based on CPU support for FPU or SVE */
void simd_init(void);

/* Returns the CPU SIMD config discovered during the init time */
int simd_get_cpu_config(struct simd_config *simd_cfg);

/* Initialize the SIMD context in RMM corresponding to NS world or Realm */
int simd_context_init(simd_owner_t owner, struct simd_context *simd_ctx,
		      const struct simd_config *simd_cfg);

/* Switch SIMD context by saving the 'ctx_in' and restoring the 'ctx_out' */
struct simd_context *simd_context_switch(struct simd_context *ctx_save,
					 struct simd_context *ctx_restore);

/*
 * Returns 'true' if the current CPU's SIMD (FPU/SVE) live state is saved in
 * memory else 'false'.
 */
bool simd_is_state_saved(void);

/* Set or clear SVE hint bit passed by SMCCCv1.3 to SIMD context status */
void simd_update_smc_sve_hint(struct simd_context *ctx, bool sve_hint);

static inline void simd_context_save(struct simd_context *ctx)
{
	(void)simd_context_switch(ctx, NULL);
}

static inline void simd_context_restore(struct simd_context *ctx)
{
	(void)simd_context_switch(NULL, ctx);
}

/*
 * Enable SIMD related flags like FPEN, ZEN, SMEN in 'cptr_val' based on SIMD
 * configuration.
 */
#define SIMD_ENABLE_CPTR_FLAGS(simd_cfg, cptr_val)				\
	do {									\
		(cptr_val) &= ~(CPTR_EL2_VHE_SIMD_MASK);			\
										\
		(cptr_val) |= INPLACE(CPTR_EL2_VHE_FPEN,			\
				      CPTR_EL2_VHE_FPEN_NO_TRAP_11);		\
										\
		if ((simd_cfg)->sve_en) {					\
			(cptr_val) |= INPLACE(CPTR_EL2_VHE_ZEN,			\
					      CPTR_EL2_VHE_ZEN_NO_TRAP_11);	\
		}								\
										\
		if ((simd_cfg)->sme_en) {					\
			(cptr_val) |= INPLACE(CPTR_EL2_VHE_SMEN,		\
					      CPTR_EL2_VHE_SMEN_NO_TRAP_11);	\
		}								\
	} while (false)

/* Disable all SIMD related flags like FPEN, ZEN, SMEN in 'cptr_val' */
#define SIMD_DISABLE_ALL_CPTR_FLAGS(cptr_val)					\
	do {									\
		(cptr_val) &= ~(CPTR_EL2_VHE_SIMD_MASK);			\
										\
		(cptr_val) |= INPLACE(CPTR_EL2_VHE_FPEN,			\
				      CPTR_EL2_VHE_FPEN_TRAP_ALL_00) |		\
			      INPLACE(CPTR_EL2_VHE_ZEN,				\
				      CPTR_EL2_VHE_ZEN_TRAP_ALL_00) |		\
			      INPLACE(CPTR_EL2_VHE_SMEN,			\
				      CPTR_EL2_VHE_SMEN_TRAP_ALL_00);		\
	} while (false)

/*
 * RMM support to use SIMD (FPU) at REL2
 */
#ifdef RMM_FPU_USE_AT_REL2
#define SIMD_FPU_ALLOW(expression)				\
	do {							\
		unsigned long cptr_el2 = read_cptr_el2();	\
								\
		assert(simd_is_state_saved() == true);		\
		write_cptr_el2(cptr_el2 | INPLACE(CPTR_EL2_VHE_FPEN,\
				CPTR_EL2_VHE_FPEN_NO_TRAP_11));	\
		isb();						\
								\
		(expression);					\
								\
		write_cptr_el2(cptr_el2);			\
		isb();						\
	} while (false)

#define SIMD_IS_FPU_ALLOWED()	(simd_is_state_saved() && is_fpen_enabled())

#else /* !RMM_FPU_USE_AT_REL2 */
#define SIMD_FPU_ALLOW(expression)				\
	do {							\
		(expression);					\
	} while (false)

#define SIMD_IS_FPU_ALLOWED() (true)

#endif /* RMM_FPU_USE_AT_REL2 */

#endif /* __ASSEMBLER__ */

#endif /* SIMD_H */
