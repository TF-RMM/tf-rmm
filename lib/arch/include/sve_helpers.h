/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef SVE_H
#define SVE_H

#include <arch.h>

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
#define SVE_VQ_ARCH_MAX		((1 << ZCR_EL2_LEN_WIDTH) - 1)

/* convert SVE VL in bytes to VQ */
#define SVE_VL_TO_VQ(vl_bytes)	((((vl_bytes) << 3) / 128) - 1)

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

/* These defines are required by compiler assert to check offsets */
#define SVE_STATE_OFFSET_Z	0U
#define SVE_STATE_OFFSET_P	(SVE_Z_REGS_SIZE(SVE_VQ_ARCH_MAX))
#define SVE_STATE_OFFSET_FFR	(SVE_STATE_OFFSET_P + \
				 SVE_P_REGS_SIZE(SVE_VQ_ARCH_MAX))
#define SVE_STATE_OFFSET_ZCR_EL12	(SVE_STATE_OFFSET_FFR + \
				 SVE_FFR_REGS_SIZE(SVE_VQ_ARCH_MAX))
#define SVE_STATE_OFFSET_FPSR	(SVE_STATE_OFFSET_ZCR_EL12 + \
				 sizeof(uint64_t))
#define SVE_STATE_OFFSET_FPCR	(SVE_STATE_OFFSET_FPSR + sizeof(uint64_t))

/* Since we use these offsets in assembly code make sure they are correct. */
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

uint64_t sve_rdvl(void);
void sve_save_z_state(uint8_t *regs_base);
void sve_save_p_ffr_state(uint8_t *regs_base);
void sve_save_zcr_fpu_state(uint8_t *regs_base);
void sve_restore_z_state(uint8_t *regs_base);
void sve_restore_ffr_p_state(uint8_t *regs_base);
void sve_restore_zcr_fpu_state(uint8_t *regs_base);

#endif /* SVE_H */
