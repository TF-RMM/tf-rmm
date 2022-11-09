/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef SVE_H
#define SVE_H

#include <arch.h>
#include <utils_def.h>

/*
 * SVE vector length in bytes and derived values
 */
#define SVE_VLA_ZCR_LEN_BITS	UL(4)
#define SVE_VLA_LEN_MAX		(UL(1) << SVE_VLA_ZCR_LEN_BITS)
#define SVE_VLA_ZCR_LEN_MAX	(SVE_VLA_LEN_MAX - UL(1))
#define SVE_VLA_VL_MIN		UL(16)
#define SVE_VLA_VL_MAX		(SVE_VLA_VL_MIN * SVE_VLA_LEN_MAX)
#define SVE_VLA_Z_REGS_MAX	UL(32)
#define SVE_VLA_P_REGS_MAX	UL(16)
#define SVE_VLA_FFR_REGS_MAX	UL(1)
#define SVE_VLA_Z_LEN_MAX	(SVE_VLA_VL_MAX * SVE_VLA_Z_REGS_MAX)
#define SVE_VLA_P_LEN_MAX	((SVE_VLA_VL_MAX * SVE_VLA_P_REGS_MAX) >> UL(3))
#define SVE_VLA_FFR_LEN_MAX	((SVE_VLA_VL_MAX * SVE_VLA_FFR_REGS_MAX) >> \
				 UL(3))
#define SVE_ZCR_FP_REGS_NUM	UL(4)

#ifndef __ASSEMBLER__

/*
 * SVE context structure. Align on cache writeback granule to minimise cache line
 * thashing when allocated as an array for use by each CPU.
 */
struct sve_state {
	unsigned long zcr_fpu[SVE_ZCR_FP_REGS_NUM];
	unsigned char z[SVE_VLA_Z_LEN_MAX];
	unsigned char p_ffr[SVE_VLA_P_LEN_MAX + SVE_VLA_FFR_LEN_MAX];
} __attribute__((aligned(CACHE_WRITEBACK_GRANULE)));

void save_sve_zcr_fpu_state(unsigned long *data);
void save_sve_z_state(unsigned char *data);
void save_sve_p_ffr_state(unsigned char *data);

void restore_sve_zcr_fpu_state(unsigned long *data);
void restore_sve_z_state(unsigned char *data);
void restore_sve_p_ffr_state(unsigned char *data);

void save_sve_state(struct sve_state *sve);
void restore_sve_state(struct sve_state *sve);

#endif /* __ASSEMBLER__ */

#endif /* __SVE_H_ */
