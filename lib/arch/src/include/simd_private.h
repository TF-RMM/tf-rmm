/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef SIMD_PRIVATE_H
#define SIMD_PRIVATE_H

#include <stdint.h>

/* convert SVE VL in bytes to VQ */
#define SVE_VL_TO_VQ(vl_bytes)	((((vl_bytes) << 3) / 128U) - 1U)

/*
 * Save/restore FPU context to/from the `fpu_state` passed as parameter. The FPU
 * instruction trap needs to be disabled before calling these functions.
 * Can be used for context switching.
 */
void fpu_save_state(uint8_t *regs_base);
void fpu_restore_state(const uint8_t *regs_base);

uint64_t sve_rdvl(void);
void sve_save_z_state(uint8_t *regs_base);
void sve_save_p_ffr_state(uint8_t *regs_base);
void sve_save_zcr_fpu_state(uint8_t *regs_base);
void sve_restore_z_state(uint8_t *regs_base);
void sve_restore_ffr_p_state(uint8_t *regs_base);
void sve_restore_zcr_fpu_state(uint8_t *regs_base);

#endif /* SIMD_PRIVATE_H */
