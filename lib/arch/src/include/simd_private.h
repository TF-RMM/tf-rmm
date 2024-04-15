/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef SIMD_PRIVATE_H
#define SIMD_PRIVATE_H

#include <stdbool.h>
#include <stdint.h>

/* convert SVE VL in bytes to VQ */
#define SVE_VL_TO_VQ(vl_bytes)	((((vl_bytes) << 3) / 128U) - 1U)

/*
 * Save current FPU registers to memory pointed by `fpu_regs`. FPU trap needs
 * to be disabled before calling this function.
 */
void fpu_save_registers(struct fpu_regs *regs);

/*
 * Restore FPU context from memory pointed by `fpu_state` to FPU registers. FPU
 * trap needs to be disabled before calling this function.
 */
void fpu_restore_registers(struct fpu_regs *regs);

/*
 * Return the length of one vector register in bytes. SVE trap needs to be
 * disabled before calling this function.
 */
uint32_t sve_rdvl(void);

/*
 * Save SVE vector registers Z/P/FFR to memory pointed by `sve_regs`. SVE trap
 * needs to be disabled before calling this function.
 */
void sve_save_vector_registers(struct sve_regs *regs, bool save_ffr);

/*
 * Restore SVE vector registers from memory pointed by 'sve_regs' to Z/P/FFR
 * registers. SVE trap needs to be disabled before calling this function.
 */
void sve_restore_vector_registers(struct sve_regs *regs, bool restore_ffr);

/* Clear SVE P and FFR registers */
void sve_clear_p_ffr_registers(void);

/* Returns 'true' when CPU in Streaming SVE mode, else 'false' */
static inline bool is_sme_sm(void)
{
	return ((read_svcr() & SVCR_SM_BIT) != 0U);
}

/* Returns 'true' when FEAT_SME_FA64 is enabled at the current exception level */
static inline bool sme_feat_fa64_enabled(void)
{
	return ((read_smcr_el2() & SMCR_EL2_FA64_BIT) != 0U);
}

/******************************************************************
 * Private APIs for unit tests
 *****************************************************************/

/*
 * Resets the values of the static global variables g_simd_cfg, g_simd_init_done
 * and g_simd_state_saved[].
 *
 * NOTE: This should only be called during unit tests, to provide a clean state
 * for each test.
 */
void simd_reset(void);

#endif /* SIMD_PRIVATE_H */
