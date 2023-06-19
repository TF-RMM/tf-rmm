/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <simd_private.h>

void fpu_save_state(uint8_t *regs_base)
{
	(void)regs_base;
}

void fpu_restore_state(const uint8_t *regs_base)
{
	(void)regs_base;
}

uint64_t sve_rdvl(void)
{
	return 0;
}

void sve_save_zcr_fpu_state(uint8_t *regs_base)
{
	(void)regs_base;
}

void sve_save_z_state(uint8_t *regs_base)
{
	(void)regs_base;
}

void sve_save_p_ffr_state(uint8_t *regs_base)
{
	(void)regs_base;
}

void sve_restore_zcr_fpu_state(uint8_t *regs_base)
{
	(void)regs_base;
}

void sve_restore_z_state(uint8_t *regs_base)
{
	(void)regs_base;
}

void sve_restore_ffr_p_state(uint8_t *regs_base)
{
	(void)regs_base;
}
