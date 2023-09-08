/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <simd.h>

void fpu_save_registers(struct fpu_regs *regs)
{
	(void)regs;
}

void fpu_restore_registers(struct fpu_regs *regs)
{
	(void)regs;
}

uint32_t sve_rdvl(void)
{
	return 0U;
}

void sve_save_vector_registers(struct sve_regs *regs, bool save_ffr)
{
	(void)regs;
	(void)save_ffr;
}

void sve_restore_vector_registers(struct sve_regs *regs, bool restore_ffr)
{
	(void)regs;
	(void)restore_ffr;
}

void sve_clear_p_ffr_registers(void)
{
}
