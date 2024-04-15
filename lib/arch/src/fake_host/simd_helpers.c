/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <simd.h>
#include <simd_callbacks.h>
#include <string.h>

uintptr_t callbacks[SIMD_CB_IDS_MAX];

static uintptr_t get_callback(enum simd_cb_ids id)
{
	return callbacks[id];
}

void fpu_save_registers(struct fpu_regs *regs)
{
	cb_fpu_save_restore cb =
			       (cb_fpu_save_restore)get_callback(FPU_SAVE_REGS);

	if (cb != NULL) {
		cb(regs);
	}
}

void fpu_restore_registers(struct fpu_regs *regs)
{
	cb_fpu_save_restore cb =
			    (cb_fpu_save_restore)get_callback(FPU_RESTORE_REGS);

	if (cb != NULL) {
		cb(regs);
	}
}

uint32_t sve_rdvl(void)
{
	cb_sve_rdvl cb = (cb_sve_rdvl)get_callback(SVE_RDVL);

	if (cb != NULL) {
		return cb();
	}

	return 0;
}

void sve_save_vector_registers(struct sve_regs *regs, bool save_ffr)
{
	cb_sve_save_restore cb =
			       (cb_sve_save_restore)get_callback(SVE_SAVE_REGS);

	if (cb != NULL) {
		cb(regs, save_ffr);
	}
}

void sve_restore_vector_registers(struct sve_regs *regs, bool restore_ffr)
{
	cb_sve_save_restore cb =
			    (cb_sve_save_restore)get_callback(SVE_RESTORE_REGS);

	if (cb != NULL) {
		cb(regs, restore_ffr);
	}
}

void sve_clear_p_ffr_registers(void)
{
	cb_sve_clear_regs cb =
			  (cb_sve_clear_regs)get_callback(SVE_CLEAR_P_FFR_REGS);

	if (cb != NULL) {
		cb();
	}
}

/******************************************************************
 * APIs for test callbacks
 *****************************************************************/

void simd_test_register_callback(enum simd_cb_ids id, union simd_cbs cb)
{
	assert(id < SIMD_CB_IDS_MAX);
	callbacks[id] = (uintptr_t)cb.fpu_save_restore_regs;
}

void simd_test_unregister_callback(enum simd_cb_ids id)
{
	callbacks[id] = (uintptr_t)NULL;
}
