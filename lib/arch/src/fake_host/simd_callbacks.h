/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef SIMD_CALLBACKS_H
#define SIMD_CALLBACKS_H

#include <simd.h>

/*
 * Callback identifiers for all the possible SIMD callbacks that can be
 * installed by the unit tests.
 */
enum simd_cb_ids {
	FPU_SAVE_REGS,
	FPU_RESTORE_REGS,
	SVE_RDVL,
	SVE_SAVE_REGS,
	SVE_RESTORE_REGS,
	SVE_CLEAR_P_FFR_REGS,
	SIMD_CB_IDS_MAX
};

/*
 * The types of callbacks that can be registered are defined below.
 */

/*
 * Corresponds to callback IDs FPU_SAVE_REGS and FPU_RESTORE_REGS.
 *
 * These two functions have the same argument and return types so they can use
 * the same callback type.
 */
typedef void (*cb_fpu_save_restore)(struct fpu_regs *regs);

/*
 * Corresponds to callback ID SVE_RDVL.
 */
typedef uint32_t (*cb_sve_rdvl)(void);

/*
 * Corresponds to callback IDs SVE_SAVE_REGS and SVE_RESTORE_REGS.
 *
 * These two functions have the same argument and return types so they can use
 * the same callback type.
 */
typedef void (*cb_sve_save_restore)(struct sve_regs *regs,
				    bool save_restore_ffr);

/*
 * Corresponds to callback ID SVE_CLEAR_P_FFR_REGS.
 */
typedef void (*cb_sve_clear_regs)(void);

union simd_cbs {
	cb_fpu_save_restore fpu_save_restore_regs;
	cb_sve_rdvl sve_rdvl;
	cb_sve_save_restore sve_save_restore_regs;
	cb_sve_clear_regs sve_clear_regs;
};

/*
 * Register a callback to be used for testing, overwriting any existing one.
 */
void simd_test_register_callback(enum simd_cb_ids id, union simd_cbs cb);

/*
 * Unregister a callback for testing.
 */
void simd_test_unregister_callback(enum simd_cb_ids id);

#endif /* SIMD_CALLBACKS_H */
