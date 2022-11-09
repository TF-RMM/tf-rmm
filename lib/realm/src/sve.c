/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch_helpers.h>
#include <assert.h>
#include <sve.h>

/*
 * Save the SVE context to memory.
 * The function saves the maximum implemented
 * SVE context size.
 */
void save_sve_state(struct sve_state *sve)
{
	assert(sve != NULL);

	save_sve_zcr_fpu_state(sve->zcr_fpu);
	save_sve_z_state(sve->z);
	save_sve_p_ffr_state(sve->p_ffr);
}

/*
 * Restore the SVE context from memory.
 * The function restores the maximum implemented
 * SVE context size.
 */
void restore_sve_state(struct sve_state *sve)
{
	assert(sve != NULL);

	restore_sve_z_state(sve->z);
	restore_sve_p_ffr_state(sve->p_ffr);
	restore_sve_zcr_fpu_state(sve->zcr_fpu);
}
