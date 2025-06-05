/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch_features.h>
#include <assert.h>
#include <mec.h>
#include <sizes.h>
#include <stdint.h>

/*
 * Before enabling the MMU, the RMM code is written and read with MECID 0, so
 * the only possible value at the moment for RMM is 0.
 */
#define RESERVED_MECID_SYSTEM	0

/*
 * RMM is loaded by EL3 with MEC disabled. This means that RMM must use
 * a MECID of 0 for its own execution and Data.
 */
void mec_init_mmu(void)
{
	uint16_t mecid;

	/*
	 * Since this function is enabled with MMU disabled, it should not
	 * update any global data.
	 */
	assert(!is_mmu_enabled());

	if ((!is_feat_sctlr2x_present()) || (!is_feat_mec_present())) {
		return;
	}

	mecid = RESERVED_MECID_SYSTEM;

	/* MECID_* reset to UNKNOWN values */
	write_mecid_p0_el2(mecid);
	write_mecid_p1_el2(mecid);
	write_mecid_a0_el2(mecid);
	write_mecid_a1_el2(mecid);
	write_vmecid_p_el2(mecid);
	write_vmecid_a_el2(mecid);
	isb();

	write_sctlr2_el2(read_sctlr2_el2() | SCTLR2_ELx_EMEC_BIT);
}
