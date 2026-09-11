/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef RMM_EL3_GPI_H
#define RMM_EL3_GPI_H

#include <stdbool.h>

/* Zero-initialize for a new PAS transition; retain across retries and yields. */
struct rmm_el3_gpi_state {
	unsigned long cookie;	/* Valid only while incomplete is true. */
	bool incomplete;	/* EL3 retains an operation requiring continuation. */
};

/*
 * Advance a caller-owned PAS transition over [@addr, @addr + @size).
 * @delegate selects Realm PAS when true, otherwise NS PAS. The range must be
 * nonempty and Granule-aligned, with no address overflow. @processed_size is
 * the accumulated completed prefix, initially zero and smaller than @size.
 * @state must be zero-initialized for a new operation. Retain both the state
 * and progress, and keep the range and direction unchanged across calls.
 *
 * Issue at most one FIRME request, or use the synchronous legacy interface.
 * Legacy delegation stops after a completed Granule if an interrupt is pending.
 * Add this invocation's progress even when EL3 reports an error. INCOMPLETE
 * and continued BUSY retain the returned cookie; other results clear it, so
 * the next invocation issues GPI_SET for the remaining suffix.
 *
 * Return the EL3 status independently of accumulated progress. The caller
 * owns sanitization, granule transitions, yielding and Host reporting. No
 * SRO is allocated and no Granule lock is acquired. Before undelegating, the
 * caller must own the complete range and finish any required sanitization.
 * Undelegation may succeed, remain incomplete or be busy; a conflict or other
 * rejection violates this ownership contract, including during continuation.
 */
int rmm_el3_ifc_gtsi_step(unsigned long addr, unsigned long size, bool delegate,
			unsigned long *processed_size, struct rmm_el3_gpi_state *state);

#endif /* RMM_EL3_GPI_H */
