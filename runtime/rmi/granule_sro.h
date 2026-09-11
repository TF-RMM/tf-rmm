/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef GRANULE_SRO_H
#define GRANULE_SRO_H

struct smc_result;

/*
 * Start delegation of a validated, non-empty, Granule-aligned
 * Host range. The caller must hold no Granule lock and initialize @res->x[0]
 * to RMI_ERROR_INPUT and @res->x[1] to @addr. The operation returns its RMI
 * status and progress address or sealed SRO handle through @res. No Granule
 * lock remains held on return; an incomplete operation retains its SRO state.
 */
void granule_delegate_start(unsigned long addr, unsigned long end_addr,
			    struct smc_result *res);

/*
 * Resume the matching range operation for RMI_OP_CONTINUE. The generic SRO
 * dispatcher must own the context and is responsible for sealing it again
 * after RMI_INCOMPLETE or releasing it after a terminal result. @res receives
 * the continuation result; no Granule lock remains held on return.
 */
void granule_delegate_continue(unsigned long fid, struct smc_result *res);

#endif /* GRANULE_SRO_H */
