/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors
 */

#ifndef PAUTH_H
#define PAUTH_H

#include <stdint.h>

struct pauth_state {
	uint64_t apiakeylo_el1;
	uint64_t apiakeyhi_el1;
	uint64_t apibkeylo_el1;
	uint64_t apibkeyhi_el1;
	uint64_t apdakeylo_el1;
	uint64_t apdakeyhi_el1;
	uint64_t apdbkeylo_el1;
	uint64_t apdbkeyhi_el1;
	uint64_t apgakeylo_el1;
	uint64_t apgakeyhi_el1;
};

/***********************************************************************
 * Pauth helper functions
 **********************************************************************/
void pauth_init_enable_el2(void);
void pauth_restore_rmm_keys(void);
void pauth_save_realm_keys(struct pauth_state *pauth);
void pauth_restore_realm_keys(struct pauth_state *pauth);

#endif /* PAUTH_H */
