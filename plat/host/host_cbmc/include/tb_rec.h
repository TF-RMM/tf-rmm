/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <granule_types.h>

#define REC_READY false
#define REC_RUNNING true

struct Rec_Runnable {
	bool runnable;
};

/*
 * In the spec, Rec predicate must return a concrete rec.
 * We use a global fallback rec to by-pass this constraint.
 * There is a mismatch in the type of `struct rec` against spec.
 */
struct rmm_rec {
	enum attest_token_gen_state_t attest_state;
	struct granule *aux[MAX_REC_AUX_GRANULES];
	struct Rec_Runnable flags;
	uint64_t gprs[RPV_SIZE];
	uint64_t mpidr;
	uint64_t owner;
	uint64_t pc;
	bool state; /* Either `REC_READY` or `REC_RUNNING` */
	uint64_t ripas_addr;
	uint64_t ripas_top;
	enum ripas ripas_value;
	enum ripas_change_destroyed ripas_destroyed;
	bool host_call_pending;
};

struct granule *init_rec_page(struct granule *g_rd);
struct rmm_rec Rec(uint64_t addr);

bool AuxStateEqual(struct granule **aux, uint64_t num_aux, unsigned char state);

struct rmm_rec nondet_struct_rmm_rec(void);
struct rec nondet_rec(void);
