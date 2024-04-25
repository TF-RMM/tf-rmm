/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <realm.h>
#include <rec.h>
#include <tb_common.h>
#include <tb_granules.h>
#include <tb_rec.h>

static struct granule *init_aux_page(void)
{
	/* Add a rec_aux page */
	unsigned long aux_content = 0;
	struct granule g = init_granule();

	__CPROVER_assume(granule_unlocked_state(&g) == GRANULE_STATE_REC_AUX);
	struct granule *g_aux = inject_granule(&g, &aux_content, sizeof(aux_content));

	return g_aux;
}

struct granule *init_rec_page(struct granule *g_rd)
{
	struct granule g = init_granule();

	__CPROVER_assume(granule_unlocked_state(&g) == GRANULE_STATE_REC);
	struct rec rec = nondet_rec();

	rec.realm_info.g_rd = g_rd;

	/* It must be a valid g_rd */
	__CPROVER_assert(granule_unlocked_state(g_rd) == GRANULE_STATE_RD,
		"internal, `_init_rec_page` valid `g_rd`.");
	struct rd *realm = granule_metadata_ptr_to_buffer_ptr(g_rd);

	rec.realm_info.s2_ctx.g_rtt = realm->s2_ctx.g_rtt;
	rec.realm_info.s2_ctx.s2_starting_level = realm->s2_ctx.s2_starting_level;

	rec.num_rec_aux = 1;
	rec.g_aux[0] = init_aux_page();

	struct granule *g_rec = inject_granule(&g, &rec, sizeof(rec));

	/*
	 * Look up the newly created 'struct rec' in the grenule buffer, and set
	 * the g_rec field
	 */
	struct rec *rec_buf = (struct rec *)granule_metadata_ptr_to_buffer_ptr(g_rec);

	rec_buf->g_rec = g_rec;

	return g_rec;
}

struct rmm_rec Rec(uint64_t addr)
{
	if (!valid_pa(addr)) {
		return nondet_struct_rmm_rec();
	}

	struct rec *rec_ptr = pa_to_granule_buffer_ptr(addr);

	struct rmm_rec spec_rec = {
		/* TODO .attest_state = */
		.owner = granule_metadata_ptr_to_pa(rec_ptr->realm_info.g_rd),
		.flags.runnable = rec_ptr->runnable,
		.state = granule_refcount_read(rec_ptr->g_rec) == 0 ? REC_READY:REC_RUNNING,
		.ripas_addr = rec_ptr->set_ripas.addr,
		.ripas_top = rec_ptr->set_ripas.top,
		.ripas_value = rec_ptr->set_ripas.ripas_val,
		.ripas_destroyed = rec_ptr->set_ripas.change_destroyed,
		.host_call_pending = rec_ptr->host_call
	};

	for (int i = 0; i < rec_ptr->num_rec_aux && i < MAX_REC_AUX_GRANULES; ++i) {
		spec_rec.aux[i] = rec_ptr->g_aux[i];
	}
	return spec_rec;
}

bool AuxStateEqual(struct granule **aux, uint64_t num_aux, unsigned char state)
{
	struct granule *g_rec_aux = aux[0];
	unsigned char aux_state = granule_unlocked_state(g_rec_aux);

	__CPROVER_assert(num_aux >= 0 && num_aux <= MAX_REC_AUX_GRANULES,
		"internal: _AuxStateEqual range check.");
	for (int i = 0; i < num_aux && i < MAX_REC_AUX_GRANULES; ++i) {
		if (!PaIsDelegable(granule_metadata_ptr_to_pa(aux[i])) ||
					granule_unlocked_state(aux[i]) != state) {
			return false;
		}
	}
	return true;
}
