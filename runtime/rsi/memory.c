/*
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <realm.h>
#include <ripas.h>
#include <rsi-memory.h>
#include <smc-rsi.h>
#include <status.h>

bool handle_rsi_ipa_state_set(struct rec *rec, struct rmi_rec_exit *rec_exit)
{
	unsigned long start = rec->regs[1];
	unsigned long size = rec->regs[2];
	unsigned long end = start + size;
	enum ripas ripas = (enum ripas)rec->regs[3];

	if (ripas > RMI_RAM) {
		return true;
	}

	if (!GRANULE_ALIGNED(start)) {
		return true;
	}

	if (!GRANULE_ALIGNED(size)) {
		return true;
	}

	if (end <= start) {
		/* Size is zero, or range overflows */
		return true;
	}

	if (!region_in_rec_par(rec, start, end)) {
		return true;
	}

	rec->set_ripas.start = start;
	rec->set_ripas.end = end;
	rec->set_ripas.addr = start;
	rec->set_ripas.ripas = ripas;

	rec_exit->exit_reason = RMI_EXIT_RIPAS_CHANGE;
	rec_exit->ripas_base = start;
	rec_exit->ripas_size = size;
	rec_exit->ripas_value = (unsigned int)ripas;

	return false;
}

rsi_status_t handle_rsi_ipa_state_get(struct rec *rec, unsigned long ipa,
				      enum ripas *ripas_ptr)
{
	bool s2tte_destroyed;

	if (!GRANULE_ALIGNED(ipa)) {
		return RSI_ERROR_INPUT;
	}

	if (!addr_in_rec_par(rec, ipa)) {
		return RSI_ERROR_INPUT;
	}

	realm_ipa_get_ripas(rec, ipa, ripas_ptr, &s2tte_destroyed);
	if (s2tte_destroyed == true) {
		/* TODO: handle destroyed state appropriately */
		return RSI_ERROR_INPUT;
	}

	return RSI_SUCCESS;
}
