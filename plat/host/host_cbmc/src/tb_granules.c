/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include "buffer.h"
#include "granule.h"
#include "granule_types.h"
#include "host_defs.h"
#include "host_utils.h"
#include "platform_api.h"
#include "sizes.h"
#include "string.h"
#include "tb_common.h"
#include "tb_granules.h"

/* Chooses an arbitrary granule state. */
bool valid_granule_unlocked_state(unsigned char value)
{
	return value == GRANULE_STATE_NS
			|| value == GRANULE_STATE_DELEGATED
			|| value == GRANULE_STATE_RD
			|| value == GRANULE_STATE_REC
			|| value == GRANULE_STATE_REC_AUX
			|| value == GRANULE_STATE_DATA
			|| value == GRANULE_STATE_RTT;
}

/* Ref to `__granule_assert_unlocked_invariants` function in `granule.h`. */
bool valid_granule(struct granule value)
{
	if (is_granule_locked(&value)) {
		return false;
	}

	switch (granule_unlocked_state(&value)) {
	case GRANULE_STATE_NS:
	case GRANULE_STATE_DELEGATED:
	case GRANULE_STATE_DATA:
	case GRANULE_STATE_REC_AUX:
		return granule_refcount_read(&value) == 0;
	/*
	 * refcount is used to check if RD and associated granules can
	 * be freed because they're no longer referenced by any other
	 * object. Can be any non-negative number.
	 */
	case GRANULE_STATE_REC: return granule_refcount_read(&value) <= 1;
	case GRANULE_STATE_RTT: return granule_refcount_read(&value) >= 0 &&
		granule_refcount_read(&value) <= REFCOUNT_MAX;
	case GRANULE_STATE_RD: return true;
	default: return false;
	}
	return false;
}

struct granule init_granule(void)
{
	struct granule rst = nondet_struct_granule();

	__CPROVER_assume((granule_unlocked_state(&rst) >= GRANULE_STATE_NS) &&
			 (granule_unlocked_state(&rst) <= GRANULE_STATE_LAST));
	__CPROVER_assume(valid_granule(rst));
	return rst;
}

void init_granule_and_page(void)
{
	struct granule g = init_granule();
	/* just write one byte when call the `inject_granule` functions */
	char ns_granule[1] = { 0 };

	inject_granule(&g, ns_granule, sizeof(ns_granule));
}

/*
 * Implementation of pedicates
 */
bool AddrIsGranuleAligned(uint64_t addr)
{
	return GRANULE_ALIGNED(addr);
}

bool PaIsDelegable(uint64_t addr)
{
	return valid_pa(addr);
}

struct SPEC_granule Granule(uint64_t addr)
{
	if (!valid_pa(addr)) {
		struct SPEC_granule nd_granule = nondet_struct_SPEC_granule();
		__CPROVER_assume((nd_granule.state >= GRANULE_STATE_NS) &&
				 (nd_granule.state <= GRANULE_STATE_LAST));
		__CPROVER_assume(__CPROVER_enum_is_in_range(nd_granule.gpt));
		return nd_granule;
	}

	struct granule *result = pa_to_granule_metadata_ptr(addr);

	struct SPEC_granule spec_granule;

	spec_granule.state = granule_unlocked_state(result);

	switch (granule_unlocked_state(result)) {
	case GRANULE_STATE_NS:
		spec_granule.gpt = get_granule_gpt(addr);
		break;
	case GRANULE_STATE_RTT:
		spec_granule.gpt = GPT_NS;
		break;
	case GRANULE_STATE_RD:
	case GRANULE_STATE_DATA:
	case GRANULE_STATE_REC:
	case GRANULE_STATE_DELEGATED:
		spec_granule.gpt = GPT_REALM;
		break;
	default:
		spec_granule.gpt = GPT_AAP;
	}

	return spec_granule;
}
