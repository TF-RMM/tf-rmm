/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <tb_common.h>
#include <tb_granules.h>

/* The valid range is smaller than in the specification */
bool valid_num_root_rtts(unsigned int num_root_rtts)
{
	return num_root_rtts >= 1 && num_root_rtts <= 2;
}

struct granule *init_rtt_root_page(unsigned int num_root_rtts)
{
	__CPROVER_assert(valid_num_root_rtts(num_root_rtts),
		"Internal: `_init_rtt_root_page` valid numbers of root rtt");

	/* The first root rtt granule is granules[index]. */
	size_t index = next_index();
	struct granule *before = &granules[index];

	for (size_t i = index; i < index + num_root_rtts && i < index + 16; ++i) {
		__CPROVER_assume(unused_index(i));
		struct granule g = init_granule();

		__CPROVER_assume(g.state == GRANULE_STATE_RTT);
		/* We assume there are at least one unused slot. */
		__CPROVER_assume(g.refcount < (GRANULE_SIZE / sizeof(uint64_t)));

		char rtt_content[GRANULE_SIZE] = { 0 };
		struct granule *after = inject_granule_at(&g, rtt_content, sizeof(rtt_content), i);
	}
	return &granules[index];
}
