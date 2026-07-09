/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef RTT_INTERNAL_H
#define RTT_INTERNAL_H

#include <s2tt.h>
#include <stdbool.h>

struct rd;

/*
 * Validate the map_addr value passed to
 * RMI_RTT_*, RMI_DATA_* and RMI_DEV_MEM_* commands.
 */
bool validate_map_addr(unsigned long map_addr,
		       long level,
		       struct rd *rd);

/*
 * Helper to reset the Access Permissions for a protected entry.
 */
unsigned long default_protected_ap(struct s2tt_context *s2_ctx);

/*
 * Count the leading bytes of the block described by @s2tte that are
 * not pinned by an auxiliary mapping. Returns the offset (in bytes)
 * of the first granule within the block whose refcount is non-zero,
 * or the block size if every granule is free of aux mappings.
 *
 * Caller must hold the RTT lock covering @s2tte.
 */
unsigned long not_aux_mappings(struct s2tt_context *s2_ctx,
			       unsigned long s2tte, long level);

#endif /* RTT_INTERNAL_H */
