/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef BUFFER_H
#define BUFFER_H

#include <assert.h>
#include <smc-rmi.h>
#include <stdbool.h>
#include <stddef.h>
#include <utils_def.h>

enum buffer_slot {
	/*
	 * NS.
	 */
	SLOT_NS,

	/*
	 * RMM-private.
	 */
	SLOT_DELEGATED,
	SLOT_RD,
	SLOT_REC,
	SLOT_REC2,		/* Some commands access two REC granules at a time*/
	SLOT_REC_TARGET,	/* Target REC for interrupts */
	SLOT_REC_AUX0,		/* Reserve slots for max rec auxiliary granules
				 * so that all of them can be mapped at once.
				 * If the max aux granules is 0, no slots will
				 * be reserved.
				 */
	SLOT_RTT = SLOT_REC_AUX0 + MAX_REC_AUX_GRANULES,
	SLOT_RTT2,		/* Some commands access two RTT granules at a time*/
	SLOT_RSI_CALL,
	NR_CPU_SLOTS
};

struct granule;

bool check_cpu_slots_empty(void);
void *granule_map(struct granule *g, enum buffer_slot slot);
void buffer_unmap(void *buf);

bool ns_buffer_read(enum buffer_slot slot,
		    struct granule *ns_gr,
		    unsigned int offset,
		    size_t size,
		    void *dest);

bool ns_buffer_write(enum buffer_slot slot,
		     struct granule *ns_gr,
		     unsigned int offset,
		     size_t size,
		     void *src);

/*
 * Finishes initializing the slot buffer mechanism.
 * This function should be called after the MMU is enabled, during the
 * warmboot path.
 */
void slot_buf_finish_warmboot_init(void);

/******************************************************************************
 * Internal APIs not meant to be invoked by generic RMM code.
 * These are exposed to facilitate testing.
 *****************************************************************************/

/*
 * Maps a given PA into the specified slot.
 *
 * On success, it returns the VA of the slot where the PA has been mapped to.
 * Otherwise, it will return NULL.
 */
void *buffer_map_internal(enum buffer_slot slot, unsigned long addr);

/*
 * Unmaps the slot buffer corresponding to the VA passed via `buf` argument.
 */
void buffer_unmap_internal(void *buf);

#endif /* BUFFER_H */
