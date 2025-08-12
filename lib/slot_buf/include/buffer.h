/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef BUFFER_H
#define BUFFER_H

#include <granule.h>
#include <smc-rmi.h>
#include <stddef.h>
#include <utils_def.h>

/* NOLINTNEXTLINE(cert-int09-c) */
enum buffer_slot {
	/*
	 * NS.
	 */
	SLOT_NS = 0,

	/*
	 * RMM-private.
	 */
	SLOT_RD,
	SLOT_REC,
	SLOT_REC2,		/* Some commands access two REC granules at a time*/
	SLOT_REC_TARGET,	/* Target REC for interrupts */
	SLOT_REC_AUX0,		/* Reserve slots for max rec auxiliary granules
				 * so that all of them can be mapped at once.
				 * If the max aux granules is 0, no slots will
				 * be reserved.
				 */
	SLOT_RTT = U(SLOT_REC_AUX0) + MAX_REC_AUX_GRANULES,
	SLOT_RTT2,		/* Some commands access two RTT granules at a time
				 * Both the RTT slots use Realm MECID when FEAT_MEC
				 * is present.
				 */
	SLOT_PDEV,		/* Slot for Physical device object */
	SLOT_PDEV_AUX0,		/* Slots for PDEV auxiliary granules */
	SLOT_VDEV = U(SLOT_PDEV_AUX0) + PDEV_PARAM_AUX_GRANULES_MAX,
	SLOT_VDEV_AUX0,		/* Slots for VDEV auxiliary granules */
	/* Slot to map Realm Data. This slot uses the Realm MECID when FEAT_MEC is present. */
	SLOT_REALM = U(SLOT_VDEV_AUX0) + VDEV_PARAM_AUX_GRANULES_MAX,
	SLOT_EL3_TOKEN_SIGN_REC,	/* Slot for target REC during EL3 sign flow */
	SLOT_EL3_TOKEN_SIGN_AUX0,	/* Slots for AUX granules on target REC for EL3 sign flow */
	/* TODO: The number of slots for app framework can be optimised as in
	 * theory it should be enough to have a single page being mapped, this
	 * is just for convenience.
	 */
	SLOT_APP_INIT = U(SLOT_EL3_TOKEN_SIGN_AUX0) + MAX_REC_AUX_GRANULES,
	SLOT_APP_PAGE_TABLE,
	SLOT_APP_SHARED,
	NR_CPU_SLOTS
};

static inline enum buffer_slot safe_cast_to_slot(enum buffer_slot slot, unsigned int val)
{
	switch (slot) {
	case SLOT_REC_AUX0:
		assert(val < MAX_REC_AUX_GRANULES);
		break;
	case SLOT_PDEV_AUX0:
		assert(val < PDEV_PARAM_AUX_GRANULES_MAX);
		break;
	default:
		assert(false);
	}
	return (enum buffer_slot)((unsigned int)slot + val); /* NOLINT(clang-analyzer-optin.core.EnumCastOutOfRange) */
}

bool check_cpu_slots_empty(void);
void *buffer_granule_map(struct granule *g, enum buffer_slot slot);
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

bool ns_buffer_write_unaligned(enum buffer_slot slot,
			       struct granule *ns_gr,
			       unsigned int offset,
			       size_t size,
			       void *src,
			       size_t *ns_start_offset);

/*
 * Finishes initializing the slot buffer mechanism.
 * This function should be called after the MMU is enabled, during the
 * warmboot path.
 */
void slot_buf_finish_warmboot_init(void);

/*
 * Maps the `num_aux` SLOT_REC_AUX granules.
 */
void *buffer_rec_aux_granules_map(struct granule *g_rec_aux[],
				  unsigned int num_aux);

/*
 * Maps and zeroes the `num_aux` SLOT_REC_AUX granules.
 */
void *buffer_rec_aux_granules_map_zeroed(struct granule *g_rec_aux[],
				  unsigned int num_aux);

/*
 * Maps the `num_aux` granules in REC to SLOT_EL3_TOKEN_SIGN_AUX0.
 */
void *buffer_rec_aux_granules_map_el3_token_sign_slot(
					      struct granule *g_rec_aux[],
						   unsigned int num_aux);

/*
 * Unmaps the `num_aux` SLOT_REC_AUX or SLOT_EL3_TOKEN_SIGN_AUX0 buffers starting
 * with the one passed at the beginning of `rec_aux`.
 */
void buffer_rec_aux_unmap(void *rec_aux, unsigned int num_aux);

/*
 * Maps the `num_aux` granules at 'g_pdev_aux' to buffer slot starting
 * SLOT_PDEV_AUX0.
 */
void *buffer_pdev_aux_granules_map(struct granule *g_pdev_aux[],
				   unsigned int num_aux);

/*
 * Maps and zeroes the `num_aux` granules at 'g_pdev_aux' to buffer slot
 * starting SLOT_PDEV_AUX0.
 */
void *buffer_pdev_aux_granules_map_zeroed(struct granule *g_pdev_aux[],
				   unsigned int num_aux);

/* Unmaps the `num_aux` granules from slot starting SLOT_PDEV_AUX0 */
void buffer_pdev_aux_unmap(void *pdev_aux, unsigned int num_aux);

static inline void *buffer_granule_map_zeroed(struct granule *g, enum buffer_slot slot)
{
	void *buf = buffer_granule_map(g, slot);
	granule_memzero_mapped(buf);
	return buf;
}

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
