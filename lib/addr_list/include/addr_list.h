/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */
#ifndef ADDR_LIST_H
#define ADDR_LIST_H

#include <assert.h>
#include <stdbool.h>
#include <stddef.h>
#include <utils_def.h>
#include <xlat_tables.h>

/*
 * Maximum number of `ranges` we allow the address list to have.
 * Note that this implementation does not allow the list to cross
 * granule, so in that case, the operation will just return INCOMPLETE.
 */
#define ADDR_LIST_MAX_RANGES	(GRANULE_SIZE / sizeof(unsigned long))

/* RmiAddrBlockSize to XLAT Level */
#define XLAT_LVL_FROM_ADR_LIST_SZ(x) ((long)XLAT_TABLE_LEVEL_MAX - (long)(x))


enum list_type {
	LIST_TYPE_INPUT = 1,
	LIST_TYPE_OUTPUT = 2,
};

/*
 * The structure implements the RMI Address List as it is described in the RMM
 * spec. The list may be of zero size and ignore `add` & `copy` requests.
 */
struct addr_list {
	unsigned long range_desc[ADDR_LIST_MAX_RANGES]; /* List of `ranges` */
	unsigned int count; /* Number of `ranges` in the list */
	unsigned int cur_idx; /* Current index in the list */
	unsigned int max_count; /* Cap on number of `ranges` */
	enum list_type type;/* Type of the list */
};

/*
 * Initializes the address list with zero `ranges`, the given type and
 * an upper bound on the number of `ranges` it will ever hold.
 *
 * Args:
 * - list: the address list to initialize.
 * - type: the type of the list (LIST_TYPE_INPUT or LIST_TYPE_OUTPUT).
 * - max_count: cap on the number of `range` descriptors the list will
 *              accept. Must be > 0 and <= ADDR_LIST_MAX_RANGES.
 *              addr_list_add_block() rejects an add that would create
 *              a new descriptor past this cap; in-place merges into an
 *              existing descriptor are unaffected.
 */
void addr_list_init(struct addr_list *list, enum list_type type,
		    unsigned int max_count);

/*
 * Adds a new memory block into the address list.
 * It tries to add the block to the `current range`. If it fails, it
 * moves the `current range` to the next range.
 * It returns false if the list cannot accept the block (when it is full).
 *
 * Args:
 * - list: the address list to add the block to.
 * - block_addr: the address of the memory block to add. It must be aligned to
 *		 the block size that matches the RTT level.
 * - rtt_level: the RTT level that matches the block size. It must be less than
 *		or equal to XLAT_TABLE_LEVEL_MAX.
 * - st: the status of the block.
 *
 * Returns:
 * - true if the block is added to the list.
 * - false if the block cannot be added to the list.
 */
bool addr_list_add_block(struct addr_list *list,
			 unsigned long block_addr,
			 int rtt_level,
			 unsigned long st);

/*
 * Adds an encoded RMI Address Range Descriptor to an input address list.
 * The descriptor is decoded and stored in the list's canonical format.
 *
 * Args:
 * - list: the input address list to add the descriptor to.
 * - desc: the encoded RMI Address Range Descriptor.
 *
 * Returns:
 * - true if the descriptor is added to the list.
 * - false if the list cannot accept the descriptor.
 */
bool addr_list_add_desc(struct addr_list *list, unsigned long desc);

/*
 * Removes the leading memory block from the address list. It returns its
 * address and the RTT level that matches its size.
 * It returns `false` if the list is empty.
 *
 * Args:
 * - list: the address list to consume the block from.
 * - block_addr: the address of the block is returned through this pointer.
 * - rtt_level: the RTT level that matches the block size is
 *		  returned through this pointer.
 * - st: the state of the block is returned through this pointer.
 *
 * Returns:
 * - true if the block is removed from the list.
 * - false if the list is empty and there is no block to remove.
 */
bool addr_list_reduce_first_block(struct addr_list *list,
			       unsigned long *block_addr,
			       int *rtt_level,
			       unsigned long *st);

/*
 * Reduces the entire contiguous block from the list and returns its base
 * address and total size in bytes. The list must contain at most one range
 * descriptor. Asserts that the total size is a power of 2 and that the base
 * address is aligned to the total size.
 *
 * Args:
 * - list: the address list to consume the block from.
 * - base_addr: the base address of the block is returned through this pointer.
 * - total_size: total size in bytes is returned through this pointer.
 * - st: the state of the block is returned through this pointer.
 *
 * Returns:
 * - true if a block was consumed from the list.
 * - false if the list is empty.
 */
bool addr_list_reduce_contig_block(struct addr_list *list,
				   unsigned long *base_addr,
				   unsigned long *total_size,
				   unsigned long *st);

/*
 * Read the (base_addr, xlat_level, cnt, st) fields of the descriptor at
 * index @idx without modifying the list. Returns false if @idx is out
 * of range.
 *
 * Returns @xlat_level as the XLAT table level derived from the descriptor's
 * encoded block size, suitable for direct use as an RTT walk level.
 *
 * Unlike addr_list_reduce_* this is non-destructive and works for both
 * INPUT and OUTPUT lists, which makes it suitable for iterating an
 * output list whose contents must be preserved for later host copy.
 */
bool addr_list_peek_desc(const struct addr_list *list, unsigned int idx,
			 unsigned long *base_addr, int *xlat_level,
			 unsigned long *cnt, unsigned long *st);

/*
 * Validates the address list `ranges` and returns the total memory described.
 *
 * Args:
 * - list: the address list to validate.
 * - is_contig: if true, the list must have exactly one valid `range` whose
 *              total size is a power of 2 and aligned to that size.
 * - total_mem_out: on success, set to the total memory size (in bytes)
 *                  described by the list. The caller is responsible for
 *                  checking this against any required memory limit.
 * - state: the expected RMI operation state for all `ranges`. Must be either
 *          RMI_OP_MEM_DELEGATED or RMI_OP_MEM_UNDELEGATED.
 *
 * Returns:
 * - true if all `ranges` pass validation.
 * - false if any `range` is invalid.
 */
bool addr_list_validate(struct addr_list *list, bool is_contig,
		unsigned long *total_mem_out, unsigned long state);

/*
 * Copies the address list from list structure to NS memory.
 *
 * Args:
 * - list: the address list to copy to NS host.
 * - ns_list_addr: the address in NS memory to copy the list to.
 * - ns_list_count: maximum number of `ranges` to copy.
 * - copied: set to the number of `ranges` actually copied.
 *
 * Returns:
 * - true if the list is copied to NS host successfully.
 * - false if the list cannot be copied to NS host.
 */
bool addr_list_partial_copy_to_host(struct addr_list *list,
			    unsigned long ns_list_addr,
			    unsigned int ns_list_count,
			    unsigned int *copied);

/*
 * Copies the address list from NS memory into the list structure.
 *
 * Args:
 * - list: the address list to populate.
 * - ns_list_addr: the address in NS memory to copy from.
 * - ns_list_count: the number of `ranges` to copy.
 *
 * Returns:
 * - true if the list is read from NS host successfully.
 * - false if the list cannot be read from NS host.
 */
bool addr_list_copy_from_host(struct addr_list *list,
			      unsigned long ns_list_addr,
			      unsigned int ns_list_count);

/* Returns true if the address list is empty */
static inline bool addr_list_is_empty(struct addr_list *list)
{
	assert(list != NULL);
	return (list->count == 0U);
}

/* Convert an encoded size field to the corresponding XLAT block size */
static inline unsigned long addr_list_sz_to_xlat_blk_sz(unsigned long sz_enc)
{
	/*
	 * @TODO: XLAT_BLOCK_SIZE takes into account only 4K granule size
	 * as it is the only supported granule size for the xlat library.
	 * We need to support other granule sizes regardless of the xlat library
	 * supported granularity in order to support all the possible
	 * RmiAddrRange block sizes.
	 */
	return XLAT_BLOCK_SIZE((long)XLAT_TABLE_LEVEL_MAX - (long)sz_enc);
}

static inline unsigned long xlat_blk_sz_to_addr_list_sz(unsigned long blk_size)
{
	for (unsigned long sz_enc = 0UL;
	     sz_enc <= (unsigned long)XLAT_TABLE_LEVEL_MAX; sz_enc++) {
		if (addr_list_sz_to_xlat_blk_sz(sz_enc) == blk_size) {
			return sz_enc;
		}
	}
	/* Should never be reached if blk_size is valid */
	assert(false);
	return 0UL;
}

#endif /* ADDR_LIST_H */
