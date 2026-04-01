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

/*
 * Maximum number of `ranges` we allow the address list to have.
 * Note that this implementation does not allow the list to cross
 * granule, so in that case, the operation will just return INCOMPLETE.
 */
#define ADDR_LIST_MAX_RANGES	(GRANULE_SIZE / sizeof(unsigned long))

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
	enum list_type type;/* Type of the list */
};

/*
 * Initializes the address list with zero `ranges` and the given type.
 *
 * Args:
 * - list: the address list to initialize.
 * - type: the type of the list (LIST_TYPE_INPUT or LIST_TYPE_OUTPUT).
 */
void addr_list_init(struct addr_list *list, enum list_type type);

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
 *          RMI_OP_MEM_DELEGATE or RMI_OP_MEM_UNDELEGATE.
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

#endif /* ADDR_LIST_H */
