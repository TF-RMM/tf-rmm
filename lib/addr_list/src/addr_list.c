/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <addr_list.h>
#include <addr_list_prv.h>
#include <buffer.h>
#include <granule.h>
#include <stdbool.h>
#include <stddef.h>
#include <string.h>
#include <utils_def.h>

/* Convert an encoded size field to the corresponding XLAT block size */
static unsigned long sz_enc_to_blk_size(unsigned long sz_enc)
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

/* Get the desc_blk_size from desc */
static unsigned long desc_blk_size(unsigned long desc)
{
	return sz_enc_to_blk_size(get_sz_from_desc(desc));
}

static unsigned long blk_size_to_sz_enc(unsigned long blk_size)
{
	for (unsigned long sz_enc = 0UL;
	     sz_enc <= (unsigned long)XLAT_TABLE_LEVEL_MAX; sz_enc++) {
		if (sz_enc_to_blk_size(sz_enc) == blk_size) {
			return sz_enc;
		}
	}
	/* Should never be reached if blk_size is valid */
	assert(false);
	return 0UL;
}

static unsigned long create_desc(unsigned long addr,
				 unsigned long cnt,
				 unsigned long blk_size,
				 unsigned long st)
{
	unsigned long sz = blk_size_to_sz_enc(blk_size);
	unsigned long desc = 0UL;

	desc |= set_addr_in_desc(desc, addr);
	desc |= set_cnt_in_desc(desc, cnt);
	desc |= set_sz_in_desc(desc, sz);
	desc |= set_st_in_desc(desc, st);

	return desc;
}

/* Returns the top address of desc */
static unsigned long desc_top_addr(unsigned long desc)
{
	unsigned long blk_size = desc_blk_size(desc);
	unsigned long base = get_addr_from_desc(desc);

	return base + (get_cnt_from_desc(desc) * blk_size);
}

static bool desc_is_empty(unsigned long desc)
{
	return (get_cnt_from_desc(desc) == 0UL);
}

static bool add_block_to_current_idx(struct addr_list *list,
				       unsigned long addr,
				       unsigned long blk_size,
				       unsigned long st)
{
	unsigned int cur_idx = list->cur_idx;

	assert(desc_is_empty(list->range_desc[cur_idx]) == false);

	if (blk_size != desc_blk_size(list->range_desc[cur_idx])) {
		return false;
	}

	if (st != get_st_from_desc(list->range_desc[cur_idx])) {
		return false;
	}

	if (get_cnt_from_desc(list->range_desc[cur_idx]) >= max_block_count()) {
		return false;
	}

	/*
	 * Try to place the block at the beginning of the current
	 * address range.
	 * This is a common case if an object is destroyed backwards.
	 */
	if (addr == (get_addr_from_desc(list->range_desc[cur_idx]) - blk_size)) {
		list->range_desc[cur_idx] = set_addr_in_desc(list->range_desc[cur_idx], addr);
		list->range_desc[cur_idx] = increment_block_count(list->range_desc[cur_idx]);
	} else if (addr == desc_top_addr(list->range_desc[cur_idx])) {
		/* Try to place the block at the end of the current address range */
		list->range_desc[cur_idx] = increment_block_count(list->range_desc[cur_idx]);
	} else {
		return false;
	}

	return true;
}

/* cppcheck-suppress misra-c2012-8.7 */
void addr_list_init(struct addr_list *list, enum list_type type)
{
	assert(list != NULL);
	(void)memset(list, 0, sizeof(struct addr_list));
	list->type = type;
}

/* cppcheck-suppress misra-c2012-8.7 */
bool addr_list_add_block(struct addr_list *list,
			 unsigned long block_addr,
			 int rtt_level,
			 unsigned long st)
{
	assert(list != NULL);
	assert(list->type == LIST_TYPE_OUTPUT);

	unsigned long blk_size;

	assert((rtt_level >= 0) && (rtt_level <= XLAT_TABLE_LEVEL_MAX));
	assert((st == RMI_OP_MEM_DELEGATE) || (st == RMI_OP_MEM_UNDELEGATE));

	/*
	 * @TODO: XLAT_BLOCK_SIZE takes into account only 4K granule size
	 * as it is the only supported granule size for the xlat library.
	 * We need to support other granule sizes regardless of the xlat library
	 * supported granularity in order to support all the possible
	 * RmiAddrRange block sizes.
	 */
	blk_size = XLAT_BLOCK_SIZE(rtt_level);

	if (!ALIGNED((uintptr_t)block_addr, blk_size)) {
		return false;
	}

	/* If the list is empty, create the first descriptor */
	if (list->count == 0UL) {
		list->range_desc[0] = create_desc(block_addr, 1UL, blk_size, st);
		list->count++;
		return true;
	}

	/* Try to fit in one of the existing `range` descriptors */
	for (list->cur_idx = 0U; list->cur_idx < list->count;
			list->cur_idx++) {
		if (add_block_to_current_idx(list, block_addr, blk_size, st)) {
			/* The address is added to the current `range` */
			return true;
		}
	}

	if (list->count == ADDR_LIST_MAX_RANGES) {
		/* The list is full, cannot add the `range` */
		return false;
	}

	list->range_desc[list->cur_idx] = create_desc(block_addr, 1UL, blk_size, st);
	list->count++;

	return true;
}

/* Reduces the first memory block from the list and returns its address & size */
/* cppcheck-suppress misra-c2012-8.7 */
bool addr_list_reduce_first_block(struct addr_list *list,
			       unsigned long *block_addr,
			       int *rtt_level,
			       unsigned long *st)
{
	assert(list != NULL);
	assert(block_addr != NULL);
	assert(rtt_level != NULL);
	assert(st != NULL);
	assert(list->type == LIST_TYPE_INPUT);

	unsigned int cur_idx;
	unsigned long blk_size;

	if (list->count == 0U) {
		return false;
	}

	/* Find the next non-empty `range` descriptor starting from cur_idx */
	while ((list->cur_idx < list->count) &&
	       (desc_is_empty(list->range_desc[list->cur_idx]))) {
		list->cur_idx++;
	}

	if (list->cur_idx == list->count) {
		/* All `range` descriptors are empty */
		return false;
	}

	cur_idx = list->cur_idx;
	assert(cur_idx < list->count);
	blk_size = desc_blk_size(list->range_desc[cur_idx]);

	*block_addr = get_addr_from_desc(list->range_desc[cur_idx]);
	*rtt_level = XLAT_TABLE_LEVEL_MAX -
		       (int)get_sz_from_desc(list->range_desc[cur_idx]);
	*st = get_st_from_desc(list->range_desc[cur_idx]);

	/* Advance base address by one block and decrement the count */
	list->range_desc[cur_idx] = set_addr_in_desc(list->range_desc[cur_idx],
							  *block_addr + blk_size);
	list->range_desc[cur_idx] = decrement_block_count(list->range_desc[cur_idx]);

	return true;
}

/* Perform the necessary validation on the address list */
/* cppcheck-suppress misra-c2012-8.7 */
bool addr_list_validate(struct addr_list *list, bool is_contig,
		unsigned long *total_mem_out, unsigned long state)
{
	assert(list != NULL);
	assert(total_mem_out != NULL);
	assert(list->type == LIST_TYPE_INPUT);
	assert((state == RMI_OP_MEM_DELEGATE) || (state == RMI_OP_MEM_UNDELEGATE));

	assert(list->count <= (unsigned int)ADDR_LIST_MAX_RANGES);

	unsigned int valid_count = 0U;
	unsigned long total_mem = 0UL;

	for (unsigned int i = 0U; i < list->count; i++) {
		if (get_cnt_from_desc(list->range_desc[i]) == 0UL) {
			/* Empty range, skip it */
			continue;
		}

		valid_count++;

		if (is_contig && (valid_count > 1U)) {
			/* A contiguous list cannot have more than 1 valid descriptor */
			return false;
		}

		if (!ALIGNED(get_addr_from_desc(list->range_desc[i]),
			      desc_blk_size(list->range_desc[i]))) {
			/* The base address of each range must be aligned to its block size */
			return false;
		}
		/* The desc block size should be a valid XLAT_BLOCK_SIZE */
		if (!IS_VALID_XLAT_BLOCK_SIZE(desc_blk_size(list->range_desc[i]))) {
			return false;
		}
		/* The desc block count should be <= maximum count allowed */
		if (get_cnt_from_desc(list->range_desc[i]) > get_max_block_cnt()) {
			return false;
		}
		/* The state in desc should match the expected state */
		if (get_st_from_desc(list->range_desc[i]) != state) {
			return false;
		}

		if (is_contig) {
			unsigned long contig_blk = desc_blk_size(list->range_desc[i])
				 * get_cnt_from_desc(list->range_desc[i]);
			/* The memory block must be a power of 2 */
			if (!IS_POWER_OF_TWO(contig_blk)) {
				return false;
			}
			/* The memory block must be aligned to its size */
			if (!ALIGNED(get_addr_from_desc(list->range_desc[i]), contig_blk)) {
				return false;
			}
		}

		total_mem += desc_blk_size(list->range_desc[i])
			     * get_cnt_from_desc(list->range_desc[i]);
	}

	*total_mem_out = total_mem;
	return true;
}

/* cppcheck-suppress misra-c2012-8.7 */
bool addr_list_partial_copy_to_host(struct addr_list *list,
			    unsigned long ns_list_addr,
			    unsigned int ns_list_count,
			    unsigned int *copied)
{
	assert(list != NULL);
	assert(list->type == LIST_TYPE_OUTPUT);
	assert(copied != NULL);

	unsigned long ns_list_offset =  (ns_list_addr & ~GRANULE_MASK) /
						 sizeof(unsigned long);
	unsigned int list_count = list->count;
	struct granule *g_ns;

	/*
	 * Cater for the case in which the host specified a count
	 * less than the pending `range` entries.
	 */
	list_count = MIN(list_count, ns_list_count);

	assert((ns_list_offset + list_count) <= ADDR_LIST_MAX_RANGES);
	assert(ALIGNED(ns_list_addr, sizeof(unsigned long)));

	g_ns = find_granule(ns_list_addr & GRANULE_MASK);
	if ((g_ns == NULL) || (granule_unlocked_state(g_ns) != GRANULE_STATE_NS)) {
		return false;
	}

	if (!ns_buffer_write(SLOT_NS, g_ns,
			(unsigned int)(ns_list_offset * sizeof(unsigned long)),
			(list_count * sizeof(unsigned long)),
			 (void *)&list->range_desc[0])) {
		return false;
	}

	list->count -= list_count;
	*copied = list_count;

	/* Move the remaining pending `ranges` to the start of the buffer */
	(void)memmove((void *)&(list->range_desc[0]),
		      (void *)&(list->range_desc[list_count]),
		      (list->count * sizeof(unsigned long)));

	return true;
}

/* cppcheck-suppress misra-c2012-8.7 */
bool addr_list_copy_from_host(struct addr_list *list,
			      unsigned long ns_list_addr,
			      unsigned int ns_list_count)
{
	assert(list != NULL);
	assert(list->type == LIST_TYPE_INPUT);

	unsigned long ns_list_offset =  (ns_list_addr & ~GRANULE_MASK) /
						 sizeof(unsigned long);
	struct granule *g_ns;

	/* Check if an uninitialized list is being used */
	assert(list->count == 0U);

	/* The caller must ensure that @ns_list_count has been adjusted/sanitized. */
	assert((ns_list_offset + ns_list_count) <= (unsigned int)ADDR_LIST_MAX_RANGES);
	assert(ALIGNED(ns_list_addr, sizeof(unsigned long)));

	g_ns = find_granule(ns_list_addr & GRANULE_MASK);
	if ((g_ns == NULL) || (granule_unlocked_state(g_ns) != GRANULE_STATE_NS)) {
		return false;
	}

	if (!ns_buffer_read(SLOT_NS, g_ns,
			(unsigned int)(ns_list_offset * sizeof(unsigned long)),
			(ns_list_count * sizeof(unsigned long)),
			(void *)&list->range_desc[0])) {
		return false;
	}

	list->count = ns_list_count;
	return true;
}
