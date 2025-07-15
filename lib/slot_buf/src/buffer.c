/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch.h>
#include <arch_helpers.h>
#include <assert.h>
#include <buffer.h>
#include <buffer_private.h>
#include <cpuid.h>
#include <debug.h>
#include <errno.h>
#include <granule.h>
#include <slot_buf_arch.h>
#include <stdbool.h>
#include <stdint.h>
/* coverity[unnecessary_header: SUPPRESS] */
#include <string.h>
#include <utils_def.h>
#include <xlat_contexts.h>
#include <xlat_high_va.h>
#include <xlat_tables.h>

COMPILER_ASSERT(XLAT_HIGH_VA_SLOT_NUM >= U(NR_CPU_SLOTS));

/* coverity[misra_c_2012_rule_8_7_violation:SUPPRESS] */
uintptr_t slot_to_va(enum buffer_slot slot)
{
	assert(slot < NR_CPU_SLOTS);

	return (SLOT_VIRT + (GRANULE_SIZE * (unsigned long)slot));
}

/* coverity[misra_c_2012_rule_8_7_violation:SUPPRESS] */
struct xlat_llt_info *get_cached_llt_info(void)
{
	/*
	 * Allocate a cache to store the last level table info where the slot buffers
	 * are mapped to avoid needing to perform a table walk every time a buffer
	 * slot operation has to be done.
	 */
	static struct xlat_llt_info llt_info_cache[MAX_CPUS];

	return &llt_info_cache[my_cpuid()];
}

__unused static uint64_t slot_to_descriptor(enum buffer_slot slot)
{
	uint64_t *entry = xlat_get_tte_ptr(get_cached_llt_info(),
				       slot_to_va(slot));
	assert(entry != NULL);

	return xlat_read_tte(entry);
}

/*
 * Finishes initializing the slot buffer mechanism.
 * This function must be called after the MMU is enabled.
 */
void slot_buf_finish_warmboot_init(void)
{
	assert(is_mmu_enabled() == true);

	/*
	 * Initialize (if not done yet) the internal cache with the last level
	 * translation table that holds the MMU descriptors for the slot
	 * buffers, so we can access them faster when we need to map/unmap.
	 */
	if ((get_cached_llt_info())->table == NULL) {
		if (xlat_get_llt_from_va(get_cached_llt_info(),
					 xlat_get_high_va_xlat_ctx(),
					 slot_to_va(SLOT_NS)) != 0) {
			ERROR("%s (%u): Failed to initialize table entry cache for CPU %u\n",
					__func__, __LINE__, my_cpuid());
			panic();

		}
	}
}

/*
 * Buffer slots are intended to be transient, and should not be live at
 * entry/exit of the RMM.
 */
bool check_cpu_slots_empty(void)
{
	for (unsigned int i = 0U; i < (unsigned int)NR_CPU_SLOTS; i++) {
		if (slot_to_descriptor((enum buffer_slot)i) !=
				       TRANSIENT_DESC) {
			return false;
		}
	}
	return true;
}

static inline bool is_ns_slot(enum buffer_slot slot)
{
	return slot == SLOT_NS;
}

static inline bool is_realm_slot(enum buffer_slot slot)
{
	return (slot != SLOT_NS) && (slot < NR_CPU_SLOTS);
}

static void *ns_buffer_granule_map(enum buffer_slot slot, struct granule *granule)
{
	unsigned long addr = granule_addr(granule);

	assert(is_ns_slot(slot));
	return buffer_arch_map(slot, addr);
}

static inline void ns_buffer_unmap(void *buf)
{
	buffer_arch_unmap(buf);
}

/*
 * Maps a granule @g into the provided @slot, returning
 * the virtual address.
 *
 * The caller must either hold @g::lock or hold a reference.
 */
void *buffer_granule_map(struct granule *g, enum buffer_slot slot)
{
	unsigned long addr = granule_addr(g);

	assert(is_realm_slot(slot));

	return buffer_arch_map(slot, addr);
}

void buffer_unmap(void *buf)
{
	buffer_arch_unmap(buf);
}

/*
 * Map a Non secure granule @g into the slot @slot and read data from
 * this granule to @dest. Unmap the granule once the read is done.
 *
 * It returns 'true' on success or `false` if not all data are copied.
 * Only the least significant bits of @offset are considered, which allows the
 * full PA of a non-granule aligned buffer to be used for the @offset parameter.
 */
bool ns_buffer_read(enum buffer_slot slot,
		    struct granule *ns_gr,
		    unsigned int offset,
		    size_t size,
		    void *dest)
{
	uintptr_t src;
	bool retval;

	assert(is_ns_slot(slot));
	assert(ns_gr != NULL);
	assert(dest != NULL);

	/*
	 * To simplify the trapping mechanism around NS access,
	 * memcpy_ns_read uses a single 8-byte LDR instruction and
	 * all parameters must be aligned accordingly.
	 */
	assert(ALIGNED(size, 8U));
	assert(ALIGNED(offset, 8U));
	assert(ALIGNED(dest, 8U));

	offset &= (unsigned int)(~GRANULE_MASK);
	assert((offset + size) <= GRANULE_SIZE);

	src = (uintptr_t)ns_buffer_granule_map(slot, ns_gr);
	retval = memcpy_ns_read(dest, (void *)(src + offset), size);
	ns_buffer_unmap((void *)src);

	return retval;
}

/*
 * Map a Non secure granule @g into the slot @slot and write data from
 * this granule to @dest. Unmap the granule once the write is done.
 *
 * It returns 'true' on success or `false` if not all data are copied.
 * Only the least significant bits of @offset are considered, which allows the
 * full PA of a non-granule aligned buffer to be used for the @offset parameter.
 */
bool ns_buffer_write(enum buffer_slot slot,
		     struct granule *ns_gr,
		     unsigned int offset,
		     size_t size,
		     void *src)
{
	uintptr_t dest;
	bool retval;

	assert(is_ns_slot(slot));
	assert(ns_gr != NULL);
	assert(src != NULL);

	/*
	 * To simplify the trapping mechanism around NS access,
	 * memcpy_ns_write uses a single 8-byte STR instruction and
	 * all parameters must be aligned accordingly.
	 */
	assert(ALIGNED(size, 8U));
	assert(ALIGNED(offset, 8U));
	assert(ALIGNED(src, 8U));

	offset &= (unsigned int)(~GRANULE_MASK);
	assert((offset + size) <= GRANULE_SIZE);

	dest = (uintptr_t)ns_buffer_granule_map(slot, ns_gr);
	retval = memcpy_ns_write((void *)(dest + offset), src, size);
	ns_buffer_unmap((void *)dest);

	return retval;
}

/*
 * Helper function to copy less than 8 bytes from the source buffer to a 8 byte
 * aligned ns buffer at a specific offset. The function always writes 8 bytes to
 * the NS buffer, the dest buffer is filled with zero bytes before and after the
 * content copied from src.
 */
static bool ns_buffer_write_unaligned_small(uintptr_t dest,
					    size_t size,
					    void *src,
					    size_t offset)
{
	uint64_t temp_buf = 0UL;
	uint8_t *temp_dest;

	assert(ALIGNED(dest, 8U));
	assert(ALIGNED(((uintptr_t)&src), 8U));
	assert(ALIGNED(((uintptr_t)&temp_buf), 8U));
	assert(size > 0U);
	assert(size < 8U);
	assert((size + offset) <= 8U);

	temp_dest = &((uint8_t *)&temp_buf)[offset];
	(void)memcpy((void *)temp_dest, src, size);

	return memcpy_ns_write((void *)(dest), &temp_buf, sizeof(temp_buf));
}

/*
 * Copies 'size' bytes from 'src' to 'ns_gr' at the offset 'offset'. The
 * function uses an optimized version of memcpy ('memcpy_ns_write') that expects
 * 'dest', 'src' and 'size' to be aligned at 8 bytes.
 * This function uses a temporary buffer, in case 'src' and or 'size' is not
 * aligned. Offset is expected to be 8 byte aligned.
 * If 'src' is not aligned, extra bytes are copied at the beginning of ns_gr to
 * make the copy eight aligned. If len is not aligned some extra bytes are
 * copied in the end.
 * The number of bytes to be copied (counting the extra bytes for the alignment)
 * must be smaller than GRANULE_SIZE.
 * The number of extra zeroes added at the beginning of the buffer are returned
 * in ns_start_offset.
 * The function returns true, if the copy operation was successful. Returns
 * false otherwise.
 * ns_start_offset should only be relied on if the function returns true.
 */
bool ns_buffer_write_unaligned(enum buffer_slot slot,
			       struct granule *ns_gr,
			       unsigned int offset,
			       size_t size,
			       void *src,
			       size_t *ns_start_offset)
{
	uintptr_t dest;
	size_t align_diff;
	size_t aligned_size;
	void *aligned_src;
	bool retval = false;

	assert(is_ns_slot(slot));
	assert(ns_gr != NULL);
	assert(src != NULL);

	if (size == 0U) {
		return true;
	}

	/*
	 * To simplify the trapping mechanism around NS access,
	 * ns_buffer_write_unaligned uses a single 8-byte STR instruction.
	 * In case 'src' and size is not aligned, a temporary 8 aligned buffer
	 * is used to do the copy. Offset must be aligned.
	 */
	assert(ALIGNED(offset, 8U));

	offset &= (unsigned int)(~GRANULE_MASK);

	dest = (uintptr_t)ns_buffer_granule_map(slot, ns_gr);

	aligned_src = (void *)round_down((uintptr_t)src, 8U);
	assert((uintptr_t)aligned_src <= (uintptr_t)src);
	align_diff = (uintptr_t)src - (uintptr_t)aligned_src;
	assert(align_diff < 8U);
	assert((offset + round_up(align_diff + size, 8U)) <= GRANULE_SIZE);

	if (align_diff > 0U) {
		size_t unaligned_size = min(size, 8U - align_diff);

		retval = ns_buffer_write_unaligned_small(
			dest + offset, unaligned_size, src, align_diff);
		if (!retval) {
			goto unmap;
		} else {
			src = (void *)((uintptr_t)src + (8U - align_diff));
			offset += 8U;
			size -= unaligned_size;
		}
	}
	assert(ALIGNED((uintptr_t)src, 8U));

	aligned_size = round_down(size, 8U);
	assert(aligned_size <= size);

	if (aligned_size > 0U) {
		retval = memcpy_ns_write((void *)(dest + offset), src, aligned_size);
		if (!retval) {
			goto unmap;
		} else {
			src = (void *)((uintptr_t)src + aligned_size);
			offset += (unsigned int)aligned_size;
			size -= aligned_size;
		}
	}
	assert(size < 8U);

	if (size > 0U) {
		retval = ns_buffer_write_unaligned_small(dest + offset, size, src, 0);
	}
unmap:

	ns_buffer_unmap((void *)dest);

	*ns_start_offset = align_diff;

	return retval;
}

static void *buffer_aux_granules_map(struct granule *g_aux[],
				     unsigned int num_aux, enum buffer_slot slot, bool zeroed)
{
	void *mapped_aux = NULL;

	for (unsigned int i = 0U; i < num_aux; i++) {
		void *aux;

		if (zeroed) {
			aux = buffer_granule_map_zeroed(g_aux[i],
				safe_cast_to_slot(slot, i));
		} else {
			aux = buffer_granule_map(g_aux[i],
				safe_cast_to_slot(slot, i));
		}

		assert(aux != NULL);

		if (i == 0UL) {
			mapped_aux = aux;
		}
	}
	return mapped_aux;
}

static void buffer_aux_unmap(void *aux, unsigned int num_aux)
{
	unsigned char *aux_vaddr = (unsigned char *)aux;

	for (unsigned int i = 0U; i < num_aux; i++) {
		buffer_unmap((void *)((uintptr_t)aux_vaddr +
				      (i * GRANULE_SIZE)));
	}
}

/*
 * The parent REC granules lock is expected to be acquired before functions
 * buffer_rec_aux_granules_map() and buffer_rec_aux_unmap() are called.
 */
void *buffer_rec_aux_granules_map(struct granule *g_rec_aux[],
				  unsigned int num_aux)
{
	assert(g_rec_aux != NULL);
	assert(num_aux <= MAX_REC_AUX_GRANULES);
	return buffer_aux_granules_map(g_rec_aux, num_aux, SLOT_REC_AUX0, false);
}

/*
 * The parent REC granules lock is expected to be acquired before functions
 * buffer_rec_aux_granules_map_zeroed() and buffer_rec_aux_unmap() are called.
 */
void *buffer_rec_aux_granules_map_zeroed(struct granule *g_rec_aux[],
				  unsigned int num_aux)
{
	assert(g_rec_aux != NULL);
	assert(num_aux <= MAX_REC_AUX_GRANULES);
	return buffer_aux_granules_map(g_rec_aux, num_aux, SLOT_REC_AUX0, true);
}

/*
 * The parent REC granules lock is expected to be acquired before functions
 * buffer_rec_aux_granules_map_el3_token_sign_slot() and
 * buffer_rec_aux_unmap() are called.
 */
void *buffer_rec_aux_granules_map_el3_token_sign_slot(
				      struct granule *g_rec_aux[],
				      unsigned int num_aux)
{
	assert(g_rec_aux != NULL);
	assert(num_aux <= MAX_REC_AUX_GRANULES);
	return buffer_aux_granules_map(g_rec_aux, num_aux,
				       SLOT_EL3_TOKEN_SIGN_AUX0, false);
}

void buffer_rec_aux_unmap(void *rec_aux, unsigned int num_aux)
{
	assert(rec_aux != NULL);
	assert(num_aux <= MAX_REC_AUX_GRANULES);
	return buffer_aux_unmap(rec_aux, num_aux);
}

/*
 * The parent REC granule lock is expected to be acquired before functions
 * buffer_pdev_aux_granules_map() and buffer_pdev_aux_unmap() are called.
 */
void *buffer_pdev_aux_granules_map(struct granule *g_pdev_aux[],
				  unsigned int num_aux)
{
	assert(g_pdev_aux != NULL);
	assert(num_aux <= PDEV_PARAM_AUX_GRANULES_MAX);
	return buffer_aux_granules_map(g_pdev_aux, num_aux, SLOT_PDEV_AUX0, false);
}

/*
 * The parent REC granule lock is expected to be acquired before functions
 * buffer_pdev_aux_granules_map_zeroed() and buffer_pdev_aux_unmap() are called.
 */
void *buffer_pdev_aux_granules_map_zeroed(struct granule *g_pdev_aux[],
				  unsigned int num_aux)
{
	assert(g_pdev_aux != NULL);
	assert(num_aux <= PDEV_PARAM_AUX_GRANULES_MAX);
	return buffer_aux_granules_map(g_pdev_aux, num_aux, SLOT_PDEV_AUX0, true);
}

void buffer_pdev_aux_unmap(void *pdev_aux, unsigned int num_aux)
{
	assert(pdev_aux != NULL);
	assert(num_aux <= PDEV_PARAM_AUX_GRANULES_MAX);
	return buffer_aux_unmap(pdev_aux, num_aux);
}

void buffer_granule_memzero(struct granule *g, enum buffer_slot slot)
{
	unsigned long *buf;

	assert(g != NULL);

	buf = buffer_granule_map(g, slot);
	assert(buf != NULL);

	granule_memzero_mapped(buf);
	buffer_unmap(buf);
}

/******************************************************************************
 * Internal helpers
 ******************************************************************************/

/* coverity[misra_c_2012_rule_8_7_violation:SUPPRESS] */
void *buffer_map_internal(enum buffer_slot slot, unsigned long addr)
{
	/*
	 * Attributes for a buffer slot page descriptor.
	 * Note that the AF bit on the descriptor is handled by the translation
	 * library (it assumes that access faults are not handled) so it does not
	 * need to be specified here.
	 */
	uint64_t attr = XLAT_NG_DATA_ATTR;
	uintptr_t va = slot_to_va(slot);
	struct xlat_llt_info *entry = get_cached_llt_info();

	assert(GRANULE_ALIGNED(addr));

	attr |= ((slot == SLOT_NS) ? MT_NS : MT_REALM);

	if (xlat_map_memory_page_with_attrs(entry, va,
					    (uintptr_t)addr, attr) != 0) {
		/* Error mapping the buffer */
		return NULL;
	}

	return (void *)va;
}

/* coverity[misra_c_2012_rule_8_7_violation:SUPPRESS] */
void buffer_unmap_internal(void *buf)
{
	int ret __unused;

	ret = xlat_unmap_memory_page(get_cached_llt_info(), (uintptr_t)buf);
	assert(ret == 0);
}
