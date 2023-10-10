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
#include <table.h>
#include <utils_def.h>
#include <xlat_contexts.h>
#include <xlat_high_va.h>
#include <xlat_tables.h>

COMPILER_ASSERT(XLAT_HIGH_VA_SLOT_NUM >= NR_CPU_SLOTS);

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
void assert_cpu_slots_empty(void)
{
	for (unsigned int i = 0U; i < (unsigned int)NR_CPU_SLOTS; i++) {
		assert(slot_to_descriptor((enum buffer_slot)i) ==
							TRANSIENT_DESC);
	}
}

static inline bool is_ns_slot(enum buffer_slot slot)
{
	return slot == SLOT_NS;
}

static inline bool is_realm_slot(enum buffer_slot slot)
{
	return (slot != SLOT_NS) && (slot < NR_CPU_SLOTS);
}

static void *ns_granule_map(enum buffer_slot slot, struct granule *granule)
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
void *granule_map(struct granule *g, enum buffer_slot slot)
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

	src = (uintptr_t)ns_granule_map(slot, ns_gr);
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

	dest = (uintptr_t)ns_granule_map(slot, ns_gr);
	retval = memcpy_ns_write((void *)(dest + offset), src, size);
	ns_buffer_unmap((void *)dest);

	return retval;
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

	/*
	 * Prevent the compiler from moving prior loads/stores to buf after the
	 * update to the translation table. Otherwise, those could fault.
	 */
	COMPILER_BARRIER();

	ret = xlat_unmap_memory_page(get_cached_llt_info(), (uintptr_t)buf);
	assert(ret == 0);
}
