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
#include <xlat_contexts.h>
#include <xlat_tables.h>

/*
 * All the slot buffers for a given PE must be mapped by a single translation
 * table, which means the max VA size should be <= 4KB * 512
 */
COMPILER_ASSERT((RMM_SLOT_BUF_VA_SIZE) <= (GRANULE_SIZE * XLAT_TABLE_ENTRIES));

/*
 * For all translation stages if FEAT_TTST is implemented, while
 * the PE is executing in AArch64 state and is using 4KB
 * translation granules, the min address space size is 64KB
 */
COMPILER_ASSERT((RMM_SLOT_BUF_VA_SIZE) >= (1 << 16U));

#define RMM_SLOT_BUF_MMAP	MAP_REGION_TRANSIENT(			\
					SLOT_VIRT,			\
					RMM_SLOT_BUF_VA_SIZE,		\
					PAGE_SIZE)

#define SLOT_BUF_MMAP_REGIONS		UL(1)

/*
 * Attributes for a buffer slot page descriptor.
 * Note that the AF bit on the descriptor is handled by the translation
 * library (it assumes that access faults are not handled) so it does not
 * need to be specified here.
 */
#define SLOT_DESC_ATTR		(MT_RW_DATA | MT_NG)

/*
 * The base tables for all the contexts are manually allocated as a continous
 * block of memory (one L3 table per PE).
 */
static uint64_t slot_buf_s1tt[XLAT_TABLE_ENTRIES * MAX_CPUS]
				    __aligned(XLAT_TABLES_ALIGNMENT);

/* Allocate per-cpu xlat_ctx_tbls */
static struct xlat_ctx_tbls slot_buf_tbls[MAX_CPUS];

/* Allocate xlat_ctx_cfg for high VA which will be common to all PEs */
static struct xlat_ctx_cfg slot_buf_xlat_ctx_cfg;

/* context definition */
static struct xlat_ctx slot_buf_xlat_ctx[MAX_CPUS];

/*
 * Allocate a cache to store the last level table info where the slot buffers
 * are mapped to avoid needing to perform a table walk every time a buffer
 * slot operation has to be done.
 */
static struct xlat_llt_info llt_info_cache[MAX_CPUS];

uintptr_t slot_to_va(enum buffer_slot slot)
{
	assert(slot < NR_CPU_SLOTS);

	return (uintptr_t)(SLOT_VIRT + (GRANULE_SIZE * (unsigned int)slot));
}

static inline struct xlat_ctx *get_slot_buf_xlat_ctx(void)
{
	return &slot_buf_xlat_ctx[my_cpuid()];
}

struct xlat_llt_info *get_cached_llt_info(void)
{
	return &llt_info_cache[my_cpuid()];
}

__unused static uint64_t slot_to_descriptor(enum buffer_slot slot)
{
	uint64_t *entry = xlat_get_tte_ptr(get_cached_llt_info(),
				       slot_to_va(slot));
	assert(entry != NULL);

	return xlat_read_tte(entry);
}

int slot_buf_coldboot_init(void)
{
	static struct xlat_mmap_region slot_buf_regions[] = {
		RMM_SLOT_BUF_MMAP,
	};

	/*
	 * Initialize the common configuration used for all
	 * translation contexts
	 */
	return xlat_ctx_cfg_init(&slot_buf_xlat_ctx_cfg, VA_HIGH_REGION,
				 &slot_buf_regions[0], 1U,
				 RMM_SLOT_BUF_VA_SIZE);
}

/*
 * Setup xlat table for slot buffer mechanism for each PE.
 * Must be called for every PE in the system
 */
void slot_buf_setup_xlat(void)
{
	unsigned int cpuid = my_cpuid();
	struct xlat_ctx *slot_buf_ctx = get_slot_buf_xlat_ctx();

	/*
	 * Initialize the translation tables for the current context.
	 * This is done on the first boot of each PE.
	 */
	int ret = xlat_ctx_init(slot_buf_ctx,
				&slot_buf_xlat_ctx_cfg,
				&slot_buf_tbls[cpuid],
				&slot_buf_s1tt[XLAT_TABLE_ENTRIES * cpuid], 1U);

	if (!((ret == 0) || (ret == -EALREADY))) {
		/*
		 * If the context was already created, carry on with the
		 * initialization. If it cannot be created, panic.
		 */
		ERROR("%s (%u): Failed to initialize the xlat context for the slot buffers (-%i)\n",
					__func__, __LINE__, ret);
		panic();
	}

	/* Configure MMU registers */
	if (xlat_arch_setup_mmu_cfg(get_slot_buf_xlat_ctx())) {
		ERROR("%s (%u): MMU registers failed to initialize\n",
					__func__, __LINE__);
		panic();
	}
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
					 get_slot_buf_xlat_ctx(),
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

bool memcpy_ns_read(void *dest, const void *ns_src, size_t size);
bool memcpy_ns_write(void *ns_dest, const void *src, size_t size);

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

void *buffer_map_internal(enum buffer_slot slot, unsigned long addr)
{
	uint64_t attr = SLOT_DESC_ATTR;
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
