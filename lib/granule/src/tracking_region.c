/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <assert.h>
#include <debug.h>
#include <dev_granule.h>
#include <errno.h>
#include <granule.h>
#include <rmm_el3_ifc.h>
#include <smc-rmi.h>
#include <spinlock.h>
#include <stdbool.h>
#include <stddef.h>
/* coverity[unnecessary_header:SUPPRESS] */
#include <string.h>
#include <tracking_region_arch.h>
#include <tracking_region_lock.h>
#include <tracking_region_pvt.h>
#include <utils_def.h>

/*
 * struct tracking_memory_bank stores a platform memory bank's PA range,
 * category and array indices. @tracking_start_idx identifies the first
 * struct tracking_region for the bank. @granule_start_idx identifies its
 * first entry in the fine-granule array.
 */
struct tracking_memory_bank {
	unsigned long base;
	unsigned long size;
	unsigned long granule_start_idx;
	uint32_t tracking_start_idx;
	uint8_t category;
};

/*
 * Persistent mapping state for one tracking-metadata array. @va and @size describe
 * its worst-case VA reservation. Backing is tracked by the architecture layer
 * after it is mapped, regardless of whether EL3 or the Host supplied it.
 */
struct tracking_array_mapping {
	uintptr_t va;
	size_t size;
	unsigned int state;
};

/* Assume a platform will not have more than 64 conventional or device tracking memory banks */
#define MAX_CONV_TRACKING_MEMORY_BANKS	U(64)
#define MAX_DEV_TRACKING_MEMORY_BANKS	U(64)
#define MAX_TRACKING_MEMORY_BANKS	(MAX_CONV_TRACKING_MEMORY_BANKS + \
					 MAX_DEV_TRACKING_MEMORY_BANKS)

/*
 * Fixed-capacity arrays of struct tracking_memory_bank, separated by memory
 * type, used for address and index lookup.
 */
struct tracking_memory_bank_storage {
	struct tracking_memory_bank conv_banks[MAX_CONV_TRACKING_MEMORY_BANKS];
	struct tracking_memory_bank dev_banks[MAX_DEV_TRACKING_MEMORY_BANKS];
} __aligned(GRANULE_SIZE);

/*
 * Tracking layout state and embedded struct tracking_memory_bank arrays.
 * Boot allocates this through rmm_el3_ifc_reserve_memory(); LFA reuses it.
 * The struct tracking_region and fine granule arrays have separate backing.
 */
struct tracking_region_data {
	struct tracking_memory_bank_storage banks;
	unsigned long tracking_region_size;
	unsigned long num_tracking_regions;
	unsigned long num_tracking_granules;
	unsigned long num_tracking_dev_granules;
	unsigned int num_conv_tracking_banks;
	unsigned int num_dev_tracking_banks;
	bool tracking_initialized;
	struct tracking_region *tracking_regions;
	struct tracking_array_mapping tracking_region_array;
	struct tracking_array_mapping granule_array_tr;
	struct tracking_array_mapping dev_granule_array_tr;
} __aligned(GRANULE_SIZE);

/* Per-image pointer to the persistent struct tracking_region_data. */
static struct tracking_region_data *tracking_data;

/*
 * Serialize configuration reads and updates, activation and tracking-info
 * queries. Acquire this lock before any tracking-region lock. LFA starts with
 * a new, unlocked lock after the previous image has been quiesced.
 */
static spinlock_t tracking_layout_lock;

/* The array VA is reserved; backing may be absent or managed per page. */
#define TRACKING_REGIONS_RESERVED	U(0)

/* The backing required to activate the array has been mapped and committed. */
#define TRACKING_REGIONS_COMMITTED	U(1)

static bool tracking_region_find_after_base(unsigned long base,
					    unsigned long top,
					    unsigned long *idx);

COMPILER_ASSERT_NO_CBMC(sizeof(struct tracking_memory_bank_storage) ==
			GRANULE_SIZE);
COMPILER_ASSERT_NO_CBMC(sizeof(struct tracking_region_data) ==
			TRACKING_REGION_DATA_SIZE);
COMPILER_ASSERT(sizeof(struct tracking_region_data) <=
		TRACKING_REGION_DATA_SIZE);
COMPILER_ASSERT(GRANULE_STATE_NS == DEV_GRANULE_STATE_NS);
COMPILER_ASSERT(GRANULE_STATE_DELEGATED == DEV_GRANULE_STATE_DELEGATED);
COMPILER_ASSERT(RMI_MEM_CATEGORY_DEV_COH <= UINT8_MAX);
COMPILER_ASSERT(mc_diverse < (U(1) << TR_MEM_CAT_WIDTH));
COMPILER_ASSERT(trs_coarse < (U(1) << TR_STATE_WIDTH));
COMPILER_ASSERT(GRANULE_ALIGNED(TRACKING_REGION_MIN_SIZE));
COMPILER_ASSERT(GRANULE_ALIGNED(TRACKING_REGION_MAX_SIZE));

static const struct tracking_memory_bank *tracking_region_find_addr(
					unsigned long addr,
					enum tr_mem_type type,
					unsigned long *tracking_region_idx,
					unsigned long *granule_idx);
static unsigned long tracking_region_lookup_by_idx(
					const struct tracking_memory_bank *banks,
					unsigned int count,
					unsigned long tr_idx,
					size_t entry_size,
					unsigned long *granule_idx);
