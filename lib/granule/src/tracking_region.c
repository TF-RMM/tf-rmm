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

/*
 * Return the granule-array stride for one region. Each fine tracking region has
 * a page-aligned range so its metadata can be reclaimed independently.
 */
static unsigned long tracking_region_fine_stride(unsigned long region_size,
						 size_t entry_size)
{
	size_t raw_size;
	size_t stride;

	assert((entry_size != 0UL) &&
	       ((region_size == TRACKING_REGION_MIN_SIZE) ||
		(region_size == TRACKING_REGION_MAX_SIZE)));
	raw_size = (region_size / GRANULE_SIZE) * entry_size;
	stride = round_up(raw_size, GRANULE_SIZE);
	assert((stride >= raw_size) && ((stride % entry_size) == 0UL));

	return stride / entry_size;
}

/*
 * Copy one category of platform banks into a struct tracking_memory_bank array.
 *
 * @platform_banks contains @count struct plat_memory_bank entries and may be
 * NULL only when @count is zero. Zero-sized banks are ignored. Every other bank
 * must have a granule-aligned base and size, and its address range must not overflow.
 * Starting at *@num_banks, append a struct tracking_memory_bank for each valid
 * range to @banks and record @category, without exceeding @capacity. The caller
 * subsequently sorts the array and validates that its ranges do not overlap.
 *
 * Return 0 on success, -EINVAL for a missing array or unaligned bank,
 * -EOVERFLOW for a wrapping address range, or -ENOSPC when @banks is full.
 * Entries appended before an error are not rolled back because initialization
 * failure is boot-fatal.
 */
static int tracking_region_copy_bank_category(
				   const struct plat_memory_bank *platform_banks,
				   unsigned long count,
				   unsigned long category,
				   struct tracking_memory_bank *banks,
				   unsigned int capacity,
				   unsigned int *num_banks)
{
	assert(banks != NULL);
	assert(num_banks != NULL);
	assert(category <= RMI_MEM_CATEGORY_DEV_COH);

	if ((platform_banks == NULL) && (count != 0UL)) {
		ERROR("%s: missing bank array for category %lu\n",
		      __func__, category);
		return -EINVAL;
	}

	for (unsigned long i = 0UL; i < count; i++) {
		const struct plat_memory_bank *bank = &platform_banks[i];

		if (bank->size == 0UL) {
			continue;
		}
		if (!GRANULE_ALIGNED(bank->base) ||
		    !GRANULE_ALIGNED(bank->size)) {
			ERROR("%s %lu: bank is not granule aligned\n",
			      __func__, category);
			return -EINVAL;
		}
		if (bank->base > (UINT64_MAX - bank->size)) {
			ERROR("%s %lu: bank range overflows\n",
			      __func__, category);
			return -EOVERFLOW;
		}

		if (*num_banks >= capacity) {
			ERROR("%s %lu: capacity %u exceeded\n",
			      __func__, category, capacity);
			return -ENOSPC;
		}

		banks[*num_banks].base = bank->base;
		banks[*num_banks].size = bank->size;
		banks[*num_banks].category = (uint8_t)category;
		(*num_banks)++;
	}

	return 0;
}

/*
 * Sort the struct tracking_memory_bank array @banks by base and assert that
 * the resulting ranges do not overlap.
 */
static void tracking_region_sort_and_validate_banks(
					struct tracking_memory_bank *banks,
					unsigned int count)
{
	for (unsigned int i = 1U; i < count; i++) {
		struct tracking_memory_bank bank = banks[i];
		unsigned int j = i;

		while ((j > 0U) && (banks[j - 1U].base > bank.base)) {
			banks[j] = banks[j - 1U];
			j--;
		}

		banks[j] = bank;
	}

	for (unsigned int i = 0U; i < count; i++) {
		assert(banks[i].base <= (UINT64_MAX - banks[i].size));
		if (i > 0U) {
			assert((banks[i - 1U].base + banks[i - 1U].size) <=
			       banks[i].base);
		}
	}
}

/*
 * Assert that the raw conventional and device PA ranges do not overlap. Bank
 * boundaries need not be tracking-region aligned, so disjoint banks may lie
 * within the same tracking region and share its index.
 */
static void tracking_memory_banks_validate_no_overlap(
				const struct tracking_memory_bank_storage *storage,
				unsigned int conv_count,
				unsigned int dev_count)
{
	for (unsigned int i = 0U; i < conv_count; i++) {
		const struct tracking_memory_bank *conv __unused =
			&storage->conv_banks[i];
		unsigned long conv_end __unused = conv->base + conv->size;

		for (unsigned int j = 0U; j < dev_count; j++) {
			const struct tracking_memory_bank *dev __unused =
				&storage->dev_banks[j];
			unsigned long dev_end __unused = dev->base + dev->size;

			assert((conv_end <= dev->base) ||
			       (dev_end <= conv->base));
		}
	}
}

/*
 * Build the compressed, shared tracking-region index space across conventional
 * and device memory banks.
 *
 * @storage contains two struct tracking_memory_bank arrays, one per memory
 * type. @conv_count and @dev_count select their populated entries, which must
 * have already been sorted and checked for overlap. @region_size is the
 * configured tracking-region size. A temporary PA-ordered view leaves the
 * stored arrays unchanged.
 * Complete aligned holes consume no array entry, while disjoint banks which
 * intersect the same tracking region share an index.
 *
 * The function sets @tracking_start_idx in each struct tracking_memory_bank
 * to its first shared index and returns the number of struct tracking_region
 * objects required by the layout.
 */
static unsigned long tracking_memory_banks_assign_shared_indices(
				struct tracking_memory_bank_storage *storage,
				unsigned int conv_count,
				unsigned int dev_count,
				unsigned long region_size)
{
	struct tracking_memory_bank *banks[MAX_TRACKING_MEMORY_BANKS];
	unsigned int count = conv_count + dev_count;
	unsigned long current_top = 0UL;
	unsigned long num_regions = 0UL;

	assert(count <= MAX_TRACKING_MEMORY_BANKS);
	assert((region_size == TRACKING_REGION_MIN_SIZE) ||
	       (region_size == TRACKING_REGION_MAX_SIZE));

	/* Build a combined view without moving either struct tracking_memory_bank array. */
	for (unsigned int i = 0U; i < conv_count; i++) {
		banks[i] = &storage->conv_banks[i];
	}

	for (unsigned int i = 0U; i < dev_count; i++) {
		banks[conv_count + i] = &storage->dev_banks[i];
	}

	/*
	 * Sort the temporary pointer table by PA so both memory types receive
	 * indices from one address-ordered space without rearranging their arrays.
	 */
	for (unsigned int i = 0U; i < count; i++) {
		for (unsigned int j = i + 1U; j < count; j++) {
			if (banks[j]->base < banks[i]->base) {
				struct tracking_memory_bank *bank = banks[i];

				banks[i] = banks[j];
				banks[j] = bank;
			}
		}
	}

	/*
	 * Assign shared indices in PA order. Complete holes are omitted, while
	 * banks intersecting the same aligned tracking region reuse its index.
	 *
	 * PA:    | CONV bank | DEV bank | full hole | CONV bank |
	 * TR:    |----------- TR 0 -----|  omitted  |--- TR 1 --|
	 * index: |             0        |           |    1      |
	 */
	for (unsigned int i = 0U; i < count; i++) {
		struct tracking_memory_bank *bank = banks[i];
		unsigned long base = round_down(bank->base, region_size);
		unsigned long start_idx;
		unsigned long top;

		top = round_up(bank->base + bank->size, region_size);
		if ((i == 0U) || (base >= current_top)) {
			start_idx = num_regions;
			num_regions += (top - base) / region_size;
			current_top = top;
		} else {
			unsigned long overlap_regions;

			overlap_regions = (current_top - base) / region_size;
			/* Disjoint PA banks can share only one boundary region. */
			assert(overlap_regions <= 1UL);
			assert(overlap_regions <= num_regions);
			start_idx = num_regions - overlap_regions;

			if (top > current_top) {
				num_regions += (top - current_top) / region_size;
				current_top = top;
			}
		}

		assert(start_idx <= UINT32_MAX);
		bank->tracking_start_idx = (uint32_t)start_idx;
	}

	return num_regions;
}

/*
 * Build the type-local fine-granule index space for @banks.
 *
 * @banks contains @count struct tracking_memory_bank entries describing
 * PA-ordered, non-overlapping banks of one memory type. In each entry, set
 * @granule_start_idx to the first granule slot for the aligned tracking region
 * containing its base. Disjoint banks which intersect the same tracking region
 * share that region's granule range.
 *
 * A represented tracking region reserves a complete page-aligned granule
 * stride. This includes slots for intra-region holes and any page padding, so
 * address-to-index conversion remains arithmetic and each region's metadata can
 * be populated or reclaimed independently. Entire tracking-region holes between
 * banks are omitted from the compact array.
 *
 * PA:    | hole | bank A | hole | bank B | full TR hole |  bank C   |
 * TR:    |------------- TR 0 ------------|   omitted    |-- TR 1 ---|
 * array: |-------- full TR 0 slots ------|              | TR 1 slots|
 *
 * Banks A and B have start index 0. Bank C starts after one complete granule
 * stride. @region_size must be a supported tracking-region size and @entry_size
 * is sizeof(struct granule) or sizeof(struct dev_granule). Return the total
 * number of array slots, including page-alignment padding, required by the
 * compact array.
 */
static unsigned long tracking_memory_banks_assign_fine_indices(
					struct tracking_memory_bank *banks,
					unsigned int count,
					unsigned long region_size,
					size_t entry_size)
{
	unsigned long current_top = 0UL;
	unsigned long num_granules = 0UL;
	unsigned long descriptors_per_region =
		tracking_region_fine_stride(region_size, entry_size);

	assert((region_size == TRACKING_REGION_MIN_SIZE) ||
	       (region_size == TRACKING_REGION_MAX_SIZE));

	for (unsigned int i = 0U; i < count; i++) {
		struct tracking_memory_bank *bank = &banks[i];
		unsigned long base = round_down(bank->base, region_size);
		unsigned long top =
			round_up(bank->base + bank->size, region_size);
		unsigned long start_idx;

		if ((i == 0U) || (base >= current_top)) {
			start_idx = num_granules;
			num_granules += ((top - base) / region_size) *
					descriptors_per_region;
			current_top = top;
		} else {
			unsigned long overlap_regions =
				(current_top - base) / region_size;
			unsigned long overlap = overlap_regions *
						 descriptors_per_region;

			/* Disjoint banks can share only one tracking region. */
			assert(overlap_regions <= 1UL);
			assert(overlap <= num_granules);
			start_idx = num_granules - overlap;
			if (top > current_top) {
				num_granules +=
					((top - current_top) / region_size) *
						descriptors_per_region;
				current_top = top;
			}
		}

		bank->granule_start_idx = start_idx;
	}

	return num_granules;
}

/*
 * Reserve VA for an array of @count entries, each @entry_size bytes.
 *
 * The required size is rounded up to a granule boundary and recorded in
 * @mapping in the reserved state. Backing is populated separately by the EL3
 * allocation path or from Host-donated pages. If @mapping already describes a
 * reservation, leave it unchanged and verify that it is large enough. @name is
 * used only for diagnostic logging.
 *
 * An empty array succeeds without modifying @mapping. Return 0 on success,
 * -EOVERFLOW if the rounded size cannot be represented, -ERANGE if an existing
 * reservation is too small, or an error from the architecture reservation.
 */
static int tracking_array_reserve(struct tracking_array_mapping *mapping,
				  unsigned long count,
				  size_t entry_size,
				  const char *name)
{
	size_t required_size;
	int ret;

	assert(mapping != NULL);
	assert(entry_size != 0UL);
	assert(name != NULL);

	if (count == 0UL) {
		return 0;
	}
	if (count > ((SIZE_MAX - (GRANULE_SIZE - 1UL)) / entry_size)) {
		return -EOVERFLOW;
	}

	required_size = round_up(count * entry_size, GRANULE_SIZE);
	if (mapping->size != 0UL) {
		return (required_size <= mapping->size) ? 0 : -ERANGE;
	}

	ret = tracking_region_arch_reserve(required_size, &mapping->va);
	if (ret != 0) {
		return ret;
	}

	mapping->size = required_size;
	mapping->state = TRACKING_REGIONS_RESERVED;

	INFO("Reserved %s VA: 0x%lx, size: 0x%lx\n",
	     name, mapping->va, mapping->size);

	return 0;
}

/*
 * Initialize the persistent tracking-region layout and its VA reservations.
 *
 * @data must identify granule-aligned storage for struct tracking_region_data,
 * and @data_size must cover the structure. During cold boot, the function
 * copies the platform's struct plat_memory_bank arrays into the embedded
 * struct tracking_memory_bank arrays for conventional and device memory,
 * and validates their PA ranges.
 * It then builds the shared tracking-region and fine-granule indices,
 * reserving enough VA for either supported region size.
 * Metadata backing is populated separately.
 *
 * The initial configuration uses 1 GiB tracking regions. RMI_RMM_CONFIG_SET may
 * select 2 MiB regions before granule initialization. On LFA, the initialized
 * struct tracking_region_data, including its indices and mappings, is reused
 * unchanged.
 *
 * A bank-list pointer may be NULL only when its corresponding count is zero.
 * Return 0 on success, or a negative error code for an invalid @data or
 * @data_size, an invalid or unrepresentable bank list, or a VA reservation
 * failure.
 */
int tracking_region_indices_init(
		uintptr_t data,
		size_t data_size,
		const struct plat_memory_bank *conv_banks,
		unsigned long conv_bank_count,
		const struct plat_memory_bank *dev_ncoh_banks,
		unsigned long dev_ncoh_bank_count,
		const struct plat_memory_bank *dev_coh_banks,
		unsigned long dev_coh_bank_count)
{
	struct tracking_memory_bank_storage *storage;
	unsigned long conv_granules_2mb;
	unsigned long conv_granules_1gb;
	unsigned long dev_granules_2mb;
	unsigned long dev_granules_1gb;
	unsigned long max_conv_granules;
	unsigned long max_dev_granules;
	unsigned long max_region_count;
	unsigned long default_region_count;
	unsigned int conv_count = 0U;
	unsigned int dev_count = 0U;
	int ret;

	if ((data == 0UL) || (data_size < sizeof(*tracking_data)) ||
	    !GRANULE_ALIGNED(data)) {
		return -EINVAL;
	}

	tracking_data = (struct tracking_region_data *)data;
	if (tracking_data->tracking_region_size != 0UL) {
		/*
		 * glob_data_init() already validated the persistent layout version.
		 * A configured size marks completed cold-boot initialization, so LFA
		 * reuses the indices in struct tracking_memory_bank, mappings and
		 * granule state.
		 */
		return 0;
	}

	storage = &tracking_data->banks;

	ret = tracking_region_copy_bank_category(conv_banks, conv_bank_count,
					     RMI_MEM_CATEGORY_CONVENTIONAL,
					     storage->conv_banks,
					     MAX_CONV_TRACKING_MEMORY_BANKS,
					     &conv_count);
	if (ret != 0) {
		return ret;
	}

	ret = tracking_region_copy_bank_category(dev_ncoh_banks,
					     dev_ncoh_bank_count,
					     RMI_MEM_CATEGORY_DEV_NCOH,
					     storage->dev_banks,
					     MAX_DEV_TRACKING_MEMORY_BANKS,
					     &dev_count);
	if (ret != 0) {
		return ret;
	}

	ret = tracking_region_copy_bank_category(dev_coh_banks,
					     dev_coh_bank_count,
					     RMI_MEM_CATEGORY_DEV_COH,
					     storage->dev_banks,
					     MAX_DEV_TRACKING_MEMORY_BANKS,
					     &dev_count);
	if (ret != 0) {
		return ret;
	}

	if ((conv_count == 0U) && (dev_count == 0U)) {
		return -EINVAL;
	}

	/* Keep each list ordered for binary lookup and validate its PA ranges. */
	tracking_region_sort_and_validate_banks(storage->conv_banks,
						conv_count);
	tracking_region_sort_and_validate_banks(storage->dev_banks,
						dev_count);
	tracking_memory_banks_validate_no_overlap(storage, conv_count,
						  dev_count);

	/*
	 * A 2 MiB size creates the most struct tracking_region objects. Fine-array
	 * requirements depend on bank-boundary padding and the granule stride,
	 * so calculate both supported sizes. Calculate the default 1 GiB layout last
	 * to leave the indices in struct tracking_memory_bank ready for initial use.
	 */
	max_region_count = tracking_memory_banks_assign_shared_indices(storage,
				conv_count, dev_count, TRACKING_REGION_MIN_SIZE);
	default_region_count = tracking_memory_banks_assign_shared_indices(storage,
				conv_count, dev_count, TRACKING_REGION_MAX_SIZE);
	conv_granules_2mb = tracking_memory_banks_assign_fine_indices(storage->conv_banks,
		conv_count, TRACKING_REGION_MIN_SIZE, sizeof(struct granule));
	conv_granules_1gb = tracking_memory_banks_assign_fine_indices(storage->conv_banks,
		conv_count, TRACKING_REGION_MAX_SIZE, sizeof(struct granule));
	dev_granules_2mb = tracking_memory_banks_assign_fine_indices(storage->dev_banks,
		dev_count, TRACKING_REGION_MIN_SIZE, sizeof(struct dev_granule));
	dev_granules_1gb = tracking_memory_banks_assign_fine_indices(storage->dev_banks,
		dev_count, TRACKING_REGION_MAX_SIZE, sizeof(struct dev_granule));
	max_conv_granules = MAX(conv_granules_2mb, conv_granules_1gb);
	max_dev_granules = MAX(dev_granules_2mb, dev_granules_1gb);

	ret = tracking_array_reserve(&tracking_data->tracking_region_array,
				     max_region_count,
				     sizeof(struct tracking_region),
				     "struct tracking_region array");
	if (ret != 0) {
		return ret;
	}

	ret = tracking_array_reserve(&tracking_data->granule_array_tr,
				     max_conv_granules,
				     sizeof(struct granule),
				     "tracking granule array");
	if (ret != 0) {
		return ret;
	}

	ret = tracking_array_reserve(&tracking_data->dev_granule_array_tr,
				     max_dev_granules,
				     sizeof(struct dev_granule),
				     "tracking device-granule array");
	if (ret != 0) {
		return ret;
	}

	tracking_data->num_conv_tracking_banks = conv_count;
	tracking_data->num_dev_tracking_banks = dev_count;
	tracking_data->num_tracking_regions = default_region_count;
	tracking_data->num_tracking_granules = conv_granules_1gb;
	tracking_data->num_tracking_dev_granules = dev_granules_1gb;
	tracking_data->tracking_region_size = TRACKING_REGION_MAX_SIZE;

	return 0;
}

/*
 * Select and build the active tracking-region layout before RMM activation.
 *
 * Cold boot installs the default maximum-size layout while reserving VA for
 * the worst supported metadata density. RMI_RMM_CONFIG_SET calls this before
 * granule initialization to select the Host-requested size. A request for
 * the current size succeeds without rebuilding the indices. A size change
 * rebuilds the shared tracking-region indices, the type-local fine-granule
 * indices, and their active counts without changing the existing VA
 * reservations or backing.
 *
 * The global layout lock excludes configuration reads, activation and
 * tracking-info queries while indices are rebuilt. The LFA path reuses the
 * persisted indices and does not call this function.
 * @tr_size must be TRACKING_REGION_MIN_SIZE or TRACKING_REGION_MAX_SIZE.
 * Returns 0 on success, or -EINVAL when struct tracking_region_data is
 * unavailable, @tr_size is not supported, or tracking granules have already
 * been initialized.
 */
int tracking_region_configure(unsigned long tr_size)
{
	struct tracking_memory_bank_storage *storage;
	unsigned long conv_granules;
	unsigned long dev_granules;
	unsigned long region_count;
	int ret = 0;

	if ((tracking_data == NULL) ||
	    ((tr_size != TRACKING_REGION_MIN_SIZE) &&
	     (tr_size != TRACKING_REGION_MAX_SIZE))) {
		return -EINVAL;
	}

	spinlock_acquire(&tracking_layout_lock);
	if (tracking_data->tracking_initialized) {
		ret = -EINVAL;
		goto out;
	}
	if (tracking_data->tracking_region_size == tr_size) {
		goto out;
	}

	storage = &tracking_data->banks;
	region_count = tracking_memory_banks_assign_shared_indices(storage,
				tracking_data->num_conv_tracking_banks,
				tracking_data->num_dev_tracking_banks, tr_size);
	conv_granules = tracking_memory_banks_assign_fine_indices(storage->conv_banks,
			tracking_data->num_conv_tracking_banks, tr_size,
			sizeof(struct granule));
	dev_granules = tracking_memory_banks_assign_fine_indices(storage->dev_banks,
			tracking_data->num_dev_tracking_banks, tr_size,
			sizeof(struct dev_granule));

	/* Boot reserved each VA array for the largest supported layout. */
	assert(region_count <=
	       (tracking_data->tracking_region_array.size /
		sizeof(struct tracking_region)));
	assert(conv_granules <=
	       (tracking_data->granule_array_tr.size / sizeof(struct granule)));
	assert(dev_granules <=
	       (tracking_data->dev_granule_array_tr.size /
		sizeof(struct dev_granule)));

	tracking_data->num_tracking_regions = region_count;
	tracking_data->num_tracking_granules = conv_granules;
	tracking_data->num_tracking_dev_granules = dev_granules;
	tracking_data->tracking_region_size = tr_size;
out:
	spinlock_release(&tracking_layout_lock);
	return ret;
}

/*
 * Return the configured tracking-region size in bytes without taking a lock.
 * The caller must ensure configuration cannot run concurrently.
 */
unsigned long tracking_region_get_size(void)
{
	assert((tracking_data != NULL) &&
	       (tracking_data->tracking_region_size != 0UL));

	return tracking_data->tracking_region_size;
}

/*
 * Return the configured size in bytes for RMI_RMM_CONFIG_GET, serializing the
 * read with configuration and activation. The caller must not hold the layout
 * lock, a tracking-region lock or a Granule lock. No lock remains held on return.
 */
unsigned long tracking_region_get_rmm_config_size(void)
{
	unsigned long size;

	spinlock_acquire(&tracking_layout_lock);
	size = tracking_region_get_size();
	spinlock_release(&tracking_layout_lock);

	return size;
}

/*
 * Binary-search the selected struct tracking_memory_bank array for @addr.
 * On success, return the matching struct tracking_memory_bank and the
 * corresponding shared tracking-region and type-local fine-granule indices.
 * Return NULL if no bank of @type contains @addr.
 */
static const struct tracking_memory_bank *tracking_region_find_addr(
					unsigned long addr,
					enum tr_mem_type type,
					unsigned long *tracking_region_idx,
					unsigned long *granule_idx)
{
	const struct tracking_memory_bank_storage *storage =
		&tracking_data->banks;
	const struct tracking_memory_bank *banks;
	unsigned long granule_stride;
	unsigned long region_size = tracking_region_get_size();
	unsigned int count;
	unsigned int l = 0U;
	unsigned int r;

	assert(tracking_region_idx != NULL);
	assert(granule_idx != NULL);

	if (type == TR_MEM_TYPE_CONV) {
		banks = storage->conv_banks;
		count = tracking_data->num_conv_tracking_banks;
		granule_stride = tracking_region_fine_stride(
					region_size, sizeof(struct granule));
	} else if (type == TR_MEM_TYPE_DEV) {
		banks = storage->dev_banks;
		count = tracking_data->num_dev_tracking_banks;
		granule_stride = tracking_region_fine_stride(
					region_size, sizeof(struct dev_granule));
	} else {
		return NULL;
	}

	if (count == 0U) {
		return NULL;
	}

	r = count - 1U;
	while (l <= r) {
		const struct tracking_memory_bank *bank;
		unsigned int i = l + ((r - l) / 2U);

		assert(i < count);
		bank = &banks[i];
		if (addr < bank->base) {
			if (i == 0U) {
				break;
			}
			r = i - 1U;
		} else if (addr >= (bank->base + bank->size)) {
			l = i + 1U;
		} else {
			/*
			 * tracking_base is the aligned base of the first tracking
			 * region intersecting the bank, which may precede bank->base.
			 * region_base is the aligned base of the tracking region
			 * containing addr.
			 */
			unsigned long tracking_base =
				round_down(bank->base, region_size);
			unsigned long region_base =
				round_down(addr, region_size);
			/* Number of tracking regions from the bank's first region. */
			unsigned long region_offset =
				(region_base - tracking_base) / region_size;
			/* Granule offset within the region containing addr. */
			unsigned long granule_offset =
				(addr - region_base) >> GRANULE_SHIFT;

			*tracking_region_idx =
				(unsigned long)bank->tracking_start_idx +
				region_offset;
			/*
			 * Each preceding region occupies a full granule stride,
			 * including padding. Then select the granule within this region.
			 */
			*granule_idx = bank->granule_start_idx +
				(region_offset * granule_stride) + granule_offset;
			return bank;
		}
	}

	return NULL;
}

/*
 * Iterate over banks of @type overlapping the tracking region at @base.
 * @base must be tracking-region aligned. Initialize @cursor to zero for
 * each new region/type combination and preserve it between calls.
 *
 * Return true with one bank's non-empty portion inside the region as
 * [@start, @end), set @fine_idx to the type-local fine-granule index
 * for @start, and advance @cursor. Holes are skipped.
 *
 * Return false when no more banks overlap the region.
 */
bool tracking_region_next_bank_range(unsigned long base,
				     enum tr_mem_type type,
				     unsigned int *cursor,
				     unsigned long *start,
				     unsigned long *end,
				     unsigned long *fine_idx)
{
	const struct tracking_memory_bank_storage *storage;
	const struct tracking_memory_bank *banks;
	unsigned long granule_stride;
	unsigned long region_size = tracking_region_get_size();
	unsigned long top;
	unsigned int count;

	assert((tracking_data != NULL) && (cursor != NULL) &&
	       (start != NULL) && (end != NULL) && (fine_idx != NULL));
	assert(ALIGNED(base, region_size));
	assert(base <= (UINT64_MAX - region_size));

	storage = &tracking_data->banks;
	if (type == TR_MEM_TYPE_CONV) {
		banks = storage->conv_banks;
		count = tracking_data->num_conv_tracking_banks;
		granule_stride = tracking_region_fine_stride(
					region_size, sizeof(struct granule));
	} else {
		assert(type == TR_MEM_TYPE_DEV);
		banks = storage->dev_banks;
		count = tracking_data->num_dev_tracking_banks;
		granule_stride = tracking_region_fine_stride(
					region_size, sizeof(struct dev_granule));
	}
	top = base + region_size;

	while (*cursor < count) {
		const struct tracking_memory_bank *bank = &banks[*cursor];
		unsigned long bank_top = bank->base + bank->size;
		unsigned long tr_offset;
		unsigned long descriptor_slots;
		unsigned long descriptor_offset;

		(*cursor)++;
		if (bank->base >= top) {
			return false;
		}
		if (bank_top <= base) {
			continue;
		}

		*start = (bank->base > base) ? bank->base : base;
		*end = (bank_top < top) ? bank_top : top;

		/* Number of regions from the bank's first region to this one. */
		tr_offset = (base - round_down(bank->base, region_size)) /
			    region_size;

		/* Each region reserves a full granule stride, including padding. */
		descriptor_slots = tr_offset * granule_stride;

		/* Granule offset of *start within the current tracking region. */
		descriptor_offset = (*start - base) >> GRANULE_SHIFT;

		/* Type-local fine-granule index for *start. */
		*fine_idx = bank->granule_start_idx +
			    descriptor_slots + descriptor_offset;
		assert(*start < *end);
		return true;
	}

	return false;
}

/*
 * Find the struct tracking_region for @addr in memory of @type.
 *
 * Return NULL if the struct tracking_region array is unavailable or @addr does
 * not belong to a configured bank of @type. The returned struct tracking_region
 * is not locked.
 */
struct tracking_region *tracking_region_find(unsigned long addr,
					     enum tr_mem_type type)
{
	unsigned long idx;

	if ((tracking_data == NULL) ||
	    (tracking_data->tracking_regions == NULL)) {
		return NULL;
	}

	idx = tracking_region_addr_to_idx(addr, type, NULL);
	if (idx >= tracking_data->num_tracking_regions) {
		return NULL;
	}

	return &tracking_data->tracking_regions[idx];
}

/*
 * Return the start of the next populated range in (@addr, @limit).
 *
 * Conventional and device memory use separate PA-ordered arrays of
 * struct tracking_memory_bank. The first bank base greater than @addr in each
 * array is therefore its only candidate; return the earlier candidate. If
 * neither array has a bank starting before @limit, return @limit. The result
 * marks the end of the unpopulated range that begins at @addr.
 */
static unsigned long tracking_memory_bank_next_base(unsigned long addr,
					     unsigned long limit)
{
	const struct tracking_memory_bank_storage *storage =
		&tracking_data->banks;
	const struct tracking_memory_bank *bank_lists[] = {
		storage->conv_banks,
		storage->dev_banks
	};
	const unsigned int bank_counts[] = {
		tracking_data->num_conv_tracking_banks,
		tracking_data->num_dev_tracking_banks
	};
	unsigned long next = limit;

	for (unsigned int list = 0U; list < ARRAY_SIZE(bank_lists); list++) {
		for (unsigned int i = 0U; i < bank_counts[list]; i++) {
			unsigned long base = bank_lists[list][i].base;

			if (base > addr) {
				if (base < next) {
					next = base;
				}
				break;
			}
		}
	}

	return next;
}

/*
 * Resolve the tracking-region index when @base lies in a hole but
 * a memory bank starts later within the same tracking region.
 *
 * @base and @top delimit one tracking region. Find the first populated bank in
 * (@base, @top), then use an address in that bank to obtain the shared region
 * index. The bank's category is irrelevant because the unpopulated prefix
 * already makes the region diverse.
 *
 * tracking_region_set_tracking_find() uses the returned index to select the
 * shared struct tracking_region for the requested transition. It also
 * returns the index to SRO callers, which use it to locate the region's
 * type-local fine-metadata ranges. @idx is not a fine-granule array index.
 *
 * Return true with @idx set when the region contains a populated bank after
 * @base. Return false when the remainder of the region is unpopulated.
 */
static bool tracking_region_find_after_base(unsigned long base,
					    unsigned long top,
					    unsigned long *idx)
{
	const struct tracking_memory_bank *bank __unused;
	unsigned long granule_idx __unused;
	unsigned long next;

	assert((idx != NULL) && (base < top));

	next = tracking_memory_bank_next_base(base, top);
	if (next >= top) {
		return false;
	}

	bank = tracking_memory_bank_find_any(next, idx, &granule_idx);
	assert(bank != NULL);
	return true;
}

/*
 * Return the memory category and tracking state at @addr.
 *
 * @limit is an exclusive upper bound. On success, @region_top receives the
 * first address after @addr at which the category or tracking-region state may
 * differ, capped at @limit. For a populated address, stop at the end of the
 * containing bank or current tracking region, whichever occurs first. For an
 * unpopulated address, stop at the start of the next bank.
 *
 * For a populated address, return the bank category and the state of its
 * shared struct tracking_region, or trs_none before activation. For an
 * unpopulated address, report RMI_MEM_CATEGORY_NONE and trs_reserved.
 *
 * Hold the global layout lock from index lookup through state inspection so
 * configuration and activation cannot invalidate the selected
 * struct tracking_region.
 * Acquire the region read lock inside that lock when reading an initialized
 * struct tracking_region. The caller must not hold a region or Granule lock.
 * No lock remains held on return.
 *
 * Return true with all outputs set when @addr is below @limit. Return false
 * when the requested interval is empty; the outputs are then unspecified.
 */
bool tracking_region_get_info(unsigned long addr,
			      unsigned long limit,
			      unsigned long *category,
			      enum tr_state *state,
			      unsigned long *region_top)
{
	const struct tracking_memory_bank *bank;
	unsigned long granule_idx __unused;
	unsigned long idx;
	unsigned long region_size;
	unsigned long top;

	assert((category != NULL) && (state != NULL) &&
	       (region_top != NULL));
	assert(tracking_data != NULL);

	if (addr >= limit) {
		return false;
	}

	spinlock_acquire(&tracking_layout_lock);
	assert(tracking_data->num_tracking_regions != 0UL);
	region_size = tracking_region_get_size();
	idx = UINT64_MAX;
	bank = tracking_memory_bank_find_any(addr, &idx, &granule_idx);
	top = round_down(addr, region_size) + region_size;
	if (top > limit) {
		top = limit;
	}

	if (bank != NULL) {
		unsigned long bank_top = bank->base + bank->size;

		assert(idx < tracking_data->num_tracking_regions);
		*category = bank->category;
		if (bank_top < top) {
			top = bank_top;
		}
	} else {
		*category = RMI_MEM_CATEGORY_NONE;
		/* NONE/RESERVED remains unchanged until the next populated bank. */
		top = tracking_memory_bank_next_base(addr, limit);
	}

	if (idx == UINT64_MAX) {
		*state = trs_reserved;
	} else if (!tracking_data->tracking_initialized) {
		*state = trs_none;
	} else {
		assert(idx < tracking_data->num_tracking_regions);
		tracking_region_read_lock(&tracking_data->tracking_regions[idx]);
		*state = tracking_region_get_state(
					&tracking_data->tracking_regions[idx]);
		tracking_region_read_unlock(
					&tracking_data->tracking_regions[idx]);
	}

	assert(top > addr);
	*region_top = top;
	spinlock_release(&tracking_layout_lock);
	return true;
}

/*
 * Convert @addr to an index in the fine-granule array selected by @type.
 *
 * @addr must be Granule-aligned and belong to a configured bank of @type. The
 * returned type-local index includes granule slots reserved for any holes
 * within a tracking region. If @category is non-NULL, set it to the exact RMI
 * memory category of the containing bank.
 *
 * Return UINT64_MAX if @addr is unaligned, @type is invalid, or no selected
 * bank contains @addr. This lookup does not access or lock the granule.
 */
unsigned long tracking_region_fine_addr_to_idx(
					unsigned long addr,
					enum tr_mem_type type,
					unsigned long *category)
{
	const struct tracking_memory_bank *bank;
	unsigned long granule_idx;
	unsigned long tracking_region_idx __unused;

	assert((tracking_data != NULL) &&
	       (tracking_data->num_tracking_regions != 0UL));

	if (!GRANULE_ALIGNED(addr)) {
		return UINT64_MAX;
	}

	bank = tracking_region_find_addr(addr, type, &tracking_region_idx,
					 &granule_idx);
	if (bank == NULL) {
		return UINT64_MAX;
	}

	if (category != NULL) {
		*category = bank->category;
	}

	return granule_idx;
}

/*
 * Convert @idx in the fine-granule array selected by @type to a PA.
 *
 * Each bank reserves a fixed granule stride for every tracking region it
 * intersects. The stride includes slots for holes and page-alignment padding.
 * Locate the struct tracking_memory_bank whose reserved granule-array span
 * contains @idx, derive the corresponding Granule address, and accept it only
 * when that address lies within the bank's PA range.
 * A tracking region shared by multiple banks may require checking more than
 * one reserved span.
 *
 * If @category is non-NULL, set it to the exact RMI memory category of the
 * containing bank. Return UINT64_MAX when @type or @idx is invalid, or when
 * @idx selects padding or an unpopulated hole. This lookup does not access or
 * lock the granule.
 */
unsigned long tracking_region_fine_idx_to_addr(
					unsigned long idx,
					enum tr_mem_type type,
					unsigned long *category)
{
	const struct tracking_memory_bank_storage *storage =
		&tracking_data->banks;
	const struct tracking_memory_bank *banks;
	unsigned long granule_stride;
	unsigned long region_size = tracking_region_get_size();
	unsigned long granules_per_region = region_size / GRANULE_SIZE;
	unsigned int count;

	assert((tracking_data != NULL) &&
	       (tracking_data->num_tracking_regions != 0UL));

	if (type == TR_MEM_TYPE_CONV) {
		banks = storage->conv_banks;
		count = tracking_data->num_conv_tracking_banks;
		granule_stride = tracking_region_fine_stride(
					region_size, sizeof(struct granule));
		if (idx >= tracking_data->num_tracking_granules) {
			return UINT64_MAX;
		}
	} else if (type == TR_MEM_TYPE_DEV) {
		banks = storage->dev_banks;
		count = tracking_data->num_dev_tracking_banks;
		granule_stride = tracking_region_fine_stride(
					region_size, sizeof(struct dev_granule));
		if (idx >= tracking_data->num_tracking_dev_granules) {
			return UINT64_MAX;
		}
	} else {
		return UINT64_MAX;
	}

	/* A shared boundary tracking region may be represented by multiple banks. */
	for (unsigned int i = 0U; i < count; i++) {
		const struct tracking_memory_bank *bank = &banks[i];
		unsigned long tracking_base =
			round_down(bank->base, region_size);
		unsigned long tracking_top =
			round_up(bank->base + bank->size, region_size);
		unsigned long bank_regions =
			(tracking_top - tracking_base) / region_size;
		unsigned long bank_descriptors = bank_regions * granule_stride;

		if ((idx >= bank->granule_start_idx) &&
		    (idx < (bank->granule_start_idx + bank_descriptors))) {
			unsigned long relative = idx - bank->granule_start_idx;
			unsigned long offset = relative % granule_stride;
			unsigned long addr;

			/* Page-alignment padding does not describe a PA. */
			if (offset >= granules_per_region) {
				continue;
			}
			addr = tracking_base +
				((relative / granule_stride) * region_size) +
				(offset << GRANULE_SHIFT);

			if ((addr < bank->base) ||
			    (addr >= (bank->base + bank->size))) {
				continue;
			}
			if (category != NULL) {
				*category = bank->category;
			}
			return addr;
		}
	}

	return UINT64_MAX;
}

/*
 * Return the fine granule at @idx.
 *
 * @idx is a type-local index into the fine granule array and must be smaller
 * than the configured granule count. This accessor does not verify that the
 * slot represents populated memory and does not acquire any lock. The caller
 * must provide the locking required for its operation.
 */
struct granule *tr_fine_granule_from_idx(unsigned long idx)
{
	struct granule *granules =
		(struct granule *)tracking_data->granule_array_tr.va;

	assert((granules != NULL) &&
	       (idx < tracking_data->num_tracking_granules));

	return &granules[idx];
}

/* Return the index of fine granule @g. */
unsigned long tr_fine_granule_to_idx(const struct granule *g)
{
	const struct granule *granules =
		(const struct granule *)tracking_data->granule_array_tr.va;
	unsigned long idx;

	assert((g != NULL) && (granules != NULL));
	assert(ALIGNED_TO_ARRAY(g, granules));

	idx = ((uintptr_t)g - (uintptr_t)granules) / sizeof(*g);
	assert(idx < tracking_data->num_tracking_granules);

	return idx;
}

/* Return the fine dev_granule at @idx. */
struct dev_granule *tr_fine_dev_granule_from_idx(unsigned long idx)
{
	struct dev_granule *granules =
		(struct dev_granule *)tracking_data->dev_granule_array_tr.va;

	assert((granules != NULL) &&
	       (idx < tracking_data->num_tracking_dev_granules));

	return &granules[idx];
}

/* Return the index of fine dev_granule @g. */
unsigned long tr_fine_dev_granule_to_idx(const struct dev_granule *g)
{
	const struct dev_granule *granules =
		(const struct dev_granule *)tracking_data->dev_granule_array_tr.va;
	unsigned long idx;

	assert((g != NULL) && (granules != NULL));
	/* cppcheck-suppress moduloofone */
	assert(ALIGNED_TO_ARRAY(g, granules));

	idx = ((uintptr_t)g - (uintptr_t)granules) / sizeof(*g);
	assert(idx < tracking_data->num_tracking_dev_granules);

	return idx;
}

/*
 * Return a physical address within both region @tr_idx and a bank in @banks.
 * If non-NULL, @granule_idx receives the fine-granule index for
 * that address. Return UINT64_MAX if no bank intersects the region.
 *
 * @banks contains @count struct tracking_memory_bank entries of one type
 * (conventional or device). @entry_size is the size of struct granule or
 * struct dev_granule for @type.
 * If multiple disjoint banks share @tr_idx, their aligned granule-array
 * range is identical and the first match is sufficient.
 */
static unsigned long tracking_region_lookup_by_idx(
					const struct tracking_memory_bank *banks,
					unsigned int count,
					unsigned long tr_idx,
					size_t entry_size,
					unsigned long *granule_idx)
{
	unsigned long region_size = tracking_region_get_size();
	unsigned long granule_stride =
		tracking_region_fine_stride(region_size, entry_size);

	for (unsigned int i = 0U; i < count; i++) {
		const struct tracking_memory_bank *bank = &banks[i];
		unsigned long bank_count_regions;
		unsigned long tracking_base;
		unsigned long tracking_top;

		tracking_base = round_down(bank->base, region_size);
		tracking_top =
			round_up(bank->base + bank->size, region_size);
		bank_count_regions =
			(tracking_top - tracking_base) / region_size;
		if ((tr_idx >= (unsigned long)bank->tracking_start_idx) &&
		    (tr_idx < ((unsigned long)bank->tracking_start_idx +
			    bank_count_regions))) {
			unsigned long addr = tracking_base +
				((tr_idx - (unsigned long)bank->tracking_start_idx) *
				 region_size);

			/* The region can start with a hole before the first bank address. */
			if (addr < bank->base) {
				addr = bank->base;
			}
			assert(addr < (bank->base + bank->size));
			if (granule_idx != NULL) {
				unsigned long region_base =
					round_down(addr, region_size);

				/* Select the region range, then the valid Granule within it. */
				*granule_idx = bank->granule_start_idx +
					((tr_idx -
					  (unsigned long)bank->tracking_start_idx) *
					 granule_stride) +
					((addr - region_base) >> GRANULE_SHIFT);
			}
			return addr;
		}
	}

	return UINT64_MAX;
}

/*
 * Binary-search the selected struct tracking_memory_bank array to validate
 * @addr and calculate its compressed struct tracking_region array index.
 * If non-NULL, @category receives the exact memory category. Return UINT64_MAX
 * when @addr is invalid for @type.
 */
unsigned long tracking_region_addr_to_idx(unsigned long addr,
					  enum tr_mem_type type,
					  unsigned long *category)
{
	const struct tracking_memory_bank *bank;
	unsigned long granule_idx __unused;
	unsigned long tracking_region_idx;

	assert((tracking_data != NULL) &&
	       (tracking_data->num_tracking_regions != 0UL));

	if (!GRANULE_ALIGNED(addr)) {
		return UINT64_MAX;
	}

	bank = tracking_region_find_addr(addr, type, &tracking_region_idx,
					 &granule_idx);
	if (bank == NULL) {
		return UINT64_MAX;
	}

	if (category != NULL) {
		*category = bank->category;
	}

	return tracking_region_idx;
}
