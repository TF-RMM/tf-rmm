/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef TRACKING_REGION_H
#define TRACKING_REGION_H

#include <granule_types.h>
#include <platform_api.h>
#include <smc-rmi.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

/* Tracking regions range from 2 MiB (2^21 bytes) to 1 GiB (2^30 bytes) for 4K pagesize */
#define TRACKING_REGION_MIN_SHIFT	U(21)
#define TRACKING_REGION_MAX_SHIFT	U(30)
#define TRACKING_REGION_MIN_SIZE		(UL(1) << TRACKING_REGION_MIN_SHIFT)
#define TRACKING_REGION_MAX_SIZE		(UL(1) << TRACKING_REGION_MAX_SHIFT)
/*
 * Storage size for struct tracking_region_data, including its embedded
 * struct tracking_memory_bank arrays. Allocated at boot through
 * rmm_el3_ifc_reserve_memory() and retained across LFA.
 */
#define TRACKING_REGION_DATA_SIZE	UL(0x2000)

enum tr_mem_cat {
	mc_conv = RMI_MEM_CATEGORY_CONVENTIONAL,
	mc_dev_ncoh = RMI_MEM_CATEGORY_DEV_NCOH,
	mc_dev_coh = RMI_MEM_CATEGORY_DEV_COH,
	/* Multiple categories or holes; coarse tracking is not permitted. */
	mc_diverse
};

enum tr_mem_type {
	TR_MEM_TYPE_CONV,
	TR_MEM_TYPE_DEV
};

enum tr_state {
	trs_reserved = RMI_TRACKING_RESERVED,
	trs_none = RMI_TRACKING_NONE,
	trs_fine = RMI_TRACKING_FINE,
	trs_coarse = RMI_TRACKING_COARSE
};

/*
 * Bind the struct tracking_region_data storage at @data. On first boot, copy
 * the platform memory banks into its embedded struct tracking_memory_bank
 * arrays and reserve VA for the largest supported tracking-array layouts.
 * An LFA instance reuses the initialized struct tracking_region_data.
 * @data must be granule-aligned, and @data_size must cover the structure.
 * Returns 0 on success or a negative error code if the storage or bank lists
 * cannot be represented, or the tracking-array VA cannot be reserved. This
 * must be called before any tracking-region conversion or population function.
 */
int tracking_region_indices_init(
		uintptr_t data,
		size_t data_size,
		const struct plat_memory_bank *conv_banks,
		unsigned long conv_bank_count,
		const struct plat_memory_bank *dev_ncoh_banks,
		unsigned long dev_ncoh_bank_count,
		const struct plat_memory_bank *dev_coh_banks,
		unsigned long dev_coh_bank_count);

/*
 * Select the active tracking-region layout before RMM activation.
 *
 * Cold boot installs the default layout while reserving VA for the worst
 * supported layout. RMI_RMM_CONFIG_SET may call this before granules are
 * initialized to select another supported size. Selecting the current size is
 * a no-op; changing it rebuilds the shared tracking-region and type-local
 * fine-granule indices and counts. A global layout lock serializes this
 * operation with configuration reads, activation and tracking-info queries.
 * The reserved VA ranges and their backing are not moved or resized. LFA
 * reuses the persisted layout and does not call this function.
 *
 * @tr_size must be between TRACKING_REGION_MIN_SIZE and TRACKING_REGION_MAX_SIZE.
 * Returns 0 on success, or -EINVAL if struct tracking_region_data is
 * unavailable, @tr_size is not supported, or tracking granules have already
 * been initialized.
 */
int tracking_region_configure(unsigned long tr_size);

/*
 * Return the configured tracking-region size in bytes without taking a lock.
 * The caller must ensure configuration cannot run concurrently.
 */
unsigned long tracking_region_get_size(void);

/*
 * Return the configured size in bytes under the global layout lock, including
 * before activation when configuration may change it. The caller must not
 * hold the layout lock, a tracking-region lock or a Granule lock. No lock
 * remains held on return.
 */
unsigned long tracking_region_get_rmm_config_size(void);

/*
 * Allocate EL3-private backing for the struct tracking_region array at cold boot.
 * If @fine is true, also populate both fine granule arrays. Populate the
 * complete reservations so later configuration does not allocate memory.
 * Existing committed mappings are retained across LFA. Private backing is
 * outside Host-managed memory and needs no tracking metadata of its own.
 * Returns 0 on success or a negative error code; failure is boot-fatal.
 */
int tracking_region_populate_from_el3(bool fine);

/*
 * Initialize the configured tracking layout from mapped, zeroed backing.
 * @state must be trs_fine or trs_coarse. Fine initialization requires both
 * fine arrays populated; coarse initialization leaves diverse regions at NONE.
 * The struct tracking_region array uses EL3-private backing allocated at boot.
 * The global layout lock excludes configuration and tracking-info queries.
 * Call once during activation; this operation cannot fail.
 */
void tracking_region_activate(enum tr_state state);

struct smc_result;

/*
 * Start an SRO-aware tracking transition. Fine tracking donates metadata
 * pages and a transition away from fine tracking reclaims them. Transitions
 * which transfer no memory complete synchronously. @addr, @category and
 * @state have the same contracts as tracking_region_set_tracking(). @res
 * receives the synchronous result or the first incomplete SRO response.
 */
void tracking_region_set_sro(unsigned long addr,
			     unsigned long category,
			     unsigned long state,
			     struct smc_result *res);

/*
 * Dispatch a follow-up SRO command for tracking-state changes.
 * The generic SRO layer must have assigned the sealed context to this PE.
 * @res receives either the next memory request or the terminal RMI result.
 */
void tracking_region_sro_handler(unsigned long fid, struct smc_result *res);

/*
 * Return the memory category and tracking state at @addr. @limit is the
 * exclusive upper bound supplied by the caller. @region_top receives the
 * first address at which either returned attribute may change, capped at
 * @limit. The global layout lock excludes configuration and activation for the
 * complete query, and precedes the region read lock used to inspect state.
 * The caller must not hold a region or Granule lock. No lock remains held on
 * return. Returns false when @addr >= @limit.
 */
bool tracking_region_get_info(unsigned long addr,
			      unsigned long limit,
			      unsigned long *category,
			      enum tr_state *state,
			      unsigned long *region_top);

/*
 * Change the state of the tracking region at @addr. @addr must be tracking-
 * region aligned. @category must match a populated base. An unpopulated base
 * is accepted only for NONE or FINE tracking of a diverse region, for which
 * @category is ignored.
 * Intermediate tracking is not supported. A transition holds the tracking-
 * region write lock and every granule in its active source representation.
 * Try the writer and source locks without waiting. Return RMI_BUSY on
 * contention after releasing every lock acquired by this attempt; the source
 * representation is unchanged and the caller may retry. Once all locks are
 * held, no further Granule lock may be acquired before publication completes.
 * Return RMI_BLOCKED if an incomplete tracking SRO owns the region. Otherwise,
 * return RMI_SUCCESS or RMI_ERROR_INPUT for invalid inputs or source state.
 */
unsigned long tracking_region_set_tracking(unsigned long addr,
					   unsigned long category,
					   unsigned long state);

#endif /* TRACKING_REGION_H */
