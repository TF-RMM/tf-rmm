/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef SRO_CONTEXT_H
#define SRO_CONTEXT_H

#include <addr_list.h>
#include <dev_type.h>
#include <smc-rmi.h>
#include <smc.h>
#include <sro_aux.h>
#include <xlat_defs.h>

/*
 * The `sro_context` library manages the storage space for the context of
 * Stateful RMM Operations (SROs).
 *
 * Usage:
 * - sro_ctx_reserve(command): Assigns SRO context to the running CPU.
 *                             Called at the start of the handle that initiates
 *                             a stateful operation.
 * - sro_ctx_release(): Called at the end of the handle if the context is not needed.
 * - sro_ctx_seal(): Called at the end of the handle if context needs to be preserved.
 *                   It returns the handle of the context that is passed to the Host.
 * - sro_ctx_find(handle): Used by continuing operations (rmi_op_xxx) to find and
 *                         assign SRO context to the running CPU.
 * - my_sro_ctx(): Returns pointer to the SRO context that is assigned to the
 *		   running CPU.
 *
 * Note that the library is agnostic to the actual content of the objects as
 * the content is very specific to each command (or, to a family of commands).
 */

/*
 * As the SRO contexts may remain allocated when RMI handler exits
 * to host, this should be considerable larger than CPU count.
 */
#define SRO_CTX_PER_CPU		(10UL)

/* Macro to define an invalid RmiResult value */
#define SRO_INVALID_RESULT	(~0UL)

/*
 * Total allocation size required for the sro_ctx_pool:
 * the pool header followed immediately by the sro_context array.
 */
#define SRO_CTX_POOL_SIZE \
	(sizeof(struct sro_ctx_pool) + \
	 (sizeof(struct sro_context) * (MAX_CPUS * SRO_CTX_PER_CPU)))

/*
 * Number of memory ranges to donate for PSMMU activation:
 *   - L1 Stream Table
 *   - SMMUv3 Command queue
 *   - SMMUv3 Event queue
 */
#define SRO_SMMU_RANGES		3U

/*
 * Data structure with the information to continue a REC related operation.
 */
struct sro_rec_ctx {
	/* Parameters for REC creation */
	unsigned long rd_addr;
	unsigned long rec_params_addr;
};

/*
 * Data structures with the information to continue a SMMU related operation.
 */
struct smmuv3_dev;

struct sro_smmu_range {
	/* Number of granules in block to donate during SMMU SRO operation */
	unsigned long requested;

	/* Contiguous flag */
	unsigned long contig;

	/*
	 * Base physical address of the donated range.
	 */
	uintptr_t base;
};

struct sro_smmu_ctx {
	/* Pointer to the SMMUv3 driver structure */
	struct smmuv3_dev *smmu_ptr;

	/* SID */
	unsigned long sid;

	/* Index of the callback to invoke */
	unsigned int cb_id;

	/* Index of the range to donate in smmu_range[] */
	unsigned int range_idx;

	/* Number of granules requested in the current range */
	unsigned long requested;

	/* Number of granules donated or reclaimed in the current range */
	unsigned long transferred;

	/* Number of granules donated or reclaimed so far */
	unsigned long total_transferred;

	/* Donation ranges */
	struct sro_smmu_range smmu_range[SRO_SMMU_RANGES];

	/* Error condition in case operation fails */
	unsigned long ret_err;
};

/* State of an SRO context */
enum sro_state {
	/* SRO is available */
	SRO_STATE_FREE,

	/* SRO is in used by a running RMI handler */
	SRO_STATE_RESERVED,

	/* SRO is reserved after exit to Host */
	SRO_STATE_SEALED
};

/*
 * Data structure with the information to continue a PDEV related operation.
 */
struct sro_pdev_ctx {
	/* Parameters for PDEV creation */
	unsigned long flags;
	unsigned long hb_base;
	unsigned long pdev_id;
	uint16_t routing_id;
	unsigned long id_index;
	unsigned int rid_base;
	unsigned int rid_top;
	unsigned char hash_algo;
};

struct granule;
struct s2tt_context;

/*
 * State carried by an in-flight RMI_RTT_DATA_UNMAP or RMI_RTT_UNPROT_UNMAP
 * across one or more RMI_OP_CONTINUE round-trips.
 *
 * RMI_RTT_DATA_UNMAP additionally defers the per-entry leaf-RTT
 * refcount drops (one per live entry the sweep freed) and a per-DATA
 * granule cache-maintenance drain back to DELEGATED. The un-dropped
 * refcounts naturally pin @g_llt across yields, and the @pending_*
 * cursors point to the next granule to drain inside @addr_list so
 * the SRO_CONTINUE entry can resume in-place. RMI_RTT_UNPROT_UNMAP
 * does not own DATA granules, so the drain cursors stay zero; the
 * extra @g_llt refcount taken at yield time is what pins the leaf.
 */
struct sro_unmap_ctx {
	struct granule *g_llt;		/* Leaf RTT pinned across yields */
	unsigned long oaddr;		/* LIST: NS PA of output buffer */
	unsigned long cur_base;		/* Next IPA to sweep; also out_top */
	unsigned int oaddr_type;	/* RmiAddrType: NONE / SINGLE / LIST */
	/*
	 * Drain cursors into sro_context::addr_list. DATA_UNMAP and
	 * DEV_UNMAP only; UNPROT_UNMAP does not use them.
	 */
	unsigned int pending_desc_idx;	/* next descriptor to drain */
	unsigned long pending_blk_idx;	/* next block within descriptor */
	unsigned long pending_pa;	/* next granule PA, or ~0UL before block start */
	/*
	 * SRO handle stamped into every s2tte the sweep writes. The
	 * drain-completion pass matches this handle to identify and
	 * clear its own marks. Set once at entry, never mutated. Width
	 * must fit within S2TTE_SW_HANDLE in s2tt.h.
	 */
	unsigned int sro_handle;
	/*
	 * MECID snapshot of the primary S2 context. Cached at entry so
	 * the SRO continue path can map the leaf RTT without needing to
	 * re-acquire the RD granule.
	 */
	unsigned int mecid;
	/*
	 * VMIDs and DA flag snapshot used by the deferred stage-2 TLB /
	 * SMMU invalidation that the drain-completion pass issues for
	 * every TTE carrying S2TTE_SW_TLBI_PENDING. Cached at entry so
	 * the SRO continue path can invalidate without an RD granule.
	 * Width fits MAX_S2_CTXS (one primary plane + auxiliary planes);
	 * in the direct (single-VMID) case nvmids == 1 and vmid_list[0]
	 * is the primary plane's vmid.
	 */
	unsigned int vmid_list[MAX_TOTAL_PLANES];
	unsigned int nvmids;
	bool da_enabled;
	/*
	 * Base IPA and level of the currently-pinned leaf RTT (@g_llt),
	 * cached when the sweep enters each leaf so the drain-completion
	 * pass can compute the IPA of every stamped TTE for its deferred
	 * TLBI. Carried across an IRQ-yield so the SRO continue path can
	 * reuse the same coordinates after reacquiring @g_llt.
	 */
	unsigned long leaf_base_ipa;
	long leaf_level;
};

/*
 * State carried by an in-flight RMI_RTT_DATA_MAP or RMI_RTT_DEV_MAP
 * block-level mapping across one or more RMI_OP_CONTINUE round-trips.
 *
 * The entry path validates the request and stamps the leaf s2tte with
 * the SRO handle plus the drain-pending bit so that concurrent
 * map/unmap/RIPAS operations on the same IPA back off with RMI_BUSY /
 * -EAGAIN. The leaf is pinned across yields by one extra refcount on
 * @g_llt taken when the marker is stamped; that refcount is the same
 * one the finalize step keeps to represent the eventual live mapping.
 *
 * DATA_MAP drains by transitioning, mapping and zeroing each backing
 * granule. DEV_MAP drains by locking each backing dev_granule and
 * unlock-transitioning it from DELEGATED to MAPPED. On a pending IRQ
 * the @pending_off cursor records the next byte offset still owing the
 * drain so the SRO continue path can resume in-place. If a drain-time
 * error starts rollback, @rollback is set, @ret_err records the
 * terminal error, and @pending_off is reused as the count of already
 * drained bytes still to roll back. When the drain completes, the leaf
 * s2tte is rewritten to the command-specific assigned form for the
 * target PA, replacing the SW marker.
 *
 * DEV_MAP records the coherency type of the first locked dev_granule
 * in @coh_type; subsequent iterations reject mismatches so the entire
 * block is backed by a single dev memory region. DATA_MAP does not use
 * @coh_type.
 *
 * The RD address is cached so the continue handler can re-acquire the
 * RD granule and copy the S2 context instead of carrying a pointer
 * into an unmapped RD buffer.
 */
struct sro_map_ctx {
	struct granule *g_llt;		/* Leaf RTT pinned across yields */
	unsigned long rd_addr;		/* RD address for continue */
	unsigned long pa;		/* Block-aligned target PA */
	unsigned long ipa;		/* IPA the block maps to */
	unsigned long init_base;	/* Base IPA from the entry call */
	unsigned long pending_off;	/* Next byte offset to drain */
	unsigned long ret_err;		/* Terminal error after rollback */
	unsigned long index;		/* Slot index inside @g_llt */
	long level;			/* Block level the map runs at */
	enum dev_coh_type coh_type;	/* DEV_MAP coherency type */
	bool rollback;			/* Rollback in progress */
};

struct sro_context {
	/* State of this context */
	enum sro_state state;

	/* Initiating RMI command */
	unsigned long init_command;

	/* SRO Address List for the ongoing operation */
	struct addr_list addr_list;

	/* Whether the command can be cancelled */
	bool can_cancel;

	/* Whether the donated memory needs to be contiguous */
	bool is_contig;

	/* The state of the memory associated with donate or reclaim */
	unsigned long mem_state;

	/* FID of the expected SRO RMI that should be invoked */
	unsigned long expected_fid;

	/*
	 * Amount of memory that the handle needs to transfer.
	 * This is setup by the ongoing SRO command when the context is created
	 * and automatically updated by RMI_OP_MEM_DONATE/RMI_OP_MEM_RECLAIM
	 * to ensure we do not request larger transfers than needed.
	 */
	unsigned long transfer_req;

	/*
	 * Keep a copy of the RmiResult for the current reclaim operation
	 * in case the copy to NS memory fails and we need to retry.
	 */
	unsigned long reclaim_res;

	/* Previous expected FID for the reclaim operation */
	unsigned long prev_exp_fid;

	/* Flags passed by the caller for continue operation */
	unsigned long flags;

	/*
	 * Number of `ranges` allowed on the list if list_type is output
	 * Else the number of valid `ranges` on the list if list_type is input.
	 */
	unsigned long range_desc_count;

	/*
	 * Common state for aux granule transfer handling
	 * Only used for memory-transferring RMI Operations.
	 */
	struct sro_aux_op_ctx aux_op_ctx;

	/* Union with a structure for all the possible SRO commands */
	union {
		struct sro_rec_ctx rec_ctx;
		struct sro_smmu_ctx smmu_ctx;
		struct sro_pdev_ctx pdev_ctx;
		struct sro_unmap_ctx unmap_ctx;
		struct sro_map_ctx map_ctx;
	};
};

/*
 * Compute the total transfer size in bytes from an RmiOpMemDonateReq
 * descriptor: block_size(sz_field) * block_count.
 */
#define RMI_OP_DONATE_TRANSFER_SIZE(_desc)					\
	(XLAT_BLOCK_SIZE((int)(XLAT_TABLE_LEVEL_MAX -				\
			(int)EXTRACT(RMI_OP_DONATE_BLK_SIZE, (_desc)))) *	\
	 EXTRACT(RMI_OP_DONATE_BLK_COUNT, (_desc)))

/*
 * Encode an RmiOpMemDonateReq descriptor from a byte size, contiguity flag
 * and memory state.
 *
 * The function picks the largest block level (L0 > L1 > L2 > L3) for which
 * the size is an exact multiple of the block size and the resulting block
 * count fits in RMI_OP_DONATE_BLK_COUNT (14 bits, max 16383).
 *
 * Args:
 *  size_bytes - total donation size in bytes (must be a multiple of GRANULE_SIZE)
 *  contig     - RMI_OP_MEM_CONTIG or RMI_OP_MEM_NON_CONTIG
 *  state      - RMI_OP_MEM_DELEGATED or RMI_OP_MEM_UNDELEGATED
 *
 * Returns the encoded RmiOpMemDonateReq value.
 */
static inline unsigned long rmi_op_donate_req_encode(unsigned long size_bytes,
						     unsigned long contig,
						     unsigned long state)
{
	unsigned long max_count =
		(1UL << RMI_OP_DONATE_BLK_COUNT_WIDTH) - 1UL;

	for (int level = 0; level <= XLAT_TABLE_LEVEL_MAX; level++) {
		unsigned long blk_size = XLAT_BLOCK_SIZE(level);
		unsigned long blk_sz_enc =
			(unsigned long)(XLAT_TABLE_LEVEL_MAX - level);

		if ((size_bytes % blk_size) != 0UL) {
			continue;
		}

		unsigned long count = size_bytes / blk_size;

		if (count > max_count) {
			continue;
		}

		return (INPLACE(RMI_OP_DONATE_BLK_SIZE, blk_sz_enc) |
			INPLACE(RMI_OP_DONATE_BLK_COUNT, count) |
			INPLACE(RMI_OP_DONATE_MEM_CONTIG, contig) |
			INPLACE(RMI_OP_DONATE_MEM_STATE, state));
	}

	/* Should never be reached for valid inputs */
	assert(false);
	return 0UL;
}

/*
 * Returns the number of `ranges` entries in the list which can be utilized by the callback.
 */
static inline unsigned long sro_ctx_range_desc_count(const struct sro_context *sro)
{
	assert(sro != NULL);
	return sro->range_desc_count;
}

/*
 * Pool of SRO contexts managed by the sro_context library.
 */
/* cppcheck-suppress misra-c2012-2.4 */
struct sro_ctx_pool {
	/* Whether the pool has been initialized */
	bool init;

	/* Number of contexts in the pool */
	unsigned long ctx_count;

	/* Pointer to the array of SRO contexts */
	struct sro_context *ctxs;
};

/*
 * Per_cpu reference to command context that is currently used by the CPU.
 */
/* cppcheck-suppress misra-c2012-2.4 */
struct sro_cpu_ctx_ref {
	/* NULL if no SRO context is assigned to the CPU */
	struct sro_context *ctx;

	/* The unique identifier of a CPU' SRO context */
	unsigned int op_handler;
};

/*
 * Reserve an SRO context for a given command.
 *
 * Args:
 *	- command: Command to associate to the SRO context.
 *	- xfer: The amount of memory that will be transferred by the
 *		ongoing operation.
 *	- can_cancel: Whether the command can be canceled.
 *	- is_contig: Whether the requested memory is contiguous or not.
 *	- expected_fid: FID of the first expected SRO RMI operation.
 *
 * Return:
 *	- One of the following return codes:
 *		- RMI_BLOCKED: All SRO contexts are sealed.
 *		- RMI_BUSY: Some SRO contexts are reserved and the rest are
 *			    sealed.
 *		- RMI_SUCCESS: An SRO context has been assigned to the
 *			       current CPU.
 */
unsigned long sro_ctx_reserve(unsigned long command, unsigned long xfer,
			      bool can_cancel, bool is_contig,
			      unsigned long expected_fid);

/*
 * Release the SRO currently in use by the calling CPU.
 */
void sro_ctx_release(void);

/*
 * Seal an SRO context upon exiting to Host.
 */
unsigned int sro_ctx_seal(void);

/*
 * Locate a given SRO op handle and assign it to the current CPU.
 *
 * Returns true if the SRO op handle is found and not sealed, false otherwise.
 */
bool sro_ctx_find(unsigned long op_handle);

/*
 * Return a pointer to the SRO context currently assigned to the calling CPU.
 */
struct sro_context *my_sro_ctx(void);

/*
 * Return the global pool index (handle) of the SRO context currently
 * assigned to the calling CPU. Stable across an IRQ-yield: matches the
 * value sro_ctx_seal() would return without changing context state.
 */
unsigned int sro_ctx_my_handle(void);

/*
 * Initialize the sro_context library.
 *
 * Args:
 *      - va: VA of the memory block allocated for the library.
 *      - sz: Size of the allocated memory block.
 */
void sro_ctx_init(uintptr_t va, size_t sz);

/*
 * ONLY FOR TEST PURPOSE.
 * Reset all SRO context state for use between persistent-mode fuzzing
 * iterations.  Frees per-CPU references and resets all pool contexts to FREE.
 */
void sro_ctx_reset(void);

/*
 * Helper macro that reads the `is_contig` flag of a given sro context
 * passed by reference and returns the contig RMI flag value to be used
 * on an rmiOpMemDonateReq type.
 */
#define SRO_CONTIG_FLAG(_sro)				\
	(((_sro)->is_contig) ? RMI_OP_MEM_CONTIG : RMI_OP_MEM_NON_CONTIG)

/*
 * Helper macro that reads the `can_cancel` flag of a given sro context
 * passed by reference and returns the can cancel RMI flag value to be used
 * on an rmiResultDataIncomplete type.
 */
#define SRO_CAN_CANCEL_FLAG(_sro)			\
	(((_sro)->can_cancel) ? RMI_OP_CAN_CANCEL : RMI_OP_CANNOT_CANCEL)

#endif /* SRO_CONTEXT_H */
