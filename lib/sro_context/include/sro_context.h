/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef SRO_CONTEXT_H
#define SRO_CONTEXT_H

#include <addr_list.h>
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
 *   - L2 Stream Table descriptors
 *   - SMMUv3 Command queue
 *   - SMMUv3 Event queue
 */
#define SRO_PSMMU_RANGES	4U

/*
 * Data structure with the information to continue a REC related operation.
 */
struct sro_rec_ctx {
	/* Parameters for REC creation */
	unsigned long rd_addr;
	unsigned long rec_params_addr;
};

/*
 * Data structures with the information to continue a PSMMU related operation.
 */
struct smmuv3_dev;

struct sro_psmmu_range {
	/* Number of granules in block to donate during PSMMU activation */
	unsigned long requested;

	/* Contiguous flag */
	unsigned long contig;

	/*
	 * Base physical address of the donated range.
	 * Since each range is contiguous, the base PA is sufficient
	 * to reconstruct all individual granule PAs.
	 */
	uintptr_t base;
};

struct sro_psmmu_ctx {
	/* Pointer to the SMMUv3 driver structure */
	struct smmuv3_dev *smmu_ptr;

	/* SID */
	unsigned long sid;

	/* Index of the callback to invoke */
	unsigned int cb_id;

	/* Index of the range to donate in psmmu_range[] */
	unsigned int range_idx;

	/* Number of granules requested in the current range */
	unsigned long requested;

	/* Number of granules donated or reclaimed in the current range */
	unsigned long transferred;

	/* Number of granules donated or reclaimed so far */
	unsigned long total_transferred;

	/* Donation ranges */
	struct sro_psmmu_range psmmu_range[SRO_PSMMU_RANGES];

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
		struct sro_psmmu_ctx psmmu_ctx;
		struct sro_pdev_ctx pdev_ctx;
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
