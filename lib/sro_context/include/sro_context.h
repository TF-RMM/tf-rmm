/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef SRO_CONTEXT_H
#define SRO_CONTEXT_H

#include <limits.h>
#include <smc-rmi.h>
#include <smc.h>

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
 *   		    running CPU.
 *
 * Note that the library is agnostic to the actual content of the objects as
 * the content is very specific to each command (or, to a family of commands).
 */

/* Prototype of the handles to use for CONTINUE operations */
typedef void(*sro_handle_cb)(struct smc_args *arg, struct smc_result *res);

/*
 * Maximum number of entries we allow the donate/reclaim address list to have.
 * Note that this implementation does not allow the list to cross
 * granule, so in that case, the operation will just return INCOMPLETE.
 */
#define SRO_MAX_LIST_ENTRIES		(GRANULE_SIZE / sizeof(unsigned long))

/*
 * As the SRO contexts may remain allocated when RMI handler exits
 * to host, this should be considerable larger than CPU count.
 */
#define SRO_CTX_PER_CPU		(10UL)

/* Macro to define an invalid RmiResult value */
#define SRO_INVALID_RESULT	(ULONG_MAX)

/*
 * Total allocation size required for the sro_ctx_pool:
 * the pool header followed immediately by the sro_context array.
 */
#define SRO_CTX_POOL_SIZE \
	(sizeof(struct sro_ctx_pool) + \
	 (sizeof(struct sro_context) * (MAX_CPUS * SRO_CTX_PER_CPU)))

/*
 * Data structure with the information to continue a REC related operation.
 */
struct sro_rec_ctx {
	/* Index of the callback to invoke */
	unsigned int cb_id;

	/* Parameters for REC creation */
	unsigned long rd_addr;
	unsigned long rec_addr;
	unsigned long rec_params_addr;

	/* Error condition in case REC_CREATE fails */
	unsigned long ret_err;

	/* List of PAs for the auxiliary granules donated by the host */
	uintptr_t aux_granules_pa[MAX_REC_AUX_GRANULES];

	/* Number of granules requested */
	unsigned long requested_aux_granules;

	/* Number of granules donated or reclaimed so far */
	unsigned long total_transferred;
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

struct sro_context {
	/* State of this context */
	enum sro_state state;

	/* Initiating RMI command */
	unsigned long init_command;

	/* Whether the command can be cancelled */
	bool can_cancel;

	/* Whether the donated memory needs to be contiguous */
	bool is_contig;

	/* FID of the expected SRO RMI that should have been invoked */
	unsigned long expected_fid;

	/*
	 * Amount of memory that the handle needs to transfer.
	 * This is setup by the ongoing SRO command when the context is created
	 * and automatically updated by RMI_OP_MEM_DONATE/RMI_OP_MEM_RECLAIM
	 * to ensure we do not request larger transfers than needed.
	 */
	unsigned long transfer_req;

	/*
	 * Amount of memory being transfered by the RMI_OP_MEM_DONATE/RECLAIM.
	 * This takes into account all the entries on the current RMI Address List.
	 */
	unsigned long current_transfer;

	/*
	 * Stores a copy of the return arguments in case it needs to
	 * retry a command due to the incorrect SRO RMI command.
	 */
	struct smc_result prev_res;

	/* Buffer to temporarly store donate/request entries */
	unsigned long list_buffer[SRO_MAX_LIST_ENTRIES];

	/* Number of valid entries on list_buffer */
	unsigned long pend_entries;

	/*
	 * Keep a copy of the RmiResult for the current reclaim operation
	 * in case the copy to NS memory fails and we need to retry.
	 */
	unsigned long reclaim_res;

	/* Previous expected FID for the reclaim operation */
	unsigned long prev_exp_fid;

	/* Union with a structure for all the possible SRO commands */
	union{
		struct sro_rec_ctx rec_ctx;
	};
};

/*
 * Pool of SRO contexts managed by the sro_context library.
 */
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
struct cpu_sro_ctx {
	/* NULL if no SRO context is assigned to the CPU */
	struct sro_context *ctx;

	/* The unique identifier of a CPU' SRO context */
	unsigned int op_handler;
};

/*
 * Reserve an SRO context for a given command.
 *
 * Args:
 * 	- command: Command to associate to the SRO context.
 * 	- xfer: The amount of memory that will be transferred by the
 *		ongoing operation.
 * 	- can_cancel: Whether the command can be canceled.
 * 	- is_contig: Whether the requested memory is contiguous or not.
 *
 * Return:
 * 	- One of the following return codes:
 * 		- RMI_BLOCKED: All SRO contexts are sealed.
 * 		- RMI_BUSY: Some SRO contexts are reserved and the rest are
 * 			    sealed.
 * 		- RMI_SUCCESS: An SRO context has been assigned to the
 * 			       current CPU.
 */
unsigned long sro_ctx_reserve(unsigned long command, unsigned long xfer,
			      bool can_cancel, bool is_contig);

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
bool sro_ctx_find(unsigned int op_handle);

/*
 * Return a pointer to the SRO context currently assigned to the calling CPU.
 */
struct sro_context *my_sro_ctx(void);

/*
 * Configure the next expected command.
 *
 * Args:
 *	- fid: FID of the expected SRO RMI operation that must follow.
 *	       if the FID does not match the FID of the invoked SRO RMI
 *	       operation, the RMI will return the same values as the
 *	       previous one to try to retry.
 */
void sro_ctx_next_cmd(unsigned long fid);

/*
 * Initialize the sro_context library.
 *
 * Args:
 *      - va: VA of the memory block allocated for the library.
 *      - sz: Size of the allocated memory block.
 */
void sro_ctx_init(uintptr_t va, size_t sz);

/*
 * Heelper macro that reads the `is_contig` flag of a given sro context
 * passed by refrence and returns the contig RMI flag value to be used
 * on an rmiOpMemDonateReq type.
 */
#define SRO_CONTIG_FLAG(_sro)				\
	(((_sro)->is_contig) ? RMI_OP_MEM_CONTIG : RMI_OP_MEM_NON_CONTIG)

/*
 * Helper macro that reads the `can_cancel` flag of a given sro context
 * passed by refrence and returns the can cancel RMI flag value to be used
 * on an rmiResultDataIncomplete type.
 */
#define SRO_CAN_CANCEL_FLAG(_sro)			\
	(((_sro)->can_cancel) ? RMI_OP_CAN_CANCEL : RMI_OP_CANNOT_CANCEL)

#endif /* SRO_CONTEXT_H */
