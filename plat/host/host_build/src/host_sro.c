/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <assert.h>
#include <debug.h>
#include <host_realm.h>
#include <host_rmi_wrappers.h>
#include <smc-rmi.h>
#include <status.h>
#include <stdbool.h>
#include <string.h>
#include <xlat_defs.h>

#define IS_RMI_RESULT_SUCCESS(_r)	((_r).x[0] == RMI_SUCCESS)

void *allocate_granule(unsigned int num_granules);
void *allocate_granule_aligned(unsigned int num_granules);

/*
 * Iteratively delegate a range of granules.
 * Returns 0 on success, -1 on failure.
 */
static int delegate_range(uintptr_t base, uintptr_t end)
{
	struct smc_result result;
	uintptr_t cur = base;

	while (cur < end) {
		host_rmi_granule_range_delegate((void *)cur, (void *)end,
						&result);
		if (!IS_RMI_RESULT_SUCCESS(result)) {
			return -1;
		}
		cur = (uintptr_t)result.x[1];
	}

	return 0;
}

/*
 * Iteratively undelegate [@base, @end) after an SRO returns delegated memory.
 * Return zero when the whole range is NS, or -1 if an RMI call fails.
 */
static int undelegate_range(uintptr_t base, uintptr_t end)
{
	struct smc_result result;
	uintptr_t cur = base;

	while (cur < end) {
		unsigned long handle;
		unsigned long status;

		host_rmi_granule_range_undelegate((void *)cur, (void *)end,
						  &result);
		status = unpack_return_code(result.x[0]).status;
		handle = result.x[1];
		while (status == RMI_INCOMPLETE) {
			unsigned long donate_req = 0UL;
			unsigned long wrapper_handle = handle;

			if (EXTRACT(RMI_OP_MEM_REQ, result.x[0]) !=
			    RMI_OP_MEM_REQ_NONE) {
				return -1;
			}
			host_rmi_op_continue(&wrapper_handle, 0UL, &donate_req,
					     &result);
			status = unpack_return_code(result.x[0]).status;
		}
		if (!IS_RMI_RESULT_SUCCESS(result)) {
			return -1;
		}
		cur = (uintptr_t)result.x[1];
	}

	return 0;
}

/*
 * Convert each delegated range in the reclaimed descriptor list back to NS
 * memory. Undelegated entries need no transition. Return zero on success or
 * -1 for an invalid donor state or a failed undelegation.
 */
static int host_sro_release_reclaimed(const uintptr_t *addr_list,
				      unsigned long list_count)
{
	assert(addr_list != NULL);
	for (unsigned long i = 0UL; i < list_count; i++) {
		unsigned long desc = addr_list[i];
		unsigned long state = EXTRACT(RMI_ADDR_RDESC_4K_ST, desc);

		if (state == RMI_OP_MEM_DELEGATED) {
			unsigned long level = XLAT_TABLE_LEVEL_MAX -
				EXTRACT(RMI_ADDR_RDESC_4K_SZ, desc);
			unsigned long size = XLAT_BLOCK_SIZE(level) *
				EXTRACT(RMI_ADDR_RDESC_4K_CNT, desc);
			uintptr_t base = EXTRACT(RMI_ADDR_RDESC_4K_ADDR, desc) <<
					 GRANULE_SHIFT;

			if (undelegate_range(base, base + size) != 0) {
				return -1;
			}
		} else if (state != RMI_OP_MEM_UNDELEGATED) {
			return -1;
		}
	}

	return 0;
}

/* Return whether TRACKING_GET reports all of [@base, @end) as fine tracked. */
static bool host_sro_range_is_fine(uintptr_t base, uintptr_t end)
{
	struct smc_result result;

	host_rmi_granule_tracking_get(base, end, &result);
	return IS_RMI_RESULT_SUCCESS(result) &&
	       (result.x[2] == RMI_TRACKING_FINE) &&
	       (result.x[3] == end);
}

/*
 * Prepare a donated range in one of the architected donor states. A
 * conditional request accepts either state, so prefer delegated memory once
 * its granules are fine tracked; otherwise leave it NS for a self-describing
 * tracking-metadata donation. Return zero with @donor_state selected, or -1
 * for an invalid requested state or a failed delegation.
 */
static int host_sro_prepare_donation(uintptr_t base, uintptr_t end,
				     unsigned long requested_state,
				     unsigned long *donor_state)
{
	bool delegate;

	assert(donor_state != NULL);
	switch (requested_state) {
	case RMI_OP_MEM_DELEGATED:
		delegate = true;
		*donor_state = RMI_OP_MEM_DELEGATED;
		break;
	case RMI_OP_MEM_UNDELEGATED:
		delegate = false;
		*donor_state = RMI_OP_MEM_UNDELEGATED;
		break;
	case RMI_OP_MEM_CONDITIONAL:
		delegate = host_sro_range_is_fine(base, end);
		*donor_state = delegate ? RMI_OP_MEM_DELEGATED :
						RMI_OP_MEM_UNDELEGATED;
		break;
	default:
		return -1;
	}

	if (delegate && (delegate_range(base, end) != 0)) {
		return -1;
	}

	return 0;
}

/*
 * Drive a generic SRO (Split RMI Operation) flow to completion.
 *
 * Handles:
 *  - MEM_REQ_DONATE: Allocates granules (aligned if contiguous), delegates,
 *    builds the address descriptor list, and calls OP_MEM_DONATE.
 *  - MEM_REQ_RECLAIM: Issues OP_MEM_RECLAIM to acknowledge returned memory.
 *  - MEM_REQ_NONE: Issues OP_CONTINUE to finalize the operation.
 *
 * Parameters:
 *  - handle: SRO operation handle (from x[1] of the initiating RMI call)
 *  - ret_status: Full return code (x[0] of the initiating RMI call)
 *  - donate_req: Donation requirements (x[2] of the initiating RMI call)
 *
 * Returns 0 on success, -1 on failure.
 */
int host_sro_drive(unsigned long handle, unsigned long ret_status,
		   unsigned long donate_req)
{
	struct smc_result result;
	unsigned long mem_req;
	unsigned long consumed_entries;
	uintptr_t *addr_list;

	addr_list = (uintptr_t *)allocate_granule(1U);

	while (unpack_return_code(ret_status).status == RMI_INCOMPLETE) {
		return_code_t return_code = unpack_return_code(ret_status);

		mem_req = return_code.data.incomplete.mem;

		if (mem_req == RMI_OP_MEM_REQ_NONE) {
			host_rmi_op_continue(&handle, 0UL, &donate_req,
					     &result);
			ret_status = result.x[0];
			continue;
		}

		if (mem_req == RMI_OP_MEM_REQ_RECLAIM) {
			host_rmi_op_mem_reclaim(handle, addr_list,
						GRANULE_SIZE / sizeof(uintptr_t),
						&consumed_entries, &result);
			/* Every returned batch is Host-owned, including the last. */
			if ((consumed_entries != 0UL) &&
			    (host_sro_release_reclaimed(addr_list,
						consumed_entries) != 0)) {
				ERROR("SRO: failed to release reclaimed memory\n");
				return -1;
			}
			ret_status = result.x[0];
			continue;
		}

		if (mem_req != RMI_OP_MEM_REQ_DONATE) {
			ERROR("SRO: unexpected mem_req %lu\n", mem_req);
			return -1;
		}

		/* Handle donate request */
		{
			unsigned long blk_sz = EXTRACT(RMI_OP_DONATE_BLK_SIZE,
						       donate_req);
			unsigned long blk_count = EXTRACT(
						RMI_OP_DONATE_BLK_COUNT,
						donate_req);
			unsigned long contig = EXTRACT(
						RMI_OP_DONATE_MEM_CONTIG,
						donate_req);
			unsigned long requested_state = EXTRACT(
						RMI_OP_DONATE_MEM_STATE,
						donate_req);
			unsigned long donor_state;
			unsigned long blk_size_bytes =
				XLAT_BLOCK_SIZE((int)XLAT_TABLE_LEVEL_MAX -
						(int)blk_sz);
			unsigned long num_granules =
				(blk_count * blk_size_bytes) / GRANULE_SIZE;
			unsigned long list_count;
			uintptr_t base;

			if (contig == RMI_OP_MEM_CONTIG) {
				base = (uintptr_t)allocate_granule_aligned(
						(unsigned int)num_granules);
			} else {
				base = (uintptr_t)allocate_granule(
						(unsigned int)num_granules);
			}

			if (host_sro_prepare_donation(base,
					base + num_granules * GRANULE_SIZE,
					requested_state, &donor_state) != 0) {
				ERROR("SRO: failed to prepare donated memory\n");
				return -1;
			}

			if (contig == RMI_OP_MEM_CONTIG) {
				addr_list[0] =
					INPLACE(RMI_ADDR_RDESC_4K_SZ, blk_sz) |
					INPLACE(RMI_ADDR_RDESC_4K_CNT,
						blk_count) |
					INPLACE(RMI_ADDR_RDESC_4K_ADDR,
						base >> GRANULE_SHIFT) |
					INPLACE(RMI_ADDR_RDESC_4K_ST,
						donor_state);
				list_count = 1UL;
			} else {
				for (unsigned long i = 0; i < num_granules;
				     i++) {
					addr_list[i] =
						INPLACE(RMI_ADDR_RDESC_4K_SZ,
							RMI_PAGE_L3) |
						INPLACE(RMI_ADDR_RDESC_4K_CNT,
							1UL) |
						INPLACE(RMI_ADDR_RDESC_4K_ADDR,
							(base + i *
							 GRANULE_SIZE) >>
							GRANULE_SHIFT) |
						INPLACE(RMI_ADDR_RDESC_4K_ST,
							donor_state);
				}
				list_count = num_granules;
			}

			host_rmi_op_mem_donate(handle, addr_list, list_count,
					       &donate_req, &consumed_entries,
					       &result);

			ret_status = result.x[0];
			if (unpack_return_code(ret_status).status !=
							RMI_INCOMPLETE) {
				ERROR("SRO: donate returned 0x%lx\n",
				      ret_status);
				return -1;
			}
		}
	}

	if (ret_status != RMI_SUCCESS) {
		ERROR("SRO: final status 0x%lx\n", ret_status);
		return -1;
	}

	return 0;
}
