/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <debug.h>
#include <host_realm.h>
#include <host_rmi_wrappers.h>
#include <smc-rmi.h>
#include <status.h>
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
		mem_req = EXTRACT(RMI_OP_MEM_REQ, ret_status);

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

			if (delegate_range(base,
					   base + num_granules * GRANULE_SIZE)
								!= 0) {
				ERROR("SRO: delegate failed\n");
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
						RMI_OP_MEM_DELEGATED);
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
							RMI_OP_MEM_DELEGATED);
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
