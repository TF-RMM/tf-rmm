/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <assert.h>
#include <host_rmi_wrappers.h>
#include <host_utils.h>
#include <status.h>
#include <string.h>
#include <test_helpers.h>
#include <test_private.h>
#include <xlat_defs.h>

static unsigned int active_smmus;
static uintptr_t ns_buf;
static unsigned int first_smmu_granule = HOST_NR_GRANULES;

/*
 * Reserve aligned NS memory at the top of the host pool for PSMMU setup.
 * @size must be a nonzero power-of-two multiple of GRANULE_SIZE. Shared
 * startup calls this after resetting metadata, before any test allocation.
 * Tests can reset their allocator or allocate directly by granule index, so
 * these long-lived donations cannot use the ordinary test allocation cursor.
 */
static uintptr_t reserve_smmu_memory(size_t size)
{
	uintptr_t pool_base = host_util_get_granule_base();
	uintptr_t top = pool_base + (uintptr_t)first_smmu_granule * GRANULE_SIZE;
	uintptr_t base;

	assert(size <= (uintptr_t)first_smmu_granule * GRANULE_SIZE);
	base = round_down(top - size, size);

	assert(base > pool_base);
	first_smmu_granule = (unsigned int)((base - pool_base) / GRANULE_SIZE);
	return base;
}

/* Delegate a reserved NS range through RMI; the caller must hold no locks. */
static void delegate_smmu_memory(uintptr_t base, size_t size)
{
	uintptr_t top = base + size;
	struct smc_result res = {0};

	while (base < top) {
		host_rmi_granule_range_delegate((void *)base, (void *)top, &res);
		assert(res.x[0] == RMI_SUCCESS);
		assert((res.x[1] > base) && (res.x[1] <= top));
		base = res.x[1];
	}
}

/* Undelegate reclaimed PSMMU backing through RMI; hold no granule locks. */
static void undelegate_smmu_memory(uintptr_t base, size_t size)
{
	uintptr_t top = base + size;
	struct smc_result res = {0};

	while (base < top) {
		host_rmi_granule_range_undelegate((void *)base, (void *)top, &res);
		assert(res.x[0] == RMI_SUCCESS);
		assert((res.x[1] > base) && (res.x[1] <= top));
		base = res.x[1];
	}
}

/* Activate one host PSMMU and complete its memory donation SRO. */
static void activate_smmu(unsigned int idx)
{
	struct smc_result res = {0};
	unsigned long psmmu_ptr = host_util_get_smmu_ns_base(idx);
	unsigned long handle, donate_req;
	unsigned long *addr_list = (unsigned long *)ns_buf;

	assert(psmmu_ptr != 0UL);

	/* Reuse the shared NS page after activation consumes its parameters. */
	(void)memset((void *)ns_buf, 0, GRANULE_SIZE);
	host_rmi_psmmu_activate(psmmu_ptr, (void *)ns_buf,
				&handle, &donate_req, &res);
	assert(unpack_return_code(res.x[0]).status == RMI_INCOMPLETE);

	while (EXTRACT(RMI_OP_MEM_REQ, res.x[0]) == RMI_OP_MEM_REQ_DONATE) {
		unsigned long block_size = EXTRACT(RMI_OP_DONATE_BLK_SIZE, donate_req);
		unsigned long count = EXTRACT(RMI_OP_DONATE_BLK_COUNT, donate_req);
		unsigned long size = count * XLAT_BLOCK_SIZE(
					(long)XLAT_TABLE_LEVEL_MAX - (long)block_size);
		uintptr_t base = reserve_smmu_memory(size);
		unsigned long consumed;

		assert(EXTRACT(RMI_OP_DONATE_MEM_CONTIG, donate_req) == RMI_OP_MEM_CONTIG);
		delegate_smmu_memory(base, size);
		addr_list[0] = INPLACE(RMI_ADDR_RDESC_4K_SZ, block_size) |
			       INPLACE(RMI_ADDR_RDESC_4K_CNT, count) |
			       INPLACE(RMI_ADDR_RDESC_4K_ADDR, base >> GRANULE_SHIFT) |
			       INPLACE(RMI_ADDR_RDESC_4K_ST, RMI_OP_MEM_DELEGATED);
		host_rmi_op_mem_donate(handle, addr_list, 1UL, &donate_req, &consumed, &res);
		assert(unpack_return_code(res.x[0]).status == RMI_INCOMPLETE);
		assert(consumed == size / GRANULE_SIZE);
	}
	assert(EXTRACT(RMI_OP_MEM_REQ, res.x[0]) == RMI_OP_MEM_REQ_NONE);
	host_rmi_op_continue(&handle, 0UL, &donate_req, &res);
	assert(res.x[0] == RMI_SUCCESS);
}

/*
 * Activate both host PSMMUs through RMI, including their memory donation SROs.
 * Shared startup must boot and activate RMM and reset granule metadata first.
 * Hold no locks and have no pending SRO; test allocators honor the reserved tail.
 */
void test_smmu_start(void)
{
	assert(active_smmus == 0U);
	ns_buf = reserve_smmu_memory(GRANULE_SIZE);

	for (unsigned int i = 0U; i < HOST_NR_SMMUS; i++) {
		activate_smmu(i);
		active_smmus++;
	}
}

/* Deactivate one PSMMU, reclaim its donated memory, and return it to NS. */
static void deactivate_smmu(unsigned int idx)
{
	struct smc_result res = {0};
	unsigned long *addr_list = (unsigned long *)ns_buf;
	unsigned long handle, donate_req;

	host_rmi_psmmu_deactivate(host_util_get_smmu_ns_base(idx), &res);
	assert(unpack_return_code(res.x[0]).status == RMI_INCOMPLETE);
	handle = res.x[1];
	while (EXTRACT(RMI_OP_MEM_REQ, res.x[0]) == RMI_OP_MEM_REQ_RECLAIM) {
		unsigned long entries;

		host_rmi_op_mem_reclaim(handle, addr_list,
					GRANULE_SIZE / sizeof(addr_list[0]), &entries, &res);
		assert(unpack_return_code(res.x[0]).status == RMI_INCOMPLETE);
		assert((entries > 0UL) && (entries <= GRANULE_SIZE / sizeof(addr_list[0])));
		/* The final batch also returns ownership of every listed range. */
		for (unsigned long i = 0UL; i < entries; i++) {
			unsigned long desc = addr_list[i];
			unsigned long block_size = EXTRACT(RMI_ADDR_RDESC_4K_SZ, desc);
			uintptr_t base = EXTRACT(RMI_ADDR_RDESC_4K_ADDR, desc) << GRANULE_SHIFT;
			unsigned long size = EXTRACT(RMI_ADDR_RDESC_4K_CNT, desc) *
				XLAT_BLOCK_SIZE((long)XLAT_TABLE_LEVEL_MAX - (long)block_size);

			assert(EXTRACT(RMI_ADDR_RDESC_4K_ST, desc) == RMI_OP_MEM_DELEGATED);
			undelegate_smmu_memory(base, size);
		}
	}
	assert(EXTRACT(RMI_OP_MEM_REQ, res.x[0]) == RMI_OP_MEM_REQ_NONE);
	host_rmi_op_continue(&handle, 0UL, &donate_req, &res);
	assert(res.x[0] == RMI_SUCCESS);
}

/*
 * Release both PSMMUs before shared startup resets their granule metadata.
 * Suite exit also releases the final fixture. Finish test SROs and release
 * locks first. Does nothing if the previous test did not request active SMMUs.
 */
void test_smmu_stop(void)
{
	while (active_smmus != 0U) {
		deactivate_smmu(active_smmus - 1U);
		active_smmus--;
	}

	ns_buf = 0UL;
	first_smmu_granule = HOST_NR_GRANULES;
}

/*
 * Exclude active PSMMU tables, queues and the shared NS descriptor page from
 * the pool available to tests. Both the shared allocator and tests allocating
 * directly by granule index use this limit, so neither can overwrite PSMMU
 * backing. The full pool becomes available after both PSMMUs are deactivated
 * and their donations have been reclaimed and undelegated.
 */
unsigned int test_smmu_granule_limit(void)
{
	return first_smmu_granule;
}
