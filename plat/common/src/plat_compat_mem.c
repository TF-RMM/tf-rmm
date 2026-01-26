/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <assert.h>
#include <debug.h>
#include <plat_compat_mem.h>
#include <rmm_el3_ifc.h>

static uintptr_t rmm_reserve_mem;
static size_t rmm_reserve_size;

static struct rmm_el3_compat_callbacks cbs;

/*  cppcheck-suppress misra-c2012-8.7 */
void plat_cmn_compat_reserve_mem_init(struct rmm_el3_compat_callbacks *cb,
		void *base_addr, size_t size)
{

	assert(cb != NULL);
	assert(base_addr != NULL);
	assert(size != 0UL);

	rmm_reserve_mem = (uintptr_t)base_addr;
	rmm_reserve_size = size;

	cbs.reserve_mem_cb = cb->reserve_mem_cb;

	/*
	 * Use the compat callback mechanism only if RMM_EL3_COMPAT_RESERVE_MEM
	 * is defined. The fake_host layer does not need it.
	 */
#ifdef RMM_EL3_COMPAT_RESERVE_MEM
	rmm_el3_ifc_set_compat_callbacks(cb);
#endif
}

static char *reserve_memory(size_t size, unsigned long alignment)
{
	static uintptr_t cur_base_addr;
	char *ret;
	uintptr_t res_mem;

	assert((alignment >= GRANULE_SIZE) && IS_POWER_OF_TWO(alignment));
	assert((size != 0UL) && GRANULE_ALIGNED(size));

	if (cur_base_addr == 0UL) {
		cur_base_addr = rmm_reserve_mem;
	}

	/* cppcheck-suppress misra-c2012-17.3 */
	ret = (char *)round_up(cur_base_addr, alignment);
	cur_base_addr = (uintptr_t)ret + size;

	res_mem = cur_base_addr - rmm_reserve_mem;
	if (res_mem > rmm_reserve_size) {
		ERROR("Reservation for %lu pages > remaining %lu pages\n",
			size/GRANULE_SIZE,
			(rmm_reserve_size - res_mem)/GRANULE_SIZE);
		return NULL;
	}

	INFO("Reserved %lu pages. Remaining: %lu pages\n",
			size/GRANULE_SIZE,
			(rmm_reserve_size - res_mem)/GRANULE_SIZE);

	return ret;
}

/*
 * Platform compatibility function to reserve memory for RMM when
 * RMM_EL3_COMPAT_RESERVE_MEM is defined.
 */
/*  cppcheck-suppress misra-c2012-8.7 */
int plat_compat_reserve_memory(size_t size, uint64_t *arg)
{
	uint64_t alignment = 1UL << EXTRACT(RESERVE_MEM_ALIGN, *arg);
	void *addr;

	addr = reserve_memory(size, alignment);

	if (addr == NULL) {
		return E_RMM_NOMEM;
	}

	*arg = (uintptr_t)addr;

	return 0;
}
