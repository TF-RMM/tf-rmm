/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include "granule.h"
#include "host_defs.h"
#include "host_utils.h"
#include "measurement.h"
#include "s2tt.h"
#include "status.h"
#include "string.h"
#include "tb_common.h"
#include "tb_granules.h"
#include "utils_def.h"

/* This array holds information on the injected granule's status in the GPT. */
static enum granule_gpt granule_gpt_array[RMM_MAX_GRANULES];

/* Declare a nondet function for registers information. */
struct tb_regs nondet_tb_regs(void);

struct tb_regs __tb_arb_regs(void)
{
	return nondet_tb_regs();
}

bool ResultEqual_2(unsigned int code, unsigned int expected)
{
	return code == expected;
}

/* TODO */
bool ResultEqual_3(unsigned int code, unsigned int expected, unsigned int level)
{
	return true;
}

uint64_t Zeros(void)
{
	return UINT64_C(0);
}

bool __tb_arb_bool(void)
{
	return nondet_bool();
}

void __tb_lock_invariant(struct tb_lock_status *lock_status)
{
	/* TODO */
}

struct tb_lock_status __tb_lock_status(void)
{
	struct tb_lock_status r = {0UL};
	return r;
}

extern struct granule granules[RMM_MAX_GRANULES];
bool used_granules_buffer[HOST_NR_GRANULES] = { 0 };

bool valid_pa(uint64_t addr)
{
	/*
	 * NOTE: the explicit pointer to integer type cast is necessary, as CBMC
	 * check fails without it.
	 */
	if (GRANULE_ALIGNED(addr) && (uint64_t)granules_buffer <= addr &&
		addr < (uint64_t)granules_buffer + sizeof(granules_buffer)) {
		/*
		 * Keep these assserts for sanitary check, there was situation
		 * these asserts fail possibly due to CBMC dislike type
		 * conversion between number and pointer
		 */
		ASSERT(GRANULE_ALIGNED(addr), "internal: `_valid_pa`, addr in alignment");
		ASSERT(addr >= (uint64_t)granules_buffer,
			"internal: `_valid_pa`, addr in lower range");
		ASSERT(addr < (uint64_t)granules_buffer + sizeof(granules_buffer),
			"internal: `_valid_pa`, addr in upper range");
		return true;
	}
	return false;
}

struct granule *pa_to_granule_metadata_ptr(uint64_t addr)
{
	uint64_t idx = (addr - (uint64_t)granules_buffer)/GRANULE_SIZE;

	__ASSERT(idx >= 0, "internal: `_pa_to_granule_metadata_ptr`, addr is in lower range");
	__ASSERT(idx < RMM_MAX_GRANULES,
		"internal: `_pa_to_granule_metadata_ptr`, addr is in upper range");

	return &granules[idx];
}

void *granule_metadata_ptr_to_buffer_ptr(struct granule *g_ptr)
{
	if (!valid_granule_metadata_ptr(g_ptr)) {
		return NULL;
	}
	return granules_buffer + (g_ptr - granules) * GRANULE_SIZE;
}

uint64_t granule_metadata_ptr_to_pa(struct granule *g_ptr)
{
	return (uint64_t)granules_buffer + (g_ptr - granules) * GRANULE_SIZE;
}

void *pa_to_granule_buffer_ptr(uint64_t addr)
{
	__ASSERT((unsigned char *)addr - granules_buffer >= 0,
		"internal: `_pa_to_granule_buffer_ptr`, addr is in lower range");
	/*
	 * CBMC has difficulty doing an integer->object mapping, when the
	 * integer is the address of the expected object, and the integer is not
	 * derived from a pointer.
	 * So instead of simply returning addr we need to tell CBMC that the
	 * object we are looking for is in the `granules_buffer` array, at an
	 * offset. To calculate the offset we can use `addr`, and the address of
	 * `granules_buffer`.
	 * For details see https://github.com/diffblue/cbmc/issues/8103
	 */
	return (void *)granules_buffer + ((unsigned char *)addr - granules_buffer);
}

bool valid_granule_metadata_ptr(struct granule *p)
{
	return p >= granules
		&& p < granules + RMM_MAX_GRANULES;
}

/*
 * Return the first index of `number` of unused continuous indice to both
 * `granules` and `granules_buffer` arrays.
 */
size_t next_index(void)
{
	size_t index = nondet_size_t();

	__ASSUME(unused_index(index));
	if (!unused_index(index)) {
		return -1;
	}

	return index;
}

bool unused_index(size_t index)
{
	if (index < HOST_NR_GRANULES && !used_granules_buffer[index]) {
		return true;
	}
	return false;
}

void init_pa_page(const void *content, size_t size)
{
	unsigned long index = next_index();
	unsigned long offset = index * GRANULE_SIZE;

	(void)memcpy(granules_buffer + offset, content, size);
	used_granules_buffer[index] = true;
}

struct granule *inject_granule_at(const struct granule *granule_metadata,
				  const void *src_page,
				  size_t src_size,
				  size_t index)
{
	size_t offset = index * GRANULE_SIZE;

	if (granule_unlocked_state((struct granule *)granule_metadata) ==
							GRANULE_STATE_NS) {
		/* initialise the granules as either secure or non-secure */
		granule_gpt_array[index] = nondet_bool() ? GPT_SECURE : GPT_NS;
	} else {
		granule_gpt_array[index] = GPT_REALM;
	}

	granules[index] = *granule_metadata;
	(void)memcpy(granules_buffer + offset, src_page, src_size);
	used_granules_buffer[index] = true;
	return &granules[index];
}

struct granule *inject_granule(const struct granule *granule_metadata,
			       const void *src_page,
			       size_t src_size)
{
	size_t index = next_index();

	return inject_granule_at(granule_metadata, src_page, src_size, index);
}

enum granule_gpt get_granule_gpt(uint64_t addr)
{
	uint64_t idx = (addr - (uint64_t)granules_buffer)/GRANULE_SIZE;

	return granule_gpt_array[idx];
}

void set_granule_gpt(uint64_t addr, enum granule_gpt granule_gpt)
{
	uint64_t idx = (addr - (uint64_t)granules_buffer)/GRANULE_SIZE;

	granule_gpt_array[idx] = granule_gpt;
}
