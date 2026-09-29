/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <arch_features.h>
#include <arch_helpers.h>
#include <assert.h>
#include <entropy.h>
#include <granule.h>
#include <memory.h>
#include <stddef.h>
#include <utils_def.h>

void granule_memzero_mapped(void *buf)
{
	unsigned long dczid_el0 = read_dczid_el0();
	uintptr_t addr = (uintptr_t)buf;
	unsigned int log2_size;
	unsigned int block_size;
	unsigned int cnt;

	/* Check that use of DC ZVA instructions is permitted */
	assert((dczid_el0 & DCZID_EL0_DZP_BIT) == 0UL);

	/*
	 * Log2 of the block size in bytes.
	 * The maximum size supported is 2KB, indicated by DCZID_EL0.BS
	 * value 0b1001 (512 words).
	 */
	log2_size = (unsigned int)EXTRACT(DCZID_EL0_BS, dczid_el0) + 2U;
	block_size = U(1) << log2_size;

	/* Number of iterations */
	cnt = U(1) << (GRANULE_SHIFT - log2_size);

	for (unsigned int i = 0U; i < cnt; i++) {
		dczva(addr);
		addr += block_size;
	}

	dsb(ish);
}

/*
 * For this sanitize method, we write a sequence of incrementing numbers to
 * the target granule, starting from a randomly chosen global seed. After the
 * operation, the global seed is incremented by the total number of values
 * written. Concurrency or atomicity of the global seed's read/update is not
 * a concern, as we do not require other CPUs to observe a consistent value
 * - any global seed value as a starting point is sufficient for scrubbing
 * purposes.
 */

# define WORDS_PER_PAGE (GRANULE_SIZE / sizeof(uint64_t))

void granule_sanitize_1_mapped(void *buf)
{
	static uint64_t global_scrub_seed;
	uint64_t *p = (uint64_t *)buf;

	/* cppcheck-suppress misra-c2012-17.3 */
	if (SCA_READ64(&global_scrub_seed) == 0UL) {
		/*
		 * Initialize the seed with a random value if not initialized
		 * or the value is 0.
		 */
		while (!(arch_collect_entropy(&global_scrub_seed))) {
		}
	}

	uint64_t local_seed = atomic_load_add_64(&global_scrub_seed, WORDS_PER_PAGE);

	for (size_t i = 0; i < WORDS_PER_PAGE; i++) {
		p[i] = local_seed;
		local_seed++;
	}
}

void granule_sanitize_mapped(void *buf)
{
	/* Zero the buffer */
	granule_memzero_mapped(buf);
}

void granule_dcci_poe_range(unsigned long addr, unsigned long size)
{
	unsigned long ctr_el0 = read_ctr_el0();
	unsigned int log2_size;
	unsigned int line_size;
	unsigned long cnt;

	assert(GRANULE_ALIGNED(addr));
	assert(GRANULE_ALIGNED(size));

	/* cppcheck-suppress knownConditionTrueFalse */
	if (!is_feat_mec_present()) {
		return;
	}

	/* Log2 of the line size in bytes */
	log2_size = (unsigned int)EXTRACT(CTR_EL0_DminLine, ctr_el0) + 2U;
	line_size = U(1) << log2_size;

	/* Number of iterations */
	cnt = size >> log2_size;

	for (unsigned long i = 0UL; i < cnt; i++) {
		/*
		 * DC CIPAE: Data or unified Cache line Clean and Invalidate
		 * by PA to PoE (Point of Encryption).
		 */
		dccipae(addr);
		addr += line_size;
	}

	dsb(ish);
}

/* Perform PoE cache maintenance for the physical Granule represented by @g. */
void granule_dcci_poe(struct granule *g)
{
	assert(g != NULL);
	granule_dcci_poe_range(tr_granule_addr(g), GRANULE_SIZE);
}
