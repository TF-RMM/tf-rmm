/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <assert.h>
#include <atomics.h>
#include <cpuid.h>
#include <debug.h>
#include <errno.h>
#include <mec.h>
#include <rmm_el3_ifc.h>

#define MECID_SYSTEM_OFFSET		(RESERVED_MECID_SYSTEM / BITS_PER_UL)

#define IS_PRIVATE_MECID_VALID(id)	(((id) >= MECID_PRIVATE_START) \
					&& ((id) <= mecid_max()))

/* Ensure all the reserved MECIDs and the shared MECID have offset 0 */
COMPILER_ASSERT(RESERVED_IDS + 1U < BITS_PER_UL);

/* All the reserved MECIDs plus the shared MECID have to be initialized */
#define MEC_RESERVE_INITALIZER		((1UL << (RESERVED_IDS + 1UL)) - 1UL)

static struct mec_state_s *g_mec_state;

static uint64_t mecid_pcpcu_refcnt[MAX_CPUS];

void _mecid_s1_get(unsigned int mecid)
{
	/* no acquire/release needed as this is a per-cpu only access variable */
	uint64_t old_val =  atomic_load_add_64(&mecid_pcpcu_refcnt[my_cpuid()], 1U);
	if (old_val == 0U) {
		assert(read_mecid_a1_el2() == RESERVED_MECID_SYSTEM);
		write_mecid_a1_el2((unsigned long)mecid);
		isb();
	} else {
		assert(read_mecid_a1_el2() == (unsigned long)mecid);
	}
}

void _mecid_s1_put(void)
{
	/* no acquire/release needed as this is a per-cpu only accessed variable */
	uint64_t old_val = atomic_load_add_64(&mecid_pcpcu_refcnt[my_cpuid()], (uint64_t)(-1));
	assert(old_val != 0U);
	assert(read_mecid_a1_el2() != RESERVED_MECID_SYSTEM);

	if (old_val == 1U) {
		write_mecid_a1_el2(RESERVED_MECID_SYSTEM);
		isb();
	}
}

unsigned int mecid_max(void)
{
	unsigned int mecid_count;

	assert(is_feat_mec_present());

	/*
	 * MECIDR_MECIDWIDTHM1 plus 1 is the MECID width in bits.
	 * So Max MECID is (2^MECID width) - 1.
	 */
	mecid_count = (unsigned int)1 << (EXTRACT(MECIDR_MECIDWIDTHM1,
						read_mecidr_el2()) + 1U);

	assert(mecid_count <= MEC_MAX_COUNT);
	return mecid_count - 1U;
}

/*
 * Atomically set a bit corresponding to mecid. Returns true if the
 * bit was not set previously, else returns false.
 */
static bool mec_reserve(unsigned int mecid)
{
	unsigned int offset, bit;

	assert(IS_PRIVATE_MECID_VALID(mecid));

	offset = mecid / BITS_PER_UL;
	bit = mecid % BITS_PER_UL;

	if (!atomic_bit_set_acquire_release_64(&g_mec_state->mec_reserved[offset],
						bit)) {
		/*
		 * Tweak the key associated with the MECID.
		 */
		(void)rmm_el3_ifc_mec_refresh((unsigned short)mecid, false);
		return true;
	}

	return false;
}

/*
 * Atomically clear a bit corresponding to mecid.
 */
static void mec_release(unsigned int mecid)
{
	unsigned int offset, bit;

	assert(IS_PRIVATE_MECID_VALID(mecid));

	offset = mecid / BITS_PER_UL;
	bit = mecid % BITS_PER_UL;

	/*
	 * Tweak the key associated with the MECID. This function
	 * is called before releasing the MECID.
	 */
	(void)rmm_el3_ifc_mec_refresh((unsigned short)mecid, true);
	atomic_bit_clear_release_64(&g_mec_state->mec_reserved[offset], bit);
}

/*
 * Assign a MECID for a particular Realm. Reserve
 * the MECID if it is not Shared. If Shared, increment
 * the use count.
 * Returns true if successful, else returns false.
 */
static bool mecid_reserve(unsigned int mecid)
{
	bool ret;

	/* cppcheck-suppress knownConditionTrueFalse */
	if (!is_feat_mec_present()) {
		return true;
	}

	if (mecid == MECID_SHARED) {
		/*
		 * If the MECID is shared, refresh the key tweak if
		 * the use count is 0 and increment the use count.
		 */
		spinlock_acquire(&g_mec_state->shared_mecid_spinlock);
		/* coverity[misra_c_2012_rule_14_3_violation:SUPPRESS] */
		if (g_mec_state->shared_mec_members < UINT64_MAX) {
			/* coverity[deadcode:SUPPRESS] */
			/* coverity[misra_c_2012_rule_14_3_violation:SUPPRESS] */
			if (g_mec_state->shared_mec_members == 0UL) {
				/* coverity[misra_c_2012_rule_14_3_violation:SUPPRESS] */
				(void)rmm_el3_ifc_mec_refresh(
					(unsigned short)MECID_SHARED,
					false);
			}
			g_mec_state->shared_mec_members++;
			ret = true;
		} else {
			ret = false;
		}
		spinlock_release(&g_mec_state->shared_mecid_spinlock);
		return ret;
	}

	if (!(IS_PRIVATE_MECID_VALID(mecid))) {
		return false;
	}

	assert(read_mecid_a1_el2() == RESERVED_MECID_SYSTEM);

	return mec_reserve(mecid);
}

/*
 * Unassign a MECID, typically called when Realm is destroyed.
 * Unreserve the MECID if it is not Shared else decrement
 * the use count.
 */
void mecid_free(unsigned int mecid)
{
	/* cppcheck-suppress knownConditionTrueFalse */
	if (!is_feat_mec_present()) {
		return;
	}

	if (mecid == MECID_SHARED) {
		/*
		 * If the MECID is shared, decrement the use count and
		 * refresh the key tweak once the count reaches 0.
		 */
		spinlock_acquire(&g_mec_state->shared_mecid_spinlock);
		assert(g_mec_state->shared_mec_members > 0U);
		g_mec_state->shared_mec_members--;
		if (g_mec_state->shared_mec_members == 0U) {
			(void)rmm_el3_ifc_mec_refresh(
				(unsigned short)MECID_SHARED, true);
		}
		spinlock_release(&g_mec_state->shared_mecid_spinlock);
		return;
	}

	/* The MECID is already validated during assign */
	assert(IS_PRIVATE_MECID_VALID(mecid));

	mec_release(mecid);
}

/*
 * Returns a starting position for allocation search by scanning all bitmap
 * words for the first free MECID.
 */
static unsigned int mecid_hint(void)
{
	assert(is_feat_mec_present());

	for (unsigned int i = 0U; i < MECID_ARRAY_SIZE; i++) {
		unsigned long word_val = g_mec_state->mec_reserved[i];

		if (word_val != ~0UL) {
			return (i * BITS_PER_UL) +
				(unsigned int)__builtin_ctzl(~word_val);
		}
	}

	return 0U;
}

/*
 * Allocates a free MECID from the available pool.
 * @is_shared: whether the MECID is to be allocated for shared
 *             or private use.
 * Returns:
 * - True, on success and sets mecid to the allocated value
 *   or FEAT_MEC is not present
 * - False, if no free MECID is available or invalid policy
 */
bool mecid_alloc(unsigned int *mecid, bool is_shared)
{
	unsigned int max_mecid;
	unsigned int private_mecid_count;
	unsigned int i;
	unsigned int start_hint;
	unsigned int hint;

	/* cppcheck-suppress knownConditionTrueFalse */
	if (!is_feat_mec_present()) {
		*mecid = RESERVED_MECID_SYSTEM;
		return true;
	}

	/* Handle policy-based allocation */
	if (is_shared) {
		if (mecid_reserve(MECID_SHARED)) {
			*mecid = MECID_SHARED;
			return true;
		}
		return false;
	}

	/* Allocate new MECID for private policy */
	max_mecid = mecid_max();

	/* Get hint for where to start searching */
	start_hint = mecid_hint();

	if ((start_hint == 0U) || (start_hint > max_mecid)) {
		start_hint = MECID_PRIVATE_START;
	}

	/*
	 * Available private MECIDs start after the reserved MECIDs and the
	 * shared MECID.
	 */
	private_mecid_count = mecid_private_count();

	/* Adjust start_hint to be relative to private MECID start */
	start_hint -= MECID_PRIVATE_START;

	/*
	 * Search for a free MECID in the bitmap circularly, starting from
	 * the hint and only through the private MECIDs.
	 */
	for (i = 0U; i < private_mecid_count; i++) {
		hint = MECID_PRIVATE_START + ((i + start_hint) % private_mecid_count);
		if (mecid_reserve(hint)) {
			*mecid = hint;
			return true;
		}
	}

	return false;
}

/*
 * Check if VMECID is private. This function will be invoked while REC is running.
 */
bool mec_is_realm_mecid_s2_pvt(void)
{
	/* cppcheck-suppress knownConditionTrueFalse */
	if (!is_feat_mec_present()) {
		return false;
	}

	unsigned int mecid = (unsigned int)read_vmecid_p_el2();
	assert(mecid != RESERVED_MECID_SYSTEM);

	return (mecid != MECID_SHARED);
}

#if (RMM_MEM_SCRUB_METHOD == 1)
# define SCRUB_METHOD_STRING "RMM_MEM_SCRUB_METHOD 1 is selected.\n"
#elif (RMM_MEM_SCRUB_METHOD == 2)
# define SCRUB_METHOD_STRING "RMM_MEM_SCRUB_METHOD 2 is selected.\n"
#else
# define SCRUB_METHOD_STRING "RMM_MEM_SCRUB_METHOD is default.\n"
#endif

/*
 * RMM is loaded by EL3 with MEC disabled. This means that RMM must use
 * a MECID of 0 for its own execution and Data.
 */
void mec_init_mmu(void)
{
	uint16_t mecid;

	/*
	 * Since this function is enabled with MMU disabled, it should not
	 * update any global data.
	 */
	assert(!is_mmu_enabled());

	/* cppcheck-suppress knownConditionTrueFalse */
	if ((!is_feat_sctlr2x_present()) || (!is_feat_mec_present())) {
#if (RMM_MEM_SCRUB_METHOD == 2)
		WARN("RMM_MEM_SCRUB_METHOD=2 is set but FEAT_MEC is not present.\n");
#endif
		return;
	}
#if (RMM_MEM_SCRUB_METHOD == 2)
	(void)rmm_el3_ifc_mec_refresh(RESERVED_MECID_SCRUB, false);
#endif
	/* Initialize the default shared MECID */
	(void)rmm_el3_ifc_mec_refresh(MECID_SHARED, false);

	mecid = RESERVED_MECID_SYSTEM;

	/* MECID_* reset to UNKNOWN values */
	write_mecid_p0_el2(mecid);
	write_mecid_p1_el2(mecid);
	write_mecid_a0_el2(mecid);
	write_mecid_a1_el2(mecid);
	write_vmecid_p_el2(mecid);
	write_vmecid_a_el2(mecid);
	isb();

	write_sctlr2_el2(read_sctlr2_el2() | SCTLR2_ELx_EMEC_BIT);
}

/*
 * Initialize MEC state values to default/reset state.
 */
static void mec_state_init_values(void)
{
	g_mec_state->shared_mec_members = 0U;

	for (unsigned int i = 0U; i < MECID_ARRAY_SIZE; i++) {
		g_mec_state->mec_reserved[i] = 0UL;
	}
	g_mec_state->mec_reserved[MECID_SYSTEM_OFFSET] = MEC_RESERVE_INITALIZER;
}

/*
 * Initialize MEC state structure. Skip initialization if already done.
 */
void mec_init_state(uintptr_t state, size_t state_size)
{
	assert(state != 0UL);

	(void)state_size;

	g_mec_state = (struct mec_state_s *)state;
	assert(state_size >= sizeof(struct mec_state_s));

	INFO(SCRUB_METHOD_STRING);

	if (g_mec_state->is_init == true) {
		/* Use mec_state from previous RMM */
		return;
	}

	/* Initialize mec_state with default values */
	mec_state_init_values();

	g_mec_state->is_init = true;
}

/*
 * Test API, only used for unit tests
 */
void mec_test_reset(void)
{
	/* Reset MEC state to power-on reset values. */
	mec_state_init_values();

	for (unsigned int i = 0U; i < MAX_CPUS; i++) {
		mecid_pcpcu_refcnt[i] = 0U;
	}
}
