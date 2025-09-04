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
#include <memory.h>
#include <rmm_el3_ifc.h>
#include <sizes.h>
#include <spinlock.h>

#define MECID_WIDTH	U(16)
#define MEC_MAX_COUNT	(U(1) << MECID_WIDTH)
#define MECID_INVALID	U(-1)

#define MECID_ARRAY_SIZE	((MEC_MAX_COUNT) / BITS_PER_UL)

#define MECID_SYSTEM_BIT	(1U << (RESERVED_MECID_SYSTEM % BITS_PER_UL))
#define MECID_SYSTEM_OFFSET	(RESERVED_MECID_SYSTEM / BITS_PER_UL)

#define IS_MEC_VALID(id)	(((id) - RESERVED_IDS) <= mecid_max())

/* MECID of 0 is Shared as default */
#define MECID_DEFAULT_SHARED		INTERNAL_MECID(0U)
#define MECID_DEFAULT_SHARED_BIT	(1U << (MECID_DEFAULT_SHARED % BITS_PER_UL))
#define MECID_DEFAULT_SHARED_OFFSET	(MECID_DEFAULT_SHARED / BITS_PER_UL)

/*
 * Ensure that the array offset is the same so that we can use a single offset
 * for initializing DEFAULT_OFFSET_BIT and SYSTEM_BIT.
 */
COMPILER_ASSERT(MECID_DEFAULT_SHARED_OFFSET == MECID_SYSTEM_OFFSET);

#define MEC_RESERVE_INITALIZER		(MECID_DEFAULT_SHARED_BIT | MECID_SYSTEM_BIT)

static struct {
	/*
	 * Together, the mec_reserved array and the shared_mec value define the
	 * state of all MECs in the system.
	 *
	 * For a given mecid:
	 *
	 * if mecid == shared_mec
	 *     MEC state is SHARED
	 *
	 * if mec_reserved[mecid] == true
	 *     MEC state is PRIVATE_ASSIGNED or SHARED or RESERVED.
	 * else
	 *     MEC state is PRIVATE_UNASSIGNED
	 */
	unsigned long shared_mec_members;
	unsigned int shared_mec;

	spinlock_t shared_mecid_spinlock;

	/* The bitmap for the reserved/used MECID values.*/
	unsigned long mec_reserved[MECID_ARRAY_SIZE];
} mec_state = {
	.shared_mec = MECID_DEFAULT_SHARED,
	.mec_reserved = {
		[MECID_SYSTEM_OFFSET] = MEC_RESERVE_INITALIZER}
};

static uint64_t mecid_pcpcu_refcnt[MAX_CPUS];

void _mecid_s1_get(unsigned int mecid)
{
	/* no acquire/release needed as this is a per-cpu only access variable */
	uint64_t old_val =  atomic_load_add_64(&mecid_pcpcu_refcnt[my_cpuid()], 1U);
	if (old_val == 0U) {
		assert(read_mecid_a1_el2() == RESERVED_MECID_SYSTEM);
		write_mecid_a1_el2(INTERNAL_MECID(mecid));
		isb();
	} else {
		assert(read_mecid_a1_el2() == INTERNAL_MECID(mecid));
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

/* Maximum MECID allocatable */
unsigned int mecid_max(void)
{
	unsigned int mecid_count;

	/* cppcheck-suppress knownConditionTrueFalse */
	if (!is_feat_mec_present()) {
		return 0;
	}

	/*
	 * MECIDR_MECIDWIDTHM1 plus 1 is the MECID width in bits.
	 * So Max count is (2^MECID width) - 1. Also reduce the RESERVED_IDs
	 * from the count.
	 */
	mecid_count = (unsigned int)1 << (EXTRACT(MECIDR_MECIDWIDTHM1,
						read_mecidr_el2()) + 1U);
	mecid_count = mecid_count - RESERVED_IDS - 1U;

	assert(mecid_count <= MEC_MAX_COUNT);
	return mecid_count;
}

/*
 * Atomically set a bit corresponding to mecid. Returns true if the
 * bit was not set previously, else returns false.
 */
static bool mec_reserve(unsigned int mecid)
{
	unsigned int offset, bit;

	assert(IS_MEC_VALID(mecid));

	offset = mecid / BITS_PER_UL;
	bit = mecid % BITS_PER_UL;

	if (!atomic_bit_set_acquire_release_64(&mec_state.mec_reserved[offset],
						bit)) {
		/*
		 * Tweak the key associated with the MECID. This function
		 * is called with lock aqcuired when reserving Shared MECID.
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

	assert(IS_MEC_VALID(mecid));

	offset = mecid / BITS_PER_UL;
	bit = mecid % BITS_PER_UL;

	/*
	 * Tweak the key associated with the MECID. This function
	 * is called before releasing the MECID.
	 */
	(void)rmm_el3_ifc_mec_refresh((unsigned short)mecid, true);
	atomic_bit_clear_release_64(&mec_state.mec_reserved[offset], bit);
}

/*
 * Helper to set a MECID as shared. Check that there is no shared MECID
 * and if MECID reservation is successful, then sets the MECID as shared.
 */
int mec_set_shared(unsigned int mecid)
{
	int ret = -EINVAL;

	mecid = INTERNAL_MECID(mecid);

	if (!(IS_MEC_VALID(mecid))) {
		return ret;
	}

	spinlock_acquire(&mec_state.shared_mecid_spinlock);
	if ((SCA_READ32(&mec_state.shared_mec) == MECID_INVALID) &&
			mec_reserve(mecid)) {
		assert(mec_state.shared_mec_members == 0U);
		/* To match with read-acquire when read outside spinlock */
		SCA_WRITE32_RELEASE(&mec_state.shared_mec, mecid);
		ret = 0;
	}
	spinlock_release(&mec_state.shared_mecid_spinlock);

	return ret;
}

/*
 * Helper to set a Shared MECID as Private. If there are no Realms
 * using the Shared MECID and if the MECID was Shared, then
 * release the MECID reservation.
 */
int mec_set_private(unsigned int mecid)
{
	mecid = INTERNAL_MECID(mecid);

	/* cppcheck-suppress knownConditionTrueFalse */
	if (!is_feat_mec_present()) {
		return -1;
	}

	if (!(IS_MEC_VALID(mecid))) {
		return -1;
	}

	spinlock_acquire(&mec_state.shared_mecid_spinlock);
	if ((mec_state.shared_mec_members == 0U) &&
		(mecid == SCA_READ32(&mec_state.shared_mec))) {
		mec_release(mecid);
		/* To match with read-acquire when read outside spinlock */
		SCA_WRITE32_RELEASE(&mec_state.shared_mec, MECID_INVALID);
		spinlock_release(&mec_state.shared_mecid_spinlock);
		return 0;
	}
	spinlock_release(&mec_state.shared_mecid_spinlock);

	return -1;
}

/*
 * Assign a MECID for a particular Realm. Reserve
 * the MECID if it is not Shared. If Shared, increment
 * the use count.
 * Returns true if successful, else returns false.
 */
bool mecid_reserve(unsigned int mecid)
{
	/* cppcheck-suppress knownConditionTrueFalse */
	if (!is_feat_mec_present()) {
		return true;
	}

	mecid = INTERNAL_MECID(mecid);

	if (!(IS_MEC_VALID(mecid))) {
		return false;
	}

	assert(read_mecid_a1_el2() == RESERVED_MECID_SYSTEM);

	spinlock_acquire(&mec_state.shared_mecid_spinlock);
	if (mecid == SCA_READ32(&mec_state.shared_mec)) {
		bool ret;
		if (mec_state.shared_mec_members < UINT64_MAX) {
			mec_state.shared_mec_members++;
			ret = true;
		} else {
			ret = false;
		}
		spinlock_release(&mec_state.shared_mecid_spinlock);
		return ret;
	}
	spinlock_release(&mec_state.shared_mecid_spinlock);
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

	mecid = INTERNAL_MECID(mecid);

	/* The MECID is already validated during assign */
	assert(IS_MEC_VALID(mecid));

	spinlock_acquire(&mec_state.shared_mecid_spinlock);
	if (mecid == SCA_READ32(&mec_state.shared_mec)) {
		assert(mec_state.shared_mec_members > 0U);
		mec_state.shared_mec_members--;
		spinlock_release(&mec_state.shared_mecid_spinlock);
		return;
	}
	spinlock_release(&mec_state.shared_mecid_spinlock);
	mec_release(mecid);
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

	/*
	 * `shared_mec` can only be updated when no REC is using it and
	 * is only updated under the `shared_mecid_spinlock`. Read
	 * with ACQUIRE semantics.
	 */
	return (mecid != SCA_READ32_ACQUIRE(&mec_state.shared_mec));
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

	INFO(SCRUB_METHOD_STRING);

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
	(void)rmm_el3_ifc_mec_refresh(MECID_DEFAULT_SHARED, false);

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
