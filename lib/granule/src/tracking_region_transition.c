/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#include <assert.h>
#include <atomics.h>
#include <dev_granule.h>
#include <granule.h>
#include <smc-rmi.h>
#include <stdbool.h>
#include <stdint.h>
#include <tracking_region_lock.h>
#include <tracking_region_pvt.h>
#include <utils_def.h>

/* Bit position of the in-progress transition flag in struct tracking_region. */
#define TR_TRANSITION_SHIFT		U(4)

/* Bitmask selecting the in-progress transition flag in struct tracking_region. */
#define TR_TRANSITION_BIT		(U(1) << TR_TRANSITION_SHIFT)

COMPILER_ASSERT(TR_TRANSITION_SHIFT < 8U);

/* Return the tracking state recorded in @tr. */
enum tr_state tracking_region_get_state(const struct tracking_region *tr)
{
	assert(tr != NULL);

	return (enum tr_state)EXTRACT(TR_STATE,
				       SCA_READ8(&tr->descriptor));
}

/* Return whether an SRO owns an incomplete transition on @tr. */
bool tracking_region_transition_pending(const struct tracking_region *tr)
{
	assert(tr != NULL);

	return (SCA_READ8(&tr->descriptor) & TR_TRANSITION_BIT) != 0U;
}

/* Set or clear the SRO transition marker while holding the region write lock. */
void tracking_region_transition_set_locked(struct tracking_region *tr,
					   bool pending)
{
	uint8_t descriptor;

	assert((tr != NULL) && tracking_region_is_write_locked(tr));
	descriptor = SCA_READ8(&tr->descriptor);
	if (pending) {
		descriptor |= (uint8_t)TR_TRANSITION_BIT;
	} else {
		descriptor &= (uint8_t)~TR_TRANSITION_BIT;
	}
	(void)atomic_eor_8(&tr->descriptor,
			   SCA_READ8(&tr->descriptor) ^ descriptor);
}

/* Atomically update the state field while retaining the region write lock. */
static void tracking_region_set_state_locked(struct tracking_region *tr,
					      enum tr_state state)
{
	uint8_t old_state;
	uint8_t new_state;

	assert((tr != NULL) && tracking_region_is_write_locked(tr));

	old_state = SCA_READ8(&tr->descriptor) & (uint8_t)MASK(TR_STATE);
	new_state = (uint8_t)((unsigned int)state << TR_STATE_SHIFT);
	(void)atomic_eor_8(&tr->descriptor, old_state ^ new_state);
}

/*
 * A fine-to-NONE transition requires every granule to be NS. A fine-to-
 * COARSE transition also permits a uniform DELEGATED state.
 */
static bool tracking_region_fine_source_state_allowed(
					enum tr_state target,
					unsigned char state)
{
	assert((target == trs_none) || (target == trs_coarse));

	if (target == trs_none) {
		return state == GRANULE_STATE_NS;
	}

	return (state == GRANULE_STATE_NS) ||
	       (state == GRANULE_STATE_DELEGATED);
}

/*
 * Fine-granule locks held for one tracking-region transition.
 *
 * Granule addresses do not need to be stored because acquisition and
 * release traverse the same sorted memory banks in the same order. Each count
 * therefore identifies how many granules of that type remain locked.
 *
 * @conv_count: Number of granules currently locked.
 * @dev_count: Number of dev_granules currently locked.
 */
struct tracking_region_fine_locks {
	unsigned long conv_count;
	unsigned long dev_count;
};

/*
 * Granule locks owned by one tracking-state transition.
 *
 * The record lets the common cleanup path release whichever active granule
 * representation was locked. A transition locks either the fine or coarse
 * representation according to the source tracking state.
 *
 * @fine: Counts of fine granule and dev_granule locks held.
 * @locked_state: Whether coarse or fine granules were locked.
 *                trs_none means that this record owns no granule locks.
 */
struct tracking_region_transition_locks {
	struct tracking_region_fine_locks fine;
	enum tr_state locked_state;
};

/*
 * Release the fine granules recorded in @locks.
 *
 * The lock record contains counts rather than granule addresses. Locking
 * visits the conventional banks followed by device banks, each in ascending
 * PA order, and increments the corresponding count after every acquired
 * lock. Replay that traversal and stop at each count to unlock exactly the
 * granules acquired before a failed collection or completed transition.
 */
static void tracking_region_fine_descriptors_unlock(
					unsigned long base,
					struct tracking_region_fine_locks *locks)
{
	unsigned long conv_remaining;
	unsigned long dev_remaining;
	unsigned int cursor = 0U;
	unsigned long start;
	unsigned long end;
	unsigned long fine_idx;

	assert(locks != NULL);
	conv_remaining = locks->conv_count;
	dev_remaining = locks->dev_count;

	while ((conv_remaining != 0UL) &&
	       tracking_region_next_bank_range(base, TR_MEM_TYPE_CONV, &cursor,
					       &start, &end, &fine_idx)) {
		for (unsigned long addr = start; addr < end; addr += GRANULE_SIZE) {
			if (conv_remaining == 0UL) {
				break;
			}
			granule_unlock(tr_fine_granule_from_idx(
					fine_idx + ((addr - start) / GRANULE_SIZE)));
			conv_remaining--;
		}
	}

	cursor = 0U;
	while ((dev_remaining != 0UL) &&
	       tracking_region_next_bank_range(base, TR_MEM_TYPE_DEV, &cursor,
					       &start, &end, &fine_idx)) {
		for (unsigned long addr = start; addr < end; addr += GRANULE_SIZE) {
			struct dev_granule *g;

			if (dev_remaining == 0UL) {
				break;
			}
			g = tr_fine_dev_granule_from_idx(
					fine_idx + ((addr - start) / GRANULE_SIZE));
			dev_granule_unlock(g);
			dev_remaining--;
		}
	}

	assert((conv_remaining == 0UL) && (dev_remaining == 0UL));
	locks->conv_count = 0UL;
	locks->dev_count = 0UL;
}

/*
 * Lock the complete fine representation before transitioning out of FINE.
 *
 * @tr must be the struct tracking_region for the region whose base PA is
 * @base. @base must be aligned to the configured tracking-region size, and the
 * caller must hold @tr's write lock. @category identifies the region's memory
 * composition. @target must be trs_none or trs_coarse and determines which
 * source Granule states can be represented by the destination.
 *
 * Traverse only the granule type used by a homogeneous region. For a diverse
 * region, acquire granules in ascending PA order before acquiring dev_granules.
 * The first ordinary granule establishes the source state; every subsequent
 * ordinary granule must have the same state after acquisition. A contended
 * granule aborts this attempt without waiting.
 * Host-donated, self-describing metadata pages are locked in
 * INTERNAL state but excluded from this comparison because they belong to the
 * fine representation being removed.
 * Derive each fine index from its PA so skipping metadata still advances both.
 *
 * Return RMI_SUCCESS with @state and @locks describing the locked source.
 * Return RMI_BUSY on lock contention, RMI_BLOCKED for an SRO-owned PARTIAL
 * granule, or RMI_ERROR_INPUT if no ordinary granule exists or another
 * source state is invalid. Every failure releases the acquired prefix; the
 * caller must also release the region writer.
 */
static unsigned long tracking_region_fine_descriptors_lock(
					struct tracking_region *tr,
					unsigned long base,
					enum tr_mem_cat category,
					enum tr_state target,
					unsigned char *state,
					struct tracking_region_fine_locks *locks)
{
	bool state_valid = false;
	unsigned long ret = RMI_ERROR_INPUT;
	bool scan_conv;
	bool scan_dev;
	unsigned int cursor = 0U;
	unsigned long start;
	unsigned long end;
	unsigned long fine_idx;

	assert((tr != NULL) && (locks != NULL) && (state != NULL));
	assert(tracking_region_is_write_locked(tr));
	assert((category == mc_conv) || (category == mc_dev_ncoh) ||
	       (category == mc_dev_coh) || (category == mc_diverse));
	assert((target == trs_none) || (target == trs_coarse));
	scan_conv = (category == mc_conv) || (category == mc_diverse);
	scan_dev = (category == mc_dev_ncoh) || (category == mc_dev_coh) ||
		   (category == mc_diverse);
	locks->conv_count = 0UL;
	locks->dev_count = 0UL;

	while (scan_conv &&
	       tracking_region_next_bank_range(base, TR_MEM_TYPE_CONV, &cursor,
					       &start, &end, &fine_idx)) {
		for (unsigned long addr = start; addr < end; addr += GRANULE_SIZE) {
			struct granule *g =
				tr_fine_granule_from_idx(
					fine_idx + ((addr - start) / GRANULE_SIZE));
			unsigned char current;

			/* Never wait for an RMI caller while excluding its readers. */
			if (!granule_bitlock_try_acquire(g)) {
				ret = RMI_BUSY;
				goto out_err;
			}
			locks->conv_count++;
			current = granule_get_state(g);
			/* Self-describing metadata is locked but does not set the source state. */
			if ((current == GRANULE_STATE_INTERNAL) &&
			    tracking_region_is_self_describing_fine_page(tr, addr)) {
				continue;
			}
			if (!state_valid) {
				*state = current;
				state_valid = true;
			}
			if (current == GRANULE_STATE_PARTIAL) {
				/* Only the owning SRO can complete this intermediate state. */
				ret = RMI_BLOCKED;
				goto out_err;
			}
			if (!tracking_region_fine_source_state_allowed(target, current) ||
			    (current != *state)) {
				ret = RMI_ERROR_INPUT;
				goto out_err;
			}
		}
	}

	cursor = 0U;
	while (scan_dev &&
	       tracking_region_next_bank_range(base, TR_MEM_TYPE_DEV, &cursor,
					       &start, &end, &fine_idx)) {
		for (unsigned long addr = start; addr < end; addr += GRANULE_SIZE) {
			struct dev_granule *g =
				tr_fine_dev_granule_from_idx(
					fine_idx + ((addr - start) / GRANULE_SIZE));
			unsigned char current;

			if (!dev_granule_bitlock_try_acquire(g)) {
				ret = RMI_BUSY;
				goto out_err;
			}
			locks->dev_count++;
			current = dev_granule_get_state(g);
			if (!state_valid) {
				*state = current;
				state_valid = true;
			}
			if (current == DEV_GRANULE_STATE_PARTIAL) {
				/* Only the owning SRO can complete this intermediate state. */
				ret = RMI_BLOCKED;
				goto out_err;
			}
			if (!tracking_region_fine_source_state_allowed(target, current) ||
			    (current != *state)) {
				ret = RMI_ERROR_INPUT;
				goto out_err;
			}
		}
	}

	/* A metadata-only region still needs its acquired INTERNAL locks released. */
	if (!state_valid) {
		goto out_err;
	}
	return RMI_SUCCESS;

out_err:
	tracking_region_fine_descriptors_unlock(base, locks);
	return ret;
}

/* Return whether @state can be converted from COARSE to @target. */
static bool tracking_region_coarse_source_state_allowed(
					enum tr_mem_cat category,
					enum tr_state target,
					unsigned char state)
{
	assert((category == mc_conv) || (category == mc_dev_ncoh) ||
	       (category == mc_dev_coh));
	assert((target == trs_none) || (target == trs_fine));

	if (target == trs_none) {
		return state == GRANULE_STATE_NS;
	}
	if (category == mc_conv) {
		return (state == GRANULE_STATE_NS) ||
		       (state == GRANULE_STATE_DELEGATED) ||
		       (state == GRANULE_STATE_DATA);
	}

	return (state == DEV_GRANULE_STATE_NS) ||
	       (state == DEV_GRANULE_STATE_DELEGATED) ||
	       (state == DEV_GRANULE_STATE_MAPPED);
}

/*
 * Try to lock and validate the coarse source under @tr's write lock.
 * @category selects the granule; @target determines its permitted states.
 * Return RMI_SUCCESS with the source locked and its state in *@state,
 * RMI_BUSY on contention, RMI_BLOCKED for an SRO-owned PARTIAL source, or
 * RMI_ERROR_INPUT for another invalid source state.
 * A failed attempt retains no granule lock.
 */
static unsigned long tracking_region_coarse_lock(struct tracking_region *tr,
					enum tr_mem_cat category,
					enum tr_state target,
					unsigned char *state)
{
	assert((tr != NULL) && (state != NULL));
	assert((category == mc_conv) || (category == mc_dev_ncoh) ||
	       (category == mc_dev_coh));

	if (category == mc_conv) {
		if (!granule_bitlock_try_acquire(&tr->coarse_granule)) {
			return RMI_BUSY;
		}
		*state = granule_get_state(&tr->coarse_granule);
		if (*state == GRANULE_STATE_PARTIAL) {
			/* Only the owning SRO can complete this intermediate state. */
			granule_unlock(&tr->coarse_granule);
			return RMI_BLOCKED;
		}
		if (!tracking_region_coarse_source_state_allowed(category, target, *state)) {
			granule_unlock(&tr->coarse_granule);
			return RMI_ERROR_INPUT;
		}
	} else {
		if (!dev_granule_bitlock_try_acquire(&tr->coarse_dev_granule)) {
			return RMI_BUSY;
		}
		*state = dev_granule_get_state(&tr->coarse_dev_granule);
		if (*state == DEV_GRANULE_STATE_PARTIAL) {
			/* Only the owning SRO can complete this intermediate state. */
			dev_granule_unlock(&tr->coarse_dev_granule);
			return RMI_BLOCKED;
		}
		if (!tracking_region_coarse_source_state_allowed(category, target, *state)) {
			dev_granule_unlock(&tr->coarse_dev_granule);
			return RMI_ERROR_INPUT;
		}
	}
	return RMI_SUCCESS;
}

/* Unlock the coarse granule selected by @category. */
static void tracking_region_coarse_unlock(struct tracking_region *tr,
					  enum tr_mem_cat category)
{
	assert(tr != NULL);
	assert((category == mc_conv) || (category == mc_dev_ncoh) ||
	       (category == mc_dev_coh));

	if (category == mc_conv) {
		granule_unlock(&tr->coarse_granule);
	} else {
		dev_granule_unlock(&tr->coarse_dev_granule);
	}
}

/*
 * Validate and lock the granules associated with a tracking region
 * with state @current.
 *
 * The caller must hold the write lock for @tr. This prevents new lookups from
 * accessing @tr while its state changes from @current to @target. An operation
 * which looked up @tr before the write lock was acquired may still hold a
 * granule lock. Try each source lock once and validate its state only
 * after acquisition; a contended source returns RMI_BUSY without waiting.
 *
 * @base and @category identify @tr and its memory composition. @current is the
 * current tracking state, while @target is the requested tracking state and
 * determines the permitted source Granule states. A coarse source requires one
 * granule lock. A fine source requires all applicable granules to be
 * locked in the same permitted state. A NONE source has no granules to lock
 * and leaves @state unchanged.
 *
 * Return RMI_SUCCESS with @state and @locks describing the locked source,
 * RMI_BUSY on contention, RMI_BLOCKED for a PARTIAL source, or
 * RMI_ERROR_INPUT for another invalid source. Failures retain no granule
 * locks. The caller releases the region writer.
 */
static unsigned long tracking_region_transition_locks_acquire(
					struct tracking_region *tr,
					unsigned long base,
					enum tr_mem_cat category,
					enum tr_state current,
					enum tr_state target,
					unsigned char *state,
					struct tracking_region_transition_locks *locks)
{
	unsigned long ret;

	assert((tr != NULL) && (state != NULL) && (locks != NULL));
	assert(tracking_region_is_write_locked(tr));
	locks->fine.conv_count = 0UL;
	locks->fine.dev_count = 0UL;
	locks->locked_state = trs_none;

	switch (current) {
	case trs_none:
		return RMI_SUCCESS;
	case trs_coarse:
		ret = tracking_region_coarse_lock(tr, category, target, state);
		break;
	case trs_fine:
		ret = tracking_region_fine_descriptors_lock(tr, base, category,
						 target, state, &locks->fine);
		break;
	default:
		return RMI_ERROR_INPUT;
	}
	if (ret == RMI_SUCCESS) {
		locks->locked_state = current;
	}
	return ret;
}

/*
 * Release the Granule locks recorded in @locks.
 *
 * The caller must hold the write lock for @tr. @tr, @base and @category must
 * match the arguments passed to tracking_region_transition_locks_acquire().
 * @locks->locked_state determines whether to release the fine granules or
 * the coarse granule. No granule is released for trs_none. Reset
 * @locks->locked_state to trs_none after cleanup.
 */
static void tracking_region_transition_locks_release(
					struct tracking_region *tr,
					unsigned long base,
					enum tr_mem_cat category,
					struct tracking_region_transition_locks *locks)
{
	assert((tr != NULL) && (locks != NULL));
	assert(tracking_region_is_write_locked(tr));

	if (locks->locked_state == trs_fine) {
		tracking_region_fine_descriptors_unlock(base, &locks->fine);
	} else if (locks->locked_state == trs_coarse) {
		tracking_region_coarse_unlock(tr, category);
	} else {
		assert(locks->locked_state == trs_none);
	}
	locks->locked_state = trs_none;
}

/*
 * Claim a metadata-transfer SRO after validating its complete source.
 *
 * On success, set @tr's transition-pending marker before releasing the region
 * write lock and source granule locks. Return RMI_SUCCESS with the marker
 * still owned by the caller; it remains set until the owner explicitly clears it.
 *
 * Return RMI_BLOCKED if another SRO owns the transition marker or a
 * PARTIAL source, RMI_BUSY for contention or a stale snapshot, or
 * RMI_ERROR_INPUT for another invalid source/transition, without claiming it.
 * See tracking_region_pvt.h for the snapshot and locking contracts.
 */
/* cppcheck-suppress misra-c2012-8.7 */
unsigned long tracking_region_transition_claim(struct tracking_region *tr,
					       unsigned long addr,
					       enum tr_state current,
					       enum tr_state target)
{
	struct tracking_region_transition_locks locks = { .locked_state = trs_none };
	enum tr_mem_cat composition;
	unsigned char state = GRANULE_STATE_NS;
	unsigned long ret = RMI_ERROR_INPUT;

	assert((tr != NULL) && ALIGNED(addr, tracking_region_get_size()));
	assert((target == trs_none) || (target == trs_coarse) || (target == trs_fine));
	assert(current != target);
	if (!tracking_region_write_try_lock(tr)) {
		return RMI_BUSY;
	}
	composition = (enum tr_mem_cat)EXTRACT(TR_MEM_CAT, tr->descriptor);
	if (tracking_region_transition_pending(tr)) {
		ret = RMI_BLOCKED;
		goto out;
	}
	if (tracking_region_get_state(tr) != current) {
		ret = RMI_BUSY;
		goto out;
	}
	if ((current == trs_reserved) ||
	    ((target == trs_coarse) && (composition == mc_diverse))) {
		goto out;
	}

	ret = tracking_region_transition_locks_acquire(tr, addr, composition,
						current, target, &state, &locks);
	if (ret == RMI_SUCCESS) {
		/*
		 * A granule user must finish before new lookups can be blocked
		 * by this marker. Invalid source states must not block lookups at
		 * all: fine DATA/MAPPED users rely on them preventing transitions.
		 */
		tracking_region_transition_set_locked(tr, true);
	}
out:
	tracking_region_transition_locks_release(tr, addr, composition, &locks);
	tracking_region_write_unlock(tr);
	return ret;
}

/*
 * Initialize granule @g with @state and @refcount.
 *
 * The caller must hold the write lock for @tr and ensure that @g cannot be
 * selected by a tracking lookup. @g must be unlocked.
 */
static void tracking_granule_init_inactive(struct tracking_region *tr,
					   struct granule *g,
					   unsigned char state,
					   unsigned short refcount)
{
	assert((tr != NULL) && (g != NULL));
	assert(tracking_region_is_write_locked(tr));
	assert(!LOCKED(g));
	assert(refcount <= REFCOUNT_MAX);
	(void)tr;
	g->descriptor = (unsigned short)INPLACE(GRN_STATE, state) |
			(unsigned short)INPLACE(GRN_REFCOUNT, refcount);
}

/*
 * Initialize the fine granule for self-describing metadata page @addr.
 *
 * @addr must be a Host-donated conventional page which backs fine metadata for
 * @tr and lies within that tracking region. The caller must hold @tr's write
 * lock while its transition marker is set, preventing normal lookups from
 * selecting the granule. Initialize it as INTERNAL with no references.
 */
/* cppcheck-suppress misra-c2012-8.7 */
void tracking_region_fine_descriptor_init_internal_locked(
					struct tracking_region *tr,
					unsigned long addr)
{
	struct granule *g;

	assert((tr != NULL) && tracking_region_is_write_locked(tr));
	g = tr_addr_to_granule(addr);
	tracking_granule_init_inactive(tr, g, GRANULE_STATE_INTERNAL, 0U);
}

/*
 * Initialize dev_granule @g with @state and @refcount.
 *
 * The caller must hold the write lock for @tr and ensure that @g cannot be
 * selected by a tracking lookup. @g must be unlocked.
 */
static void tracking_dev_granule_init_inactive(struct tracking_region *tr,
					       struct dev_granule *g,
					       unsigned char state,
					       unsigned char refcount)
{
	assert((tr != NULL) && (g != NULL));
	assert(tracking_region_is_write_locked(tr));
	assert(!DEV_LOCKED(g));
	assert(refcount <= DEV_REFCOUNT_MAX);
	(void)tr;
	g->descriptor = (unsigned char)INPLACE(DEV_GRN_STATE, state) |
			(unsigned char)INPLACE(DEV_GRN_REFCOUNT, refcount);
}

/*
 * Initialize the fine granules for the tracking region at @base.
 *
 * @tr must describe the region at @base, and its write lock must be held. The
 * fine representation must be inactive while it is initialized, as it is the
 * destination of a NONE-to-FINE or COARSE-to-FINE transition. @category
 * identifies which granule arrays belong to the region; both arrays are
 * initialized only for a diverse region. Initialize each selected granule
 * to @state and @refcount without taking its lock. @refcount must fit the
 * granule type for every populated bank.
 */
static void tracking_region_fine_descriptors_init(struct tracking_region *tr,
						  unsigned long base,
						  enum tr_mem_cat category,
						  unsigned char state,
						  unsigned short refcount)
{
	bool init_conv;
	bool init_dev;
	unsigned int cursor = 0U;
	unsigned long start;
	unsigned long end;
	unsigned long fine_idx;

	assert((category == mc_conv) || (category == mc_dev_ncoh) ||
	       (category == mc_dev_coh) || (category == mc_diverse));
	init_conv = (category == mc_conv) || (category == mc_diverse);
	init_dev = (category == mc_dev_ncoh) || (category == mc_dev_coh) ||
		   (category == mc_diverse);

	while (init_conv &&
	       tracking_region_next_bank_range(base, TR_MEM_TYPE_CONV, &cursor,
					       &start, &end, &fine_idx)) {
		for (unsigned long addr = start; addr < end; addr += GRANULE_SIZE) {
			struct granule *g =
				tr_fine_granule_from_idx(
					fine_idx + ((addr - start) / GRANULE_SIZE));

			tracking_granule_init_inactive(tr, g, state, refcount);
		}
	}

	cursor = 0U;
	while (init_dev &&
	       tracking_region_next_bank_range(base, TR_MEM_TYPE_DEV, &cursor,
					       &start, &end, &fine_idx)) {
		assert(refcount <= DEV_REFCOUNT_MAX);
		for (unsigned long addr = start; addr < end; addr += GRANULE_SIZE) {
			struct dev_granule *g =
				tr_fine_dev_granule_from_idx(
					fine_idx + ((addr - start) / GRANULE_SIZE));

			tracking_dev_granule_init_inactive(
						tr, g, state,
						(unsigned char)refcount);
		}
	}
}

/*
 * Initialize the inactive fine representation from a coarse granule.
 *
 * The caller must hold @tr's write lock, @tr must be in COARSE state and
 * @base must be tracking-region aligned. @category selects the active coarse
 * granule. For DATA or mapped device memory, copy its reference count to
 * every fine granule so existing auxiliary-plane mappings remain
 * represented.
 *
 * Return true if @state can be represented by fine granules, or false if
 * the coarse state cannot be split.
 */
static bool tracking_region_coarse_to_fine_init(
					struct tracking_region *tr,
					unsigned long base,
					enum tr_mem_cat category,
					unsigned char state)
{
	unsigned short refcount = 0U;

	assert(tr != NULL);
	assert(tracking_region_is_write_locked(tr));
	assert(tracking_region_get_state(tr) == trs_coarse);

	if (category == mc_conv) {
		switch (state) {
		case GRANULE_STATE_NS:
		case GRANULE_STATE_DELEGATED:
			break;
		case GRANULE_STATE_DATA:
			refcount = granule_refcount_read_acquire(
							&tr->coarse_granule);
			break;
		default:
			/* RD, RTT and other object states cannot be coarse tracked. */
			return false;
		}
	} else {
		assert((category == mc_dev_ncoh) || (category == mc_dev_coh));
		switch (state) {
		case DEV_GRANULE_STATE_NS:
		case DEV_GRANULE_STATE_DELEGATED:
			break;
		case DEV_GRANULE_STATE_MAPPED:
			refcount = dev_granule_refcount_read_acquire(
						&tr->coarse_dev_granule);
			break;
		default:
			return false;
		}
	}

	tracking_region_fine_descriptors_init(tr, base, category, state, refcount);
	return true;
}

/* Initialize the coarse granule selected by @category. */
static void tracking_region_coarse_init(struct tracking_region *tr,
					enum tr_mem_cat category,
					unsigned char state)
{
	assert((tr != NULL) && tracking_region_is_write_locked(tr));

	if (category == mc_conv) {
		tracking_granule_init_inactive(tr, &tr->coarse_granule,
					       state, 0U);
	} else {
		tracking_dev_granule_init_inactive(tr,
						  &tr->coarse_dev_granule,
						  state, 0U);
	}
}

/*
 * Transition the tracking region at @addr to @state.
 *
 * @addr must be tracking-region aligned. If @addr belongs to a populated bank,
 * @category must match that bank. A base in an unpopulated prefix is accepted
 * for NONE or FINE when the same diverse region contains memory at a higher
 * address; @category is ignored in that case.
 *
 * Try to acquire the region writer and every active source granule.
 * On contention release the acquired locks and return RMI_BUSY so readers
 * can continue. Once acquired, validate and publish without waiting for any
 * further lock. Release the granule locks before the region writer.
 *
 * @sro_owner indicates that the caller owns the SRO transition marker and may
 * complete the transition while that marker is set. A non-owner receives
 * RMI_BLOCKED while the marker is set.
 *
 * Return RMI_SUCCESS if the requested state is installed or was already set.
 * Return RMI_ERROR_INPUT if an input or requested state transition is invalid.
 * Return RMI_BUSY on lock contention, or RMI_BLOCKED if another SRO owns the
 * marker or a PARTIAL source.
 */
static unsigned long tracking_region_transition(unsigned long addr,
						unsigned long category,
						unsigned long state,
						bool sro_owner)
{
	struct tracking_region *tr;
	enum tr_mem_cat composition = mc_diverse;
	enum tr_state current;
	struct tracking_region_transition_locks transition_locks = {
		.locked_state = trs_none
	};
	unsigned char granule_state = GRANULE_STATE_NS;
	unsigned long tr_idx __unused;
	unsigned long ret = RMI_ERROR_INPUT;

	if ((state != RMI_TRACKING_NONE) &&
	    (state != RMI_TRACKING_FINE) &&
	    (state != RMI_TRACKING_COARSE)) {
		return RMI_ERROR_INPUT;
	}
	if (!tracking_region_set_tracking_find(addr, category, &tr_idx, &tr)) {
		return RMI_ERROR_INPUT;
	}

	/* Keep the gate open for readers whenever this transition must back off. */
	if (!tracking_region_write_try_lock(tr)) {
		return RMI_BUSY;
	}
	/* Permit only the SRO which set the marker to complete this transition. */
	if (tracking_region_transition_pending(tr) && !sro_owner) {
		ret = RMI_BLOCKED;
		goto out;
	}
	current = tracking_region_get_state(tr);
	composition = (enum tr_mem_cat)EXTRACT(TR_MEM_CAT,
					      SCA_READ8(&tr->descriptor));

	/* Reserved regions cannot transition; matching states are idempotent. */
	if (current == trs_reserved) {
		goto out;
	}

	if ((unsigned long)current == state) {
		ret = RMI_SUCCESS;
		goto out;
	}

	/* Coarse tracking cannot represent a region with mixed composition. */
	if ((state == RMI_TRACKING_COARSE) &&
	    (composition == mc_diverse)) {
		goto out;
	}

	/* Try the complete source; contention must release the writer as well. */
	ret = tracking_region_transition_locks_acquire(tr, addr, composition,
				current, (enum tr_state)state, &granule_state,
				&transition_locks);
	if (ret != RMI_SUCCESS) {
		goto out;
	}
	ret = RMI_ERROR_INPUT;

	/*
	 * Preserve the source Granule state when transitioning tracking region. A
	 * NONE source has no granules, so newly enabled tracking starts at NS.
	 */
	switch (current) {
	case trs_none:
		/* Newly tracked Granules begin in the undelegated state. */
		if (state == RMI_TRACKING_FINE) {
			tracking_region_fine_descriptors_init(tr, addr, composition,
							 GRANULE_STATE_NS, 0U);
		} else {
			tracking_region_coarse_init(tr, composition,
						    GRANULE_STATE_NS);
		}
		break;
	case trs_fine:
		if (state == RMI_TRACKING_NONE) {
			if (granule_state != GRANULE_STATE_NS) {
				goto out;
			}
		} else {
			assert(state == RMI_TRACKING_COARSE);
			if (!tracking_region_fine_source_state_allowed(
							trs_coarse, granule_state)) {
				goto out;
			}
			tracking_region_coarse_init(tr, composition,
						    granule_state);
		}
		break;
	case trs_coarse:
		if (state == RMI_TRACKING_NONE) {
			if (granule_state != GRANULE_STATE_NS) {
				goto out;
			}
		} else if (!tracking_region_coarse_to_fine_init(
					tr, addr, composition, granule_state)) {
			goto out;
		}
		break;
	default:
		goto out;
	}

	tracking_region_set_state_locked(tr, (enum tr_state)state);
	ret = RMI_SUCCESS;

out:
	tracking_region_transition_locks_release(tr, addr, composition,
						 &transition_locks);
	tracking_region_write_unlock(tr);
	return ret;
}

/*
 * Change a tracking region synchronously when no metadata transfer is needed.
 * An incomplete SRO transition owns the region and causes RMI_BLOCKED.
 */
/* cppcheck-suppress misra-c2012-8.7 */
unsigned long tracking_region_set_tracking(unsigned long addr,
					   unsigned long category,
					   unsigned long state)
{
	return tracking_region_transition(addr, category, state, false);
}

/*
 * Change a tracking representation for the SRO which owns its transition
 * marker. The common transition implementation still validates the marker,
 * source state and complete locking contract.
 */
/* cppcheck-suppress misra-c2012-8.7 */
unsigned long tracking_region_set_tracking_owned(unsigned long addr,
						 unsigned long category,
						 unsigned long state)
{
	return tracking_region_transition(addr, category, state, true);
}
