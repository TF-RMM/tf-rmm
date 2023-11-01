/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef GRANULE_H
#define GRANULE_H

#include <assert.h>
#include <atomics.h>
#include <buffer.h>
#include <errno.h>
#include <granule_types.h>
#include <memory.h>
#include <spinlock.h>
#include <status.h>

static inline unsigned long granule_refcount_read_relaxed(struct granule *g)
{
	return __sca_read64(&g->refcount);
}

static inline unsigned long granule_refcount_read_acquire(struct granule *g)
{
	return __sca_read64_acquire(&g->refcount);
}

/*
 * Sanity-check unlocked granule invariants.
 *
 * These invariants must hold for any granule which is unlocked.
 *
 * These invariants may not hold transiently while a granule is locked (e.g.
 * when transitioning to/from delegated state).
 *
 * Note: this function is purely for debug/documentation purposes, and is not
 * intended as a mechanism to ensure correctness.
 */
static inline void __granule_assert_unlocked_invariants(struct granule *g,
							enum granule_state state)
{
	(void)g;

	switch (state) {
	case GRANULE_STATE_NS:
		assert(granule_refcount_read_relaxed(g) == 0UL);
		break;
	case GRANULE_STATE_DELEGATED:
		assert(g->refcount == 0UL);
		break;
	case GRANULE_STATE_RD:
		/*
		 * refcount is used to check if RD and associated granules can
		 * be freed because they're no longer referenced by any other
		 * object. Can be any non-negative number.
		 */
		break;
	case GRANULE_STATE_REC:
		assert(granule_refcount_read_relaxed(g) <= 1UL);
		break;
	case GRANULE_STATE_DATA:
		assert(g->refcount == 0UL);
		break;
	case GRANULE_STATE_RTT:
		/* Refcount cannot be greater that number of entries in an RTT */
		assert(g->refcount <= (GRANULE_SIZE / sizeof(uint64_t)));
		break;
	case GRANULE_STATE_REC_AUX:
		assert(g->refcount == 0UL);
		break;
	default:
		/* Unknown granule type */
		assert(false);
	}
}

/* Must be called with g->lock held */
static inline enum granule_state granule_get_state(struct granule *g)
{
	return g->state;
}

/* Must be called with g->lock held */
static inline void granule_set_state(struct granule *g,
				     enum granule_state state)
{
	g->state = state;
}

/*
 * Acquire the spinlock and then check expected state
 * Fails if unexpected locking sequence detected.
 * Also asserts if invariant conditions are met.
 */
static inline bool granule_lock_on_state_match(struct granule *g,
				    enum granule_state expected_state)
{
	spinlock_acquire(&g->lock);

	if (granule_get_state(g) != expected_state) {
		spinlock_release(&g->lock);
		return false;
	}

	__granule_assert_unlocked_invariants(g, expected_state);
	return true;
}

/*
 * Used when we're certain of the type of an object (e.g. because we hold a
 * reference to it). In these cases we should never fail to acquire the lock.
 */
static inline void granule_lock(struct granule *g,
				enum granule_state expected_state)
{
	__unused bool locked = granule_lock_on_state_match(g, expected_state);

	assert(locked);
}

static inline void granule_unlock(struct granule *g)
{
	__granule_assert_unlocked_invariants(g, granule_get_state(g));
	spinlock_release(&g->lock);
}

/* Transtion state to @new_state and unlock the granule */
static inline void granule_unlock_transition(struct granule *g,
					     enum granule_state new_state)
{
	granule_set_state(g, new_state);
	granule_unlock(g);
}

unsigned long granule_addr(const struct granule *g);
struct granule *addr_to_granule(unsigned long addr);
struct granule *find_granule(unsigned long addr);
struct granule *find_lock_granule(unsigned long addr,
				  enum granule_state expected_state);

bool find_lock_two_granules(unsigned long addr1,
			    enum granule_state expected_state1,
			    struct granule **g1,
			    unsigned long addr2,
			    enum granule_state expected_state2,
			    struct granule **g2);

void granule_memzero(struct granule *g, enum buffer_slot slot);

void granule_memzero_mapped(void *buf);

void *aux_granules_map(struct granule *rec_aux_pages[], unsigned int num_aux);
void aux_granules_unmap(void *rec_aux, unsigned int num_aux);

/* Must be called with g->lock held */
static inline void __granule_get(struct granule *g)
{
	assert(g->lock.val != 0U);
	g->refcount++;
}

/* Must be called with g->lock held */
static inline void __granule_put(struct granule *g)
{
	assert(g->lock.val != 0U);
	assert(g->refcount > 0UL);
	g->refcount--;
}

/* Must be called with g->lock held */
static inline void __granule_refcount_inc(struct granule *g, unsigned long val)
{
	assert(g->lock.val != 0U);
	g->refcount += val;
}

/* Must be called with g->lock held */
static inline void __granule_refcount_dec(struct granule *g, unsigned long val)
{
	assert(g->lock.val != 0U);
	assert(g->refcount >= val);
	g->refcount -= val;
}

/*
 * Atomically increments the reference counter of the granule.
 */
static inline void atomic_granule_get(struct granule *g)
{
	atomic_add_64(&g->refcount, 1L);
}

/*
 * Atomically decrements the reference counter of the granule.
 */
static inline void atomic_granule_put(struct granule *g)
{
	atomic_add_64(&g->refcount, -1L);
}

/*
 * Atomically decrements the reference counter of the granule.
 * Stores to memory with release semantics.
 */
static inline void atomic_granule_put_release(struct granule *g)
{
	unsigned long old_refcount __unused;

	old_refcount = atomic_load_add_release_64(&g->refcount, -1L);
	assert(old_refcount > 0UL);
}

/*
 * Obtain a pointer to a locked unused granule at @addr if @addr is a valid
 * granule physical address, the state of the granule at @addr is
 * @expected_state, and the granule at @addr is unused.
 *
 * Returns:
 * 0, @*g - address of the granule,
 *	if @addr is a valid granule physical address.
 * -EINVAL, @*g = NULL,
 *	if @addr is not aligned to the size of a granule,
 *	@addr is out of range, or if the state of the granule at @addr
 *	is not @expected_state.
 * -EBUSY, @*g = NULL,
 *	if the granule at @addr has a non-zero reference count.
 */
static inline int find_lock_unused_granule(unsigned long addr,
					   enum granule_state expected_state,
					   struct granule **g)
{
	*g = find_lock_granule(addr, expected_state);
	if (*g == NULL) {
		return -EINVAL;
	}

	/*
	 * Granules can have lock-free access (e.g. REC), thus using acquire
	 * semantics to avoid race conditions.
	 */
	if (granule_refcount_read_acquire(*g) != 0UL) {
		granule_unlock(*g);
		*g = NULL;
		return -EBUSY;
	}

	return 0;
}

#endif /* GRANULE_H */
