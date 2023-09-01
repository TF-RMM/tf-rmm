/*
 * SPDX-License-Identifier: BSD-3-Clause
 * SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
 */

#ifndef GRANULE_TYPES_H
#define GRANULE_TYPES_H

#include <spinlock.h>

/*
 * Locking Order
 * -------------
 * Granules must be locked in a specific order to prevent deadlocks.
 *
 * We define two classes of granule states: `external` and `internal`.
 *
 * A granule state belongs to the `external` class iff _any_ parameter to _any_
 * RMI command is an address of a granule which is expected to be in that state
 * i.e the lock is only acquired if the granule state of the address in RMI
 * command matches to that of the expected state.
 *
 * The following granule states are `external`:
 *
 * - GRANULE_STATE_NS
 * - GRANULE_STATE_DELEGATED
 * - GRANULE_STATE_RD
 * - GRANULE_STATE_REC
 *
 * Otherwise a granule state is considered `internal`.
 *
 * The following granule states are `internal`:
 *
 * - GRANULE_STATE_RTT
 * - GRANULE_STATE_DATA
 * - GRANULE_STATE_REC_AUX
 *
 * The following locking rules must be followed in all cases:
 *
 * 1. Granules expected to be in an `external` state must be locked before
 *    locking any granules in an `internal` state.
 *
 * 2. Granules expected to be in an `external` state must be locked in order
 *    of their physical address, starting with the lowest address.
 *
 * 3. Once a granule expected to be in an `external` state has been locked, its
 *    state must be checked against the expected state. If these do not match,
 *    the granule must be unlocked and no further granules may be locked.
 *
 * 4. Granules in an `internal` state must be locked in order of state:
 *    1. `RTT`
 *    2. `DATA`
 *    3. `REC_AUX`
 *
 * 5. Granules in the same `internal` state must be locked in the order defined
 *    below for that specific state.
 *
 * A granule's state can be changed iff the granule is locked.
 *
 * Invariants
 * ----------
 * GRANULE_STATE_DELEGATED is special, in that it is the gateway between the
 * non-secure and realm world.  We maintain the property that any unlocked
 * granule with state == GRANULE_STATE_DELEGATED contains only zeroes; while
 * locked these may contain non-zero values.
 */

enum granule_state {
	/*
	 * Non-Secure granule (external)
	 *
	 * Granule content is not protected by granule::lock, as it is always
	 * subject to reads and writes from the NS world.
	 */
	GRANULE_STATE_NS,
	/*
	 * Delegated Granule (external)
	 *
	 * Granule content is protected by granule::lock.
	 *
	 * No references are held on this granule type.
	 */
	GRANULE_STATE_DELEGATED,
	/*
	 * Realm Descriptor Granule (external)
	 *
	 * Granule content is protected by granule::lock.
	 *
	 * A reference is held on this granule:
	 * - For each associated REC granule.
	 *
	 * The RD may only be destroyed when the following objects
	 * have a reference count of zero:
	 * - The root-level RTT
	 */
	GRANULE_STATE_RD,
	/*
	 * Realm Execution Context Granule (external)
	 *
	 * Granule content (see struct rec) comprises execution
	 * context state and cached realm information copied from the RD.
	 *
	 * Execution context is not protected by granule::lock, because we can't
	 * enter a Realm while holding the lock.
	 *
	 * The following rules with respect to the granule's reference apply:
	 * - A reference is held on this granule when a REC is running.
	 * - As REC cannot be run on two PEs at the same time, the maximum
	 *   value of the reference count is one.
	 * - When the REC in entered, the reference count is incremented
	 *   (set to 1) atomically while granule::lock is held.
	 * - When the REC exits, the reference counter is released (set to 0)
	 *   atomically with store-release semantics without granule::lock being
	 *   held.
	 * - The RMM can access the granule's content on the entry and exit path
	 *   from the REC while the reference is held.
	 */
	GRANULE_STATE_REC,
	/*
	 * Realm Execution Context auxiliary granule (internal)
	 *
	 * Granule auxiliary content is used to store any state that cannot
	 * fit in the main REC page. This is typically used for context
	 * save/restore of PE features like SVE, SME, etc.
	 *
	 * Granule content is not protected by granule::lock nor the reference
	 * count. The RMM can access the content of the auxiliary granules
	 * only while holding a lock or reference to the parent REC granule.
	 *
	 * The granule::lock is held during a state change to
	 * GRANULE_STATE_REC_AUX and from GRANULE_STATE_REC_AUX.
	 *
	 * The complete internal locking order when changing REC_AUX
	 * granule's state is:
	 *
	 * REC -> REC_AUX[0] -> REC_AUX[1] -> ... -> REC_AUX[n-1]
	 */
	GRANULE_STATE_REC_AUX,

	/*
	 * Data Granule (internal)
	 *
	 * Granule content is not protected by granule::lock, as it is always
	 * subject to reads and writes from within a Realm.
	 *
	 * A granule in this state is always referenced from exactly one entry
	 * in an RTT granule which must be locked before locking this granule.
	 * Only a single DATA granule can be locked at a time.
	 * The complete internal locking order for DATA granules is:
	 *
	 * RD -> RTT -> RTT -> ... -> DATA
	 *
	 * No references are held on this granule type.
	 */
	GRANULE_STATE_DATA,
	/*
	 * RTT Granule (internal)
	 *
	 * Granule content is protected by granule::lock.
	 *
	 * Granule content is protected by granule::lock, but hardware
	 * translation table walks may read the RTT at any point in time.
	 * TODO: do we wish/need to use hardware access flag management?
	 *
	 * Multiple granules in this state can only be locked at the same time
	 * if they are part of the same tree, and only in topological order
	 * from root to leaf. The topological order of concatenated root level
	 * RTTs is from lowest address to highest address.
	 *
	 * The complete internal locking order for RTT granules is:
	 *
	 * RD -> [RTT] -> ... -> RTT
	 *
	 * A reference is held on this granule for each entry in the RTT that
	 * refers to a granule:
	 *   - Table s2tte.
	 *   - Assigned_RAM s2tte.
	 *   - Assigned_NS s2tte.
	 *   - Assigned s2tte.
	 */
	GRANULE_STATE_RTT,
	GRANULE_STATE_LAST = GRANULE_STATE_RTT
};

struct granule {
	/*
	 * @lock protects the struct granule itself. Take this lock whenever
	 * inspecting or modifying any other fields in this struct.
	 */
	spinlock_t lock;

	/*
	 * @state is the state of the granule.
	 */
	enum granule_state state;

	/*
	 * @refcount counts RMM and realm references to this granule with the
	 * following rules:
	 *  - The @state of the granule cannot be modified when @refcount
	 *    is non-zero.
	 *  - When a granule is mapped into the RMM, either the granule lock
	 *    must be held or a reference must be held.
	 *  - The content of the granule itself can be modified when
	 *    @refcount is non-zero without holding @lock.  However, specific
	 *    types of granules may impose further restrictions on concurrent
	 *    access.
	 */
	unsigned long refcount;
};

#endif /* GRANULE_TYPES_H */
