.. SPDX-License-Identifier: BSD-3-Clause
.. SPDX-FileCopyrightText: Copyright TF-RMM Contributors.

.. _locking_rmm:

RMM Locking Guidelines
=========================

This document outlines the locking requirements, discusses the implementation
and provides guidelines for a deadlock free |RMM| implementation. Further, the
document hitherto is based upon |RMM| Alpha-05 specification and is expected to
change as the implementation proceeds.

.. _locking_intro:

Introduction
-------------
In order to meet the requirement for the |RMM| to be small, simple to reason
about, and to co-exist with contemporary hypervisors which are already
designed to manage system memory, the |RMM| does not include a memory allocator.
It instead relies on an untrusted caller providing granules of memory used
to hold both meta data to manage realms as well as code and data for realms.

To maintain confidentiality and integrity of these granules, the |RMM|
implements memory access controls by maintaining awareness of the state of each
granule (aka Granule State, ref :ref:`locking_impl`) and enforcing rules on how
memory granules can transition from one state to another and how a granule can
be used depending on its state. For example, all granules that can be accessed
by software outside the |PAR| of a realm are in a specific state, and a granule
that holds meta data for a realm is in another specific state that prevents it
from being used as data in a realm and accidentally corrupted by a realm, which
could lead to internal failure in the |RMM|.

Due to this complex nature of the operations supported by the |RMM|, for example
when managing page tables for realms, the |RMM| must be able to hold locks on
multiple objects at the same time. It is a well known fact that holding multiple
locks at the same time can easily lead to deadlocking the system, as for example
illustrated by the dining philosophers problem [EWD310]_. In traditional
operating systems software such issues are avoided by defining a partial order
on all system objects and always acquiring a lower-ordered object before a
higher-ordered object. This solution was shown to be correct by Dijkstra
[EWD625]_. Solutions are typically obtained by assigning an arbitrary order
based upon certain attributes of the objects, for example by using the memory
address of the object.

Unfortunately, software such as the |RMM| cannot use these methods directly
because the |RMM| receives an opaque pointer from the untrusted caller and it
cannot know before locking the object if it is indeed of the expected state.
Furthermore, MMU page tables are hierarchical data structures and operations on
the page tables typically must be able to locate a leaf node in the hierarchy
based on single value (a virtual address) and therefore must walk the page
tables in their hierarchical order. This implies an order of objects in the same
Granule State which is not known by a process executing in the |RMM| before
holding at least one lock on object in the page table hierarchy. An obvious
solution to these problems would be to use a single global lock for the |RMM|,
but that would serialize all operations across all shared data structures in the
system and severely impact performance.


.. _locking_reqs:

Requirements
-------------

To address the synchronization needs of the |RMM| described above, we must
employ locking and lock-free mechanisms which satisfies a number of properties.
These are discussed below:

Critical Section
*****************

A critical section can be defined as a section of code within a process that
requires access to shared resources and that must not be executed while
another process is in a corresponding section of code [WS2001]_.

Further, access to shared resources without appropriate synchronization can lead
to **race conditions**, which can be defined as a situation in which multiple
threads or processes read and write a shared item and the final result depends
on the relative timing of their execution [WS2001]_.

In terms of |RMM|, an access to a shared resource can be considered as a list
of operations/instructions in program order that either reads from or writes to
a shared memory location (e.g. the granule data structure or the memory granule
described by the granule data structure, ref :ref:`locking_impl`). It is also
understood that this list of operations does not execute indefinitely, but
eventually terminates.

We can now define our desired properties as follows:

Mutual Exclusion
*****************

Mutual exclusion can be defined as the requirement that when one process is in a
critical section that accesses shared resources, no other process may be in a
critical section that accesses any of those shared resources [WS2001]_.

The following example illustrates how an implementation might enforce mutual
exclusion of critical sections using a lock on a valid granule data structure
`struct granule *a`:

.. code-block:: C

	struct granule *a;
	bool r;

	r = try_lock(a);
	if (!r) {
		return -ERROR;
	}
	critical_section(a);
	unlock(a);
	other_work();

We note that a process might fail to perform the `lock` operation on object `a`
and return an error or successfully acquire the lock, execute the
`critical_section()`, `unlock()` and then continue to make forward progress to
`other_work()` function.

Deadlock Avoidance
*******************

A deadlock can be defined as a situation in which two or more processes are
unable to proceed because each is waiting for one of the others to do something
[WS2001]_.

In other words, one or more processes are trying to enter their critical
sections but none of them make forward progress.

We can then define the deadlock avoidance property as the inverse scenario:

When one or more processes are trying to enter their critical sections, at least
one of them makes forward progress.

A deadlock is a fatal event if it occurs in supervisory software such as the
|RMM|. This must be avoided as it can render the system vulnerable to exploits
and/or unresponsive which may lead to data loss, interrupted service and
eventually economic loss.

Starvation Avoidance
*********************

Starvation can be defined as a situation in which a runnable process is
overlooked  indefinitely by the scheduler; although it is able to proceed, it is
never chosen [WS2001]_.

Then starvation avoidance can be defined as, all processes that are trying to
enter their critical sections eventually make forward progress.

Starvation must be avoided, because if one or more processes do not make forward
progress, the PE on which the process runs will not perform useful work and
will be lost to the user, resulting in similar issues like a deadlocked system.

Nested Critical Sections
*************************

A critical section for an object may be nested within the critical section for
another object for the same process.  In other words, a process may enter more
than one critical section at the same time.

For example, if the |RMM| needs to copy data from one granule to another
granule, and must be sure that both granules can only be modified by the process
itself, it may be implemented in the following way:

.. code-block:: C

	struct granule *a;
	struct granule *b;
	bool r;

	r = try_lock(a);
	if (!r) {
		return -ERROR;
	}

	/* critical section for granule a -- ENTER */

	r = try_lock(b);
	if (r) {
		/* critical section for granule b -- ENTER */
		b->foo = a->foo;
		/* critical section for granule b -- EXIT */
		unlock(b);
	}

	/* critical section for granule a -- EXIT */
	unlock(a);

.. _locking_impl:

Implementation
---------------

The |RMM| maintains granule states by defining a data structure for each
memory granule in the system. Conceptually, the data structure contains the
following fields:

* Granule State
* Lock
* Reference Count

The Lock field provides mutual exclusion of processes executing in their
critical sections which may access the shared granule data structure and the
shared meta data which may be stored in the memory granule which is in one of
the |RD|, |REC|, and Table states. Both the data structure describing
the memory granule and the contents of the memory granule itself can be accessed
by multiple PEs concurrently and we therefore require some concurrency protocol
to avoid corruption of shared data structures. An alternative to using a lock
providing mutual exclusion would be to design all operations that access shared
data structures as lock-free algorithms, but due to the complexity of the data
structures and the operation of the |RMM| we consider this too difficult to
accomplish in practice.

The Reference Count field is used to keep track of references between granules.
For example, an |RD| describes a realm, and a |REC| describes an execution
context within that realm, and therefore an |RD| must always exist when a |REC|
exists. To prevent the |RMM| from destroying an |RD| while a |REC| still exists,
the |RMM| holds a reference count on the |RD| for each |REC| associated with the
same realm, and only when all the RECs in a realm have been destroyed and
the reference count on an |RD| drops to zero, can the |RD| be destroyed and the
granule be repurposed for other use.

Based on the above, we now describe the Granule State field and the current
locking/refcount implementation:

* **Non-Secure (NS):** These are granules for which |RMM| does not prevent the
  |PAS| of the granule from being changed by another agent to any value. In
  this state, the granule content access is not protected by granule::lock, as
  it is always subject to reads and writes from Non-Realm worlds.

* **Delegated:** These are granules with memory only accessible by the |RMM|.
  The granule content is protected by granule::lock. No reference counts are
  held on this granule state.

* **Realm Descriptor (RD):** These are granules containing meta data describing
  a realm, and only accessible by the |RMM|. Granule content access is protected
  by granule::lock. A reference count is also held on this granule for each
  associated |REC| granule.

* **Realm Execution Context (REC):** These are granules containing meta data
  describing a virtual PE running in a realm, and are only accessible by the
  |RMM|. The execution content access is not protected by granule::lock, because
  we cannot enter a realm while holding the lock. Further, the following rules
  apply with respect to the granule's reference counts:

	- A reference count is held on this granule when a |REC| is running.

	- As |REC| cannot be run on two PEs at the same time, the maximum value
	  of the reference count is one.

	- When the |REC| is entered, the reference count is incremented
	  (set to 1) atomically while granule::lock is held.

	- When the |REC| exits, the reference counter is released (set to 0)
	  atomically with store-release semantics without granule::lock being
	  held.

	- The |RMM| can access the granule's content on the entry and exit path
	  from the |REC| while the reference is held.

* **Physical Device (PDEV):** These are granules containing metadata describing
  a physical device assigned through the device-assignment flow. Granule
  content access is protected by granule::lock. A reference count is held on
  this granule for each associated VDEV granule.

* **Virtual Device (VDEV):** These are granules containing metadata describing
  a virtual device assigned to a realm. Granule content access is protected by
  granule::lock. A reference is held to the associated RD and PDEV while the
  VDEV exists.

* **Translation Table:** These are granules containing meta data describing
  virtual to physical address translation for the realm, accessible by the |RMM|
  and the hardware Memory Management Unit (MMU). Granule content access is
  protected by granule::lock, but hardware translation table walks may read the
  RTT at any point in time. Multiple granules in the same RTT tree can only be
  locked in topological order from root to leaf. The topological order of
  concatenated root level RTTs is from the lowest address to the highest
  address.

  An operation that accesses both the Primary and an Auxiliary RTT tree must
  acquire the Primary RTT hierarchy before acquiring locks in the Auxiliary RTT
  tree. If locks in both trees are held simultaneously, the Primary tree locks
  precede the Auxiliary tree locks. Each RTT tree still follows its own
  root-to-leaf order, and Auxiliary trees are processed one at a time. The
  complete internal locking order for RTT granules is: RD -> [Primary RTT] ->
  ... -> RTT -> [Auxiliary RTT] -> ... -> RTT. A reference count is held on
  this granule for each entry in the RTT that refers to a granule:

	- Table s2tte.

	- Valid s2tte.

	- Valid_NS s2tte.

	- Assigned s2tte.

* **Data:** These are granules containing realm data, accessible by the |RMM|
  and by the realm to which it belongs. Granule content access is not protected
  by granule::lock, as it is always subject to reads and writes from within a
  realm. A granule in this state can be referenced by at most one entry in each
  RTT tree, and the RTT leaf entry must be locked before locking this granule
  through that reference. Only a single DATA granule can be locked at a time on
  a given PE. The complete internal locking order for DATA granules is:
  RD -> RTT -> RTT -> ... -> DATA. No reference counts are held on this granule
  type.

* **Auxiliary granules:** These are granules containing additional object state
  that does not fit in the primary object granule. REC_AUX, PDEV_AUX, VDEV_AUX
  and RD_AUX granules are locked only when the corresponding parent object or
  SRO flow already provides the necessary ownership.

* **Partial:** This intermediate state reserves a ``granule`` or
  ``dev_granule`` for an ongoing SRO. It is used during object creation or
  destruction, delegation or undelegation, coarse DATA map zeroing, and
  coarse DATA/DEV unmap invalidation and drain. Ownership persists across
  yields without retaining the granule lock. Other RMM operations cannot
  reuse the granule, and tracking transitions cannot replace its
  representation. The owning SRO acquires the granule lock when required,
  following the lock order for its object or memory operation.

* **Internal:** These are granules owned by |RMM| for internal use which do not
  yet have a more specific granule state. This state is currently used by the
  SMMU driver for donated PSMMU memory while it is staged for driver use, or
  after a driver object has been torn down and before the memory is reclaimed by
  the host. It is also used for Host-donated pages which back fine-tracking
  metadata. This includes self-describing pages whose backing PA lies in the
  tracking region represented by that metadata; their fine granules remain
  INTERNAL while the fine representation is active. No reference counts are
  held on this granule type.

* **PSMMU L2 Stream Table:** These are granules containing SMMUv3 Level 2
  Stream Tables. Granule content access is protected by the SMMUv3 device lock.
  A reference count is held on this granule for each configured Stream Table
  Entry in the L2 table. The L2 table can only be destroyed when the reference
  count is zero.

  When an SMMUv3 device lock and a PSMMU granule lock are both required, the
  SMMUv3 device lock must be acquired before locking granules in
  ``GRANULE_STATE_INTERNAL`` or ``GRANULE_STATE_PSMMU_ST_L2``. Donation and
  reclaim paths may lock ``GRANULE_STATE_INTERNAL`` granules without holding an
  SMMUv3 device lock, but must not acquire an SMMUv3 device lock while holding
  such a granule lock.


Locking
********

The |RMM| uses spinlocks along with the object state for locking implementation.
The lock provides similar exclusive acquire semantics known from trivial
spinlock implementations, however also allows verification of whether the locked
object is of an expected state.

The data structure for the spinlock can be described in C as follows:

.. code-block:: C

	typedef struct {
		unsigned int val;
	} spinlock_t;

This data structure can be embedded in any object that requires synchronization
of access, such as the `struct granule` described above.

The following operations are defined on spinlocks:

.. code-block:: C
	:caption: **Typical spinlock operations**

	/*
	 * Locks a spinlock with acquire memory ordering semantics or goes into
	 * a tight loop (spins) and repeatedly checks the lock variable
	 * atomically until it becomes available.
	 */
	void spinlock_acquire(spinlock_t *l);

	/*
	 * Unlocks a spinlock with release memory ordering semantics. Must only
	 * be called if the calling PE already holds the lock.
	 */
	void spinlock_release(spinlock_t *l);


The above functions should not be directly used for locking/unlocking granules,
instead the following should be used:

.. code-block:: C
	:caption: **Granule locking operations**

	/*
	 * Acquire an independently addressed Granule only while its state matches.
	 * Check the state before acquisition, throughout contention and after
	 * acquiring the lock. Return true with the lock held in expected_state,
	 * or false without holding it on a mismatch. The caller must keep the
	 * granule stable and acquire locks in the required order.
	 */
	bool granule_lock_on_state_match(struct granule *g,
					 unsigned char expected_state);

	/*
	 * Acquire through a protected reference with a guaranteed state after
	 * acquisition. Wait unconditionally for the lock, then assert the expected
	 * state and check its invariants. The caller must establish the locking
	 * order independently of the object's current state.
	 */
	void granule_lock(struct granule *g,
			  unsigned char expected_state);

	/*
	 * Finds and locks the granule at `addr` for `tracking_size`. Returns
	 * an encoded RMI_ERROR_TRACKING result containing `addr` if the tracking
	 * granularity does not match, or RMI_ERROR_INPUT if the address, size or
	 * Granule state is invalid. An incomplete tracking SRO returns RMI_BLOCKED.
	 */
	unsigned long tr_find_lock_granule(unsigned long addr,
					   unsigned long tracking_size,
					   unsigned char expected_state,
					   struct granule **g);

	/*
	 * Find two granules and lock them in lock order. Granules of
	 * the same type are locked in order of their address. Returns an RMI
	 * result and leaves no Granule locked on failure.
	 */
	unsigned long tr_find_lock_two_fine_granules(unsigned long addr1,
				       unsigned char expected_state1,
				       struct granule **g1,
				       unsigned long addr2,
				       unsigned char expected_state2,
				       struct granule **g2);

	/*
	 * Find three granules and lock them in lock order. Granules of
	 * the same type are locked in order of their address. Returns an RMI
	 * result and leaves no Granule locked on failure.
	 */
	unsigned long tr_find_lock_three_fine_granules(unsigned long addr1,
					 unsigned char expected_state1,
					 struct granule **g1,
					 unsigned long addr2,
					 unsigned char expected_state2,
					 struct granule **g2,
					 unsigned long addr3,
					 unsigned char expected_state3,
					 struct granule **g3);

	/*
	 * Obtain a pointer to a locked granule at `addr` which is unused
	 * (refcount = 0), if `addr` is a valid granule physical address and the
	 * state of the granule at `addr` is `expected_state`.
	 */
	int tr_find_lock_unused_fine_granule(unsigned long addr,
					      unsigned char expected_state,
					      struct granule **g);

.. code-block:: C
	:caption: **Granule unlocking operations**

	/*
	 * Release a spinlock held on a granule. Must only be called if the
	 * calling PE already holds the lock.
	 */
	void granule_unlock(struct granule *g);

	/*
	 * Sets the state and releases a spinlock held on a granule. Must only
	 * be called if the calling PE already holds the lock.
	 */
	void granule_unlock_transition(struct granule *g,
				       unsigned char new_state);


Reference Counting
*******************

The reference count is implemented using the **refcount** variable within the
granule structure to keep track of the references in between granules. For
example, the refcount is used to prevent changes to the attributes of a parent
granule which is referenced by child granules, ie. a parent with refcount not
equal to zero.

Race conditions on the refcount variable are avoided by either locking the
granule before accessing the variable or by lock-free mechanisms such as
Single-Copy Atomic operations along with ARM weakly ordered
ACQUIRE/RELEASE/RELAXED memory semantics to synchronize shared resources.

The following operations are defined on refcount:

.. code-block:: C
	:caption: **Read a refcount value**

	/*
	 * Single-copy atomic read of refcount variable with RELAXED memory
	 * ordering semantics. Use this function if lock-free access to the
	 * refcount is required with relaxed memory ordering constraints applied
	 * at that point.
	 */
	unsigned short granule_refcount_read(struct granule *g);

	/*
	 * Single-copy atomic read of refcount variable with ACQUIRE memory
	 * ordering semantics. Use this function if lock-free access to the
	 * refcount is required with acquire memory ordering constraints applied
	 * at that point.
	 */
	unsigned short granule_refcount_read_acquire(struct granule *g);

.. code-block:: C
	:caption: **Increment a refcount value**

	/*
	 * Increments the granule refcount by `val`. Must be called with the
	 * granule lock held.
	 */
	void granule_refcount_inc(struct granule *g, unsigned short val);

	/* Atomically increments the reference counter of the granule.*/
	void atomic_granule_get(struct granule *g);


.. code-block:: C
	:caption: **Decrement a refcount value**

	/*
	 * Decrements the granule refcount by `val`. Asserts if refcount can
	 * become negative. Must be called with the granule lock held.
	 */
	void granule_refcount_dec(struct granule *g, unsigned short val);

	/* Atomically decrements the reference counter of the granule. */
	void atomic_granule_put(struct granule *g);

	/*
	 * Atomically decrements the reference counter of the granule. Stores to
	 * memory with RELEASE semantics.
	 */
	void atomic_granule_put_release(struct granule *g);

.. code-block:: C
	:caption: **Directly access refcount value**

	/*
	 * Directly reads/writes the refcount variable. Must be called with the
	 * granule lock held.
	 */
	granule->refcount;

.. _locking_guidelines:

Guidelines
-----------

In order to meet the :ref:`locking_reqs` discussed above, this section
stipulates some locking and lock-free algorithm implementation guidelines for
developers.

Mutual Exclusion
*****************

The spinlock, acquire/release and atomic operations provide trivial mutual
exclusion implementations for |RMM|. However, the following general guidelines
should be taken into consideration:

	- Appropriate deadlock avoidance techniques should be incorporated when
	  using multiple locks.

	- Lock-free access to shared resources should be atomic.

	- Memory ordering constraints should be used prudently to avoid
	  performance degradation. For e.g. on an unlocked granule (e.g. REC),
	  prior to the refcount update, if there are associated memory
	  operations, then the update should be done with release semantics.
	  However, if there are no associated memory accesses to the granule
	  prior to the refcount update then release semantics will not be
	  required.


Deadlock Avoidance
******************

Deadlock avoidance is provided by defining a partial order on all objects in the
system where the locking operation will eventually fail if the caller tries to
acquire a lock of a different state object than expected. This means that no
two processes will be expected to acquire locks in a different order than the
defined partial order, and we can rely on the same reasoning for deadlock
avoidance as shown by Dijkstra [EWD625]_.

To establish this partial order, the objects referenced by |RMM| can be
classified into two categories:

#. **External**: A memory granule state belongs to the `external` class iff
   _any_ parameter in _any_ RMI command is an address of a granule which is
   expected to be in that state. The following memory granule states are
   `external`:

	- GRANULE_STATE_NS
	- GRANULE_STATE_DELEGATED
	- GRANULE_STATE_RD
	- GRANULE_STATE_REC
	- GRANULE_STATE_PDEV
	- GRANULE_STATE_VDEV

#. **Internal**: A memory granule state belongs to the `internal` class iff it
   is not an `external`. These are objects which are referenced from another
   object after that object is locked. The owning object or hierarchy defines
   the exact ownership rule for each `internal` state. The following memory
   granule states are `internal`:

	- GRANULE_STATE_RTT
	- GRANULE_STATE_DATA
	- GRANULE_STATE_REC_AUX
	- GRANULE_STATE_PDEV_AUX
	- GRANULE_STATE_VDEV_AUX
	- GRANULE_STATE_INTERNAL
	- GRANULE_STATE_PSMMU_ST_L2
	- GRANULE_STATE_RD_AUX
	- GRANULE_STATE_PARTIAL

.. _locking_granule_order:

We now state the locking guidelines for |RMM| as:

#. Independently-addressed memory granules must be locked in type order:
   RD, REC, PDEV, VDEV, RTT, DELEGATED, NS, followed by the remaining internal
   order below.
   The ``tr_find_lock_two_fine_granules()`` and
   ``tr_find_lock_three_fine_granules()`` helpers
   implement this ordering.

#. Independently-addressed memory granules of the same type must be locked in
   order of their physical address, starting with the lowest address.

#. An independently-addressed granule's state must be checked before
   acquisition, throughout contention and after acquiring its lock. A mismatch
   must stop acquisition without waiting for the granule to reach the expected
   state. Release any acquired locks and do not acquire further granules within the
   currently-executing RMM command.

#. Granules in the remaining `internal` states must be locked in order of
   state:

	- `DATA`
	- `REC_AUX`
	- `PDEV_AUX`
	- `VDEV_AUX`
	- `INTERNAL`
	- `PSMMU_ST_L2`
	- `RD_AUX`
	- `PARTIAL`

#. Granules in the same `internal` state must be locked in the
   :ref:`locking_impl` defined order for that specific state.

#. RTT granules are ordered by the RTT hierarchy rather than by physical
   address. RTT walks must lock the root table before child tables and use
   hand-over-hand locking. Concatenated root-level RTTs are entered from the
   lowest root address before locking the selected concatenated root. When an
   operation accesses both a Primary and an Auxiliary RTT tree, it must acquire
   the Primary RTT hierarchy before acquiring any Auxiliary RTT locks. If locks
   in both trees are held at the same time, the Primary tree locks precede the
   Auxiliary tree locks; each tree retains root-to-leaf ordering and Auxiliary
   trees are processed one at a time.

#. DATA granules and device granules whose ownership is obtained from a locked
   leaf RTT entry are locked under that leaf RTT according to the RTT
   map/unmap flow. Only one such backing granule is locked at a time. Lists of
   backing granules queued by RTT unmap are sorted in ascending physical
   address order before the backing granules are locked and drained.

#. Device granule states, `DEV_GRANULE_STATE_NS`,
   `DEV_GRANULE_STATE_DELEGATED` and `DEV_GRANULE_STATE_MAPPED`, are locked
   separately from memory granules by the device granule locking helpers.
   Memory granules must be locked before device granules.

#. A granule's state can be changed iff the granule is locked and the reference
   count is zero.

Starvation Avoidance
********************

Currently, the lock-free implementation for RMI.REC.Enter provides Starvation
Avoidance in |RMM|. However, for the locking implementation, Starvation
Avoidance is yet to be accomplished. This can be added by a ticket or MCS style
locking implementation [MCS]_.

Nested Critical Sections
************************

Spinlocks provide support for nested critical sections. Processes can acquire
multiple spinlocks at the same time, as long as the locking order is not
violated.

Object-map Epoch Counter
************************

Some operations must obtain an object address from a map owned by an |RD|
before they can acquire all the required granule locks in the prescribed
order. Such an operation reads the map while holding the RD granule lock,
releases that lock, and then reacquires the RD and referenced object granules
together. During this unlocked interval, the Host can remove or replace the
mapping. It can also reuse the same granule for a new object, so checking only
the cached address and granule state would not detect this scenario.

Each RD therefore contains a 64-bit ``obj_map_epoch`` counter. The counter is
the generation of the RD-owned object maps, which currently contain the
VDEV-ID-to-VDEV and MPIDR-to-REC mappings. An insertion or deletion in either
map increments the counter while the RD granule lock is held.

A consumer snapshots ``obj_map_epoch`` under the RD granule lock when it reads
a mapping. After acquiring the complete lock set, including the RD, it compares
the current epoch with the snapshot. If they differ, an object map changed
during the unlocked interval, so the consumer releases the acquired objects
and retries the lookup. If they match, the cached mapping has not changed and
the consumer can continue with the usual granule state and ownership checks.
The counter is deliberately coarse-grained: a change to an unrelated mapping
also causes a conservative retry.

At Realm creation, ``obj_map_epoch`` is initialized to 0. Every RD object-map
change advances this counter.

Tracking-region representation locking
***************************************

A tracking region can represent its memory with either one coarse granule
or a set of fine granules. These are ``struct granule`` objects for
conventional memory and ``struct dev_granule`` objects for device memory.
Both types can be coarse or fine. Each ``struct tracking_region`` object has
a reader-writer lock protecting the active representation.
Granule lookup paths take the lock for reading, while tracking-state
transitions take it for writing.

The following figure shows the two representations of one tracking region.
Only one representation is active at a time; the inactive representation is
prepared by a transition before it becomes active.

.. code-block:: text

   Coarse representation                 Fine representation

   +-------------------+                 +-----+-----+-----+-----+
   |        C          |       or        | F0  | F1  | ... | Fn  |
   +-------------------+                 +-----+-----+-----+-----+
   one granule for the region            one granule per physical Granule

   The tracking-region reader-writer lock protects the choice between C and
   F0...Fn.  The selected granule's Granule lock protects that granule.

Tracking configuration, activation and queries share a global layout spinlock.
A query holds it while locating a region and reading its state, so the layout
cannot change during the query.

Granule lookups follow the :ref:`locking-order rules <locking_granule_order>`:
conventional Granule locks follow the global state and physical address order,
RTTs follow their hierarchy, and device Granule locks follow ascending physical
addresses. Each lookup acquires its own tracking-region reader, selects the
active representation, locks the granule, then releases the reader. The acquired
granule lock pins that representation until the caller releases it.

Use ``tr_find_lock_*()`` for unowned PAs. Unlocked lookups do not pin metadata.
Owned-granule helpers require ownership that pins both state and representation;
they must not bypass validation of an unowned PA.

``tr_find_lock_two_fine_granules()`` and
``tr_find_lock_three_fine_granules()`` lock independent fine granules by state,
then by ascending PA within each state. Coarse tracking causes them to release
earlier locks and return ``RMI_ERROR_TRACKING``. RTT, DATA and auxiliary
granules follow their hierarchy or ownership rules.

A tracking API may acquire its temporary region reader while the caller holds
earlier Granule locks. Readers may also nest inside the tracking implementation.
This is safe because tracking writers never wait for readers or Granule locks
while retaining the reader gate:

#. Try the region writer. Acquire the reader gate and inspect the reader count
   while the gate excludes new readers. If either the gate or an existing
   reader is busy, return ``RMI_BUSY`` without retaining the gate.
#. Try each source granule lock once. On contention, release the acquired
   granule prefix and the region writer, then return ``RMI_BUSY``.
#. Once all source granules are locked and valid, initialize the inactive
   representation, publish the new tracking state, release the source locks
   and finally release the region writer. This section must not wait for
   another Granule lock.

Tracking SROs use the same source locking and validation before publishing a
pending marker. A failed claim publishes no marker. An SRO retaining donated
metadata yields ``RMI_INCOMPLETE`` on contention. Live fine objects and
``PARTIAL`` ownership prevent transition claims; unlocked coarse DATA/MAPPED
granules can split.

A reader arriving while the writer holds the region lock waits at the gate.
After the writer releases the lock, the reader selects whichever representation
is then active. If the writer backed off, the representation is unchanged.
An admitted reader prevents writer acquisition.

For example, an RMI caller can hold a coarse granule and make another lookup
in the same region while a tracking transition attempts to split it:

.. code-block:: text

   RMI CPU                                    Transition CPU
   -------                                    --------------
   read_lock(region)
   select and lock coarse granule C
   read_unlock(region)                        try_write_lock(region): succeeds
                                              try_lock(C): fails
                                              write_unlock(region)
                                              return RMI_BUSY
   read_lock(region): can proceed
   perform later lookup in Granule lock order
   read_unlock(region)
   unlock granules                            retry can now complete

The same rule breaks a cycle when a different reader waits for an RMI caller's
Granule: that reader prevents writer acquisition, so the RMI caller can still
enter the reader gate to finish its own lookups. State-aware Granule locking
remains necessary to preserve the state and address order between ordinary
callers; writer backoff does not replace that ordering.

See :doc:`dynamic-granule-management` for storage, allocation, allowed
transitions, reference counts and RMI behavior. Map/unmap address-list ordering
and SRO behavior are described in :doc:`rtt-map-unmap`.

References
----------

.. [EWD310] Dijkstra, E.W. Hierarchical ordering of sequential processes.
	EWD 310.

.. [EWD625] Dijkstra, E.W. Two starvation free solutions to a general exclusion
	problem. EWD 625.

.. [MCS] Mellor-Crummey, John M. and Scott, Michael L. Algorithms for scalable
	synchronization on shared-memory multiprocessors. ACM TOCS, Volume 9,
	Issue 1, Feb. 1991.

.. [WS2001] Stallings, W. (2001). Operating systems: Internals and design
	principles. Upper Saddle River, N.J: Prentice Hall.
