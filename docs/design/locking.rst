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
same realm, and only when the all the RECs in a realm have been destroyed and
the reference count on an |RD| drops to zero, can the |RD| be destroyed and the
granule be repurposed for other use.

Based on the above, we now describe the Granule State field and the current
locking/refcount implementation:

* **UnDelegated:** These are granules for which |RMM| does not prevent the |PAS|
  of the granule from being changed by another agent to any value.
  In this state, the granule content access is not protected by granule::lock,
  as it is always subject to reads and writes from Non-Realm worlds.

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

* **Translation Table:** These are granules containing meta data describing
  virtual to physical address translation for the realm, accessible by the |RMM|
  and the hardware Memory Management Unit (MMU). Granule content access is
  protected by granule::lock, but hardware translation table walks may read the
  RTT at any point in time. Multiple granules in this state can only be locked
  at the same time if they are part of the same tree, and only in topological
  order from root to leaf. The topological order of concatenated root level RTTs
  is from the lowest address to the highest address. The complete internal
  locking order for RTT granules is: RD -> [RTT] -> ... -> RTT. A reference
  count is held on this granule for each entry in the RTT that refers to a
  granule:

	- Table s2tte.

	- Valid s2tte.

	- Valid_NS s2tte.

	- Assigned s2tte.

* **Data:** These are granules containing realm data, accessible by the |RMM|
  and by the realm to which it belongs. Granule content access is not protected
  by granule::lock, as it is always subject to reads and writes from within a
  realm. A granule in this state is always referenced from exactly one entry in
  an RTT granule which must be locked before locking this granule. Only a single
  DATA granule can be locked at a time on a given PE. The complete internal
  locking order for DATA granules is: RD -> RTT -> RTT -> ... -> DATA.
  No reference counts are held on this granule type.


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
	 * Acquires a lock (or spins until the lock is available), then checks
	 * if the granule is in the `expected_state`. If the `expected_state`
	 * is matched, then returns `true`. Otherwise, releases the lock and
	 * returns `false`.
	 */
	bool granule_lock_on_state_match(struct granule *g,
					 enum granule_state expected_state);

	/*
	 * Used when we're certain of the state of an object (e.g. because we
	 * hold a reference to it) or when locking objects whose reference is
	 * obtained from another object, after that objects is locked.
	 */
	void granule_lock(struct granule *g,
			  enum granule_state expected_state);

	/*
	 * Obtains a pointer to a locked granule at `addr` if `addr` is a valid
	 * granule physical address and the state of the granule at `addr` is
	 * `expected_state`.
	 */
	struct granule *find_lock_granule(unsigned long addr,
					  enum granule_state expected_state);

	/* Find two granules and lock them in order of their address. */
	return_code_t find_lock_two_granules(unsigned long addr1,
					     enum granule_state expected_state1,
					     struct granule **g1,
					     unsigned long addr2,
					     enum granule_state expected_state2,
					     struct granule **g2);

	/*
	 * Obtain a pointer to a locked granule at `addr` which is unused
	 * (refcount = 0), if `addr` is a valid granule physical address and the
	 * state of the granule at `addr` is `expected_state`.
	 */
	struct granule *find_lock_unused_granule(unsigned long addr,
						 enum granule_state
						 expected_state);

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
				       enum granule_state new_state);


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
	unsigned long granule_refcount_read_relaxed(struct granule *g);

	/*
	 * Single-copy atomic read of refcount variable with ACQUIRE memory
	 * ordering semantics. Use this function if lock-free access to the
	 * refcount is required with acquire memory ordering constraints applied
	 * at that point.
	 */
	unsigned long granule_refcount_read_acquire(struct granule *g);

.. code-block:: C
	:caption: **Increment a refcount value**

	/*
	 * Increments the granule refcount. Must be called with the granule
	 * lock held.
	 */
	void __granule_get(struct granule *g);

	/*
	 * Increments the granule refcount by `val`. Must be called with the
	 * granule lock held.
	 */
	void __granule_refcount_inc(struct granule *g, unsigned long val);

	/* Atomically increments the reference counter of the granule.*/
	void atomic_granule_get(struct granule *g);


.. code-block:: C
	:caption: **Decrement a refcount value**

	/*
	 * Decrements the granule refcount. Must be called with the granule
	 * lock held.
	 */
	void __granule_put(struct granule *g);

	/*
	 * Decrements the granule refcount by `val`. Asserts if refcount can
	 * become negative. Must be called with the granule lock held.
	 */
	void __granule_refcount_dec(struct granule *g, unsigned long val);

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

#. **External**: A granule state belongs to the `external` class iff _any_
   parameter in _any_ RMI command is an address of a granule which is expected
   to be in that state. The following granule states are `external`:

	- GRANULE_STATE_NS
	- GRANULE_STATE_DELEGATED
	- GRANULE_STATE_RD
	- GRANULE_STATE_REC

#. **Internal**: A granule state belongs to the `internal` class iff it is not
   an `external`. These are objects which are referenced from another
   object after that object is locked. Each `internal` object should be
   referenced from exactly one place. The following granule states are
   `internal`:

	- GRANULE_STATE_RTT
	- GRANULE_STATE_DATA

We now state the locking guidelines for |RMM| as:

#. Granules expected to be in an `external` state must be locked before locking
   any granules in an `internal` state.

#. Granules expected to be in an `external` state must be locked in order of
   their physical address, starting with the lowest address.

#. Once a granule expected to be in an `external` state has been locked, its
   state must be checked against the expected state. If these do not match, the
   granule must be unlocked and no further granules may be locked within the
   currently-executing RMM command.

#. Granules in an `internal` state must be locked in order of state:

	- `RTT`
	- `DATA`

#. Granules in the same `internal` state must be locked in the
   :ref:`locking_impl` defined order for that specific state.

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
