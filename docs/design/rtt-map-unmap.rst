.. SPDX-License-Identifier: BSD-3-Clause
.. SPDX-FileCopyrightText: Copyright TF-RMM Contributors.

#####################
RTT map/unmap flows
#####################

This document describes the design of the range-aware RTT map and unmap
commands implemented in ``runtime/rmi/rtt_map.c`` and
``runtime/rmi/rtt_unmap.c``. It focuses on the common flow first, then
describes how the DATA, UNPROT and DEV flavours differ.

The commands covered here are:

- ``RMI_RTT_DATA_MAP`` and ``RMI_RTT_DATA_UNMAP`` for protected Realm data.
- ``RMI_RTT_UNPROT_MAP`` and ``RMI_RTT_UNPROT_UNMAP`` for unprotected NS
  mappings outside the Realm's |PAR|.
- ``RMI_RTT_DEV_MAP`` and ``RMI_RTT_DEV_UNMAP`` for device memory mappings.
- ``RMI_RTT_DATA_MAP_INIT`` as the single-page, measurement-aware data
  initialization path.

The basic invariant is that an RTT leaf entry is made visible as a usable
mapping only after its required ownership, cache and TLB maintenance is
complete. If that work must continue after the command returns, the entry
carries a software marker that blocks conflicting operations until completion.

************
Shared model
************

Address ranges
==============

The range-aware commands operate on IPA ranges that include ``base`` and
exclude ``top``. In other words, ``base`` is the first IPA in the range and
``top`` is the first IPA after the range. Output addresses (OAs) are supplied
or returned through RMI address range descriptors.

Map commands consume input descriptors:

- ``SINGLE`` puts one descriptor directly in ``oaddr``.
- ``LIST`` treats ``oaddr`` as an NS address of a descriptor list and uses
  ``LIST_COUNT`` descriptors, clipped so the list does not cross one granule.

Unmap commands produce output descriptors:

- ``NONE`` discards the freed OAs.
- ``SINGLE`` returns one descriptor in ``x[2]``.
- ``LIST`` copies descriptors to the NS list at ``oaddr`` and reports the
  number copied in ``x[3]``.

The descriptor size field determines the RTT level for a map operation. The
first descriptor selects the level for the whole call, and every later block
processed in the call must use the same level. For unmap, the walk itself
selects the level: if ``base`` is covered by a block entry, the command runs at
that block level; otherwise it runs at page level.

Progress model
==============

The implementation deliberately bounds the work done by each command
invocation:

- Map commands walk to the leaf table containing ``base`` and iterate forward
  within that table only.
- Unmap commands sweep one leaf table per invocation.
- If the requested range spans more tables, the host reissues the same command
  with the returned ``out_top`` as the new ``base``.

Partial progress is reported as success. If at least one block has been
processed and a later block fails validation, hits a table boundary, exhausts
the address list, or otherwise cannot continue in the same invocation, the
command returns ``RMI_SUCCESS`` and places the next IPA in ``x[1]``. If no
progress was made, the original error is returned.

SRO-backed slow operations yield cooperatively when a physical IRQ is pending.
A yielded operation returns ``RMI_INCOMPLETE`` with an SRO handle in ``x[1]``.
The host resumes it with ``RMI_OP_CONTINUE``. These map and unmap SROs are
not memory transferring and cannot be cancelled.

Locking and lifetime
====================

The entry paths lock the RD first, validate inputs and copy the primary
``s2tt_context``. They then lock the root RTT and release the RD lock. From
that point the RTT hierarchy lock pins the tree shape needed by the current
walk. RTT walks use the normal parent/child ordering described in
:doc:`locking`.

Leaf RTT granules that must survive across an SRO yield are pinned by
refcounts:

- DATA and DEV map take one refcount when they stamp the leaf entry. That
  refcount becomes the live mapping refcount after the entry is finalized.
- DATA and DEV unmap inherit the live mapping refcount and drop it only after
  deferred TLBI and drain work has completed.
- UNPROT unmap has no live data-granule refcount to inherit, so it takes a
  transient leaf refcount for each stamped entry and drops it at the end of the
  deferred work.

Unmap continue handlers do not need to re-lock the RD. The pinned leaf keeps
the RTT chain and RD alive, and the SRO context carries the cached MECID, leaf
IPA coordinates, VMIDs and DA state needed to finish the deferred work.

DATA and DEV map continue handlers do re-lock the RD before the leaf RTT, copy
the primary ``s2tt_context``, then release the RD once the leaf is locked.

Drain-pending markers
=====================

Some flows cannot finish all required TLB invalidations, cache maintenance and
backing-granule state changes before returning to the host. They mark the leaf
S2TTE with software-only fields:

- ``S2TTE_SW_DRAIN_PENDING_BIT`` records that deferred work still owns the
  entry.
- ``S2TTE_SW_TLBI_PENDING_BIT`` records that a stage-2 and possibly SMMU
  invalidation is still owed for the old mapping.
- The SRO handle identifies which in-flight SRO owns the marker.

The software fields are placed in the architectural OA field of an invalid
descriptor, which the unassigned-form constructors leave clear:

.. list-table::
   :header-rows: 1

   * - TTE bits
     - Field
     - Meaning
   * - ``[33]``
     - ``S2TTE_SW_TLBI_PENDING_BIT``
     - A deferred stage-2 and optional SMMU invalidation is owed.
   * - ``[32]``
     - ``S2TTE_SW_DRAIN_PENDING_BIT``
     - Deferred work still owns the entry.
   * - ``[31:16]``
     - ``S2TTE_SW_HANDLE``
     - 16-bit index of the owning SRO context in the global SRO pool.

``s2tte_set_drain_pending()`` stamps ``S2TTE_SW_DRAIN_PENDING_BIT`` and the
SRO handle together. ``s2tte_set_tlbi_pending()`` adds
``S2TTE_SW_TLBI_PENDING_BIT`` only for entries whose old form had a
hardware-valid mapping. The TLBI pass clears only the TLBI bit after issuing
the invalidation; the drain-pending bit and handle remain until the final clear
phase removes the marker.

Deferred walks must match ``S2TTE_SW_HANDLE`` against the current SRO handle
before acting on an entry. The handle is the ownership check for the marker:
after yields, other in-flight SROs may own different entries in the same leaf.
Without the match, one SRO could clear another operation's marker or TLBI bit,
or drop the leaf refcount that pins that operation's deferred state.

The marker is written while the entry is architecturally unassigned, so
hardware does not use the software fields as a translation. Other map, unmap
and RIPAS operations check the marker and return busy or retryable failures
instead of racing the deferred work.

********
Map flow
********

.. rubric:: High-level map flow

.. code-block:: text

   Host RMI_RTT_*_MAP(base, top, descriptors)
             |
             v
   Validate RD state, descriptor source, IPA range and PAR side
             |
             v
   Decode first descriptor level and walk to the leaf containing base
             |
             v
   For each entry in that leaf while IPA < top:
       pop one descriptor and run per-block checks
       DATA/DEV: stamp drain-pending entry and drain backing granules
                 yield via SRO if an IRQ is pending
       UNPROT:  write assigned_ns entry synchronously
       advance out_top
             |
             v
   Return a no-progress error, RMI_SUCCESS + out_top for terminal
   progress, or RMI_INCOMPLETE + SRO handle for a yielded DATA/DEV drain

.. rubric:: DATA/DEV map continue flow

.. code-block:: text

   Host RMI_OP_CONTINUE(handle)
             |
             v
   Find the sealed SRO context and dispatch to the DATA/DEV map continue handler
             |
             v
   Re-lock the RD and pinned leaf RTT, then map the leaf with the Realm MECID
             |
             v
   Resume the drain from the saved cursor:
       DATA: zero and transition backing granules from DELEGATED to DATA
       DEV:  transition dev_granules from DELEGATED to MAPPED, checking
             that all granules in the block have the same coherency type
             |
             v
   If an IRQ is pending:
       return RMI_INCOMPLETE and keep the drain-pending marker
   If rollback completes after a drain error:
       clear the marker, drop the leaf refcount and return error/partial progress
   If the drain completes:
       replace the marker with the assigned entry and return RMI_SUCCESS + next IPA

Common validation
=================

The range map commands share a validator. It checks that the Realm is ``NEW``
or ``ACTIVE``, that ``top`` is greater than ``base``, and that the descriptor
source is valid. The first descriptor is decoded to get the walk level and
block size.

The IPA range is then checked against the Realm IPA size and |PAR|:

- DATA and DEV map require the entire range to be inside the |PAR|.
- UNPROT map requires the entire range to be outside the |PAR|.

Per-block checks are done inside the walk loop because they depend on the
current descriptor and the remaining IPA range. Each block must match the call
level, fit before ``top``, be aligned to the block size, and fit within the PA
width when LPA2 is disabled. DATA and DEV map also require the expected
descriptor operation state; UNPROT map validates the resulting host NS S2TTE.

Common execution
================

After validation, the command locks the root RTT, releases the RD lock, walks
to ``base`` at the requested level, and maps the leaf RTT with the Realm MECID.
The loop then consumes one block descriptor per leaf slot until it reaches the
end of the leaf, the requested ``top``, the descriptor list, an error, or a
yield point.

``RMI_RTT_DATA_MAP`` and ``RMI_RTT_DEV_MAP`` reserve an SRO context before
validation because one block can take multiple per-granule transitions. If
they yield, the partially prepared block is resumed by ``RMI_OP_CONTINUE``.

``RMI_RTT_UNPROT_MAP`` has no SRO lifecycle. Each block is completed by one
leaf S2TTE write, so a pending IRQ only stops the loop and returns terminal
progress.

``RMI_RTT_DATA_MAP_INIT``
=========================

``RMI_RTT_DATA_MAP_INIT`` is the initialization-time special case. It maps one
delegated granule at page level, copies data from an NS source granule,
optionally measures the content, writes an ``assigned_ram`` S2TTE, takes the
leaf RTT refcount, and transitions the backing granule to DATA. It only accepts
a Realm in ``NEW`` state and does not use the range/SRO map machinery.

**********
Unmap flow
**********

.. rubric:: High-level unmap flow

.. code-block:: text

   Host RMI_RTT_*_UNMAP(base, top, output mode)
             |
             v
   Validate IPA range, PAR side and output-address mode
             |
             v
   Reserve SRO, snapshot S2 context / VMIDs, then walk to cur_base
             |
             v
   Sweep one leaf RTT:
       skip non-live entries, including drain-pending markers
       for live entries owned by the selected flavor:
           append the old OA to the output list
           write the matching unassigned_* entry with a drain-pending marker
           stamp TLBI_PENDING if the old entry was HW-valid
           advance cur_base
             |
             v
   Run deferred pipeline:
       TLBI pass for marked entries
       DATA/DEV backing-granule drain; UNPROT skips this phase
       clear drain markers and drop leaf refcounts
             |
             v
   Return a first-entry error, RMI_SUCCESS + out_top/output descriptors,
   or RMI_INCOMPLETE + SRO handle if deferred work yields

.. rubric:: Unmap continue flow

.. code-block:: text

   Host RMI_OP_CONTINUE(handle)
             |
             v
   Find the sealed SRO context and dispatch to the unmap continue handler
             |
             v
   Re-lock the pinned leaf RTT and map it with the cached Realm MECID
             |
             v
   Resume the deferred pipeline:
       TLBI pass for entries with this SRO handle and TLBI_PENDING
       DATA/DEV: transition queued backing granules back to DELEGATED
       UNPROT:   skip backing-granule drain
       clear drain-pending markers and drop leaf refcounts
             |
             v
   If an IRQ is pending during TLBI or backing-granule drain:
       return RMI_INCOMPLETE and keep the SRO context sealed
   If the pipeline completes:
       format output descriptors from the saved list and return RMI_SUCCESS + out_top

Sweep phase
===========

The common unmap runner walks to ``cur_base`` and sweeps one leaf table. For
each live entry owned by the selected flavour, it:

1. Extracts the old OA and appends it to the SRO output address list.
2. Replaces the live entry with the appropriate unassigned form.
3. Stamps the drain-pending marker and SRO handle.
4. Stamps ``TLBI_PENDING`` when the old entry had a hardware-valid mapping.
5. Advances ``cur_base`` to the next IPA.

Non-live entries are skipped. If no live entry was unmapped, the result still
advances ``x[1]`` over the contiguous run of non-live entries in the leaf so
the host can skip unused IPA ranges efficiently.

Some stop conditions are treated differently depending on whether they happen
on the first entry of the sweep. A table descriptor at a non-leaf level, a live
entry larger than the remaining range, a DATA entry with live auxiliary
mappings, or a wrong-flavour live entry is reported as an error when it is the
first entry. After prior progress or skipped entries, the sweep stops with
success and the host can reissue from the returned ``cur_base`` to observe the
condition as a first-entry error.

Deferred phase
==============

After the sweep, all unmap flavours run the same deferred pipeline:

1. Issue pending stage-2 TLB invalidations, and SMMU invalidations when device
   assignment is enabled, for entries marked with
   ``S2TTE_SW_TLBI_PENDING_BIT`` and a matching ``S2TTE_SW_HANDLE``. Clear the
   TLBI-pending bit after each invalidation.
2. Drain backing granules for DATA and DEV unmap. DATA transitions DATA
   granules back to DELEGATED with the required cache maintenance. DEV
   transitions MAPPED dev granules back to DELEGATED. UNPROT has no backing
   granule drain.
3. Clear the drain-pending markers and drop the leaf RTT refcount associated
   with each stamped entry whose ``S2TTE_SW_HANDLE`` matches the current SRO.

The first two phases are yieldable and sample for pending IRQs. If a yield
occurs, the SRO context keeps the output address list, drain cursors and leaf
metadata. ``RMI_OP_CONTINUE`` re-locks the leaf and resumes the same pipeline.

Result formatting
=================

Terminal unmap success is formatted from the output address list:

- ``NONE`` discards the list and reports only ``x[1]``.
- ``SINGLE`` encodes the first descriptor into ``x[2]``. The sweep stops at a
  PA discontinuity so the single descriptor remains contiguous.
- ``LIST`` copies as many descriptors as allowed to the host's NS output
  buffer and reports the copied count in ``x[3]``.

If the final copy to an NS list fails because the host changed the buffer's
state after validation, the unmap is not rolled back. The command reports zero
copied descriptors.

***********************
Flavour-specific detail
***********************

DATA map
========

DATA map consumes descriptors whose state is ``RMI_OP_MEM_DELEGATED`` and maps
them inside the |PAR|. A new mapping starts from an unassigned leaf entry. The
entry is stamped with the SRO handle and drain-pending bit, then each backing
granule is locked in DELEGATED state, zeroed under the Realm MECID, and
transitioned to DATA.

When all granules in the block have been drained, the leaf entry is finalized
with ``s2tte_create_assigned_unchanged()`` for the requested OA. If a backing
granule cannot be claimed, already transitioned granules are rolled back to
DELEGATED, the marker is cleared, and the leaf refcount is dropped.

An existing DATA mapping to the same OA is idempotent. An existing mapping to a
different OA, a non-unassigned entry, or an entry with a pending drain produces
an error or busy result.

DATA unmap
==========

DATA unmap accepts live ``assigned_ram``, ``assigned_empty`` and
``assigned_destroyed`` entries. It rejects device entries, because those must
be unmapped through the DEV command, and it rejects entries that still have
live auxiliary RTT mappings.

The replacement S2TTE preserves the DATA RIPAS state:

- ``assigned_ram`` becomes ``unassigned_destroyed`` and owes TLBI.
- ``assigned_empty`` becomes ``unassigned_empty`` and does not owe TLBI.
- ``assigned_destroyed`` becomes ``unassigned_destroyed`` and does not owe
  TLBI.

After TLBI, every freed DATA granule is transitioned back to DELEGATED with
cache maintenance. The old live mapping refcount on the leaf is dropped only
after this drain and marker clearing are complete.

UNPROT map
==========

UNPROT map maps descriptors outside the |PAR|. The current implementation does
not enforce the descriptor state field for this flavour. Instead, it builds a
constant attribute mask from ``MEMATTR`` and ``S2AP`` flags, using either
direct AP bits or indirect permission indexes according to the Realm S2
context. Each block combines that mask with the descriptor PA and validates the
resulting host NS S2TTE.

The leaf entry must be ``unassigned_ns``. A matching ``assigned_ns`` entry is
idempotent. There is no backing granule transition and no leaf refcount for the
NS memory itself; architectural protection prevents an NS PA from being used as
protected memory at the same time.

UNPROT unmap
============

UNPROT unmap accepts ``assigned_ns`` entries outside the |PAR|. Each freed
entry becomes ``unassigned_ns`` and always owes TLBI because ``assigned_ns`` is
a hardware-valid mapping.

There is no backing granule drain. The sweep takes a transient leaf refcount
for each stamped entry so the leaf remains pinned across any yield in the TLBI
pass. Those transient refcounts are dropped when the drain-pending markers are
cleared.

DEV map
=======

DEV map consumes descriptors whose state is ``RMI_OP_MEM_DELEGATED`` and maps
them inside the |PAR|. It also validates the VDEV granule, verifies that the
VDEV belongs to the target RD, and snapshots the VDEV address ranges before
walking the RTT. Every mapped block must fit entirely inside one of those VDEV
ranges.

The leaf entry must be ``unassigned_empty`` or ``unassigned_destroyed``. The
entry is stamped with the SRO handle and drain-pending bit, then each backing
``dev_granule`` is locked in DELEGATED state and transitioned to MAPPED. The
coherency type of the first ``dev_granule`` is recorded, and every later
granule in the block must match it.

When the block drain completes, the leaf entry is finalized with
``s2tte_create_assigned_dev_unchanged()``. If any backing dev granule cannot be
claimed, or if coherency types differ within the block, already transitioned
dev granules are rolled back to DELEGATED and the marker is cleared.

DEV unmap
=========

DEV unmap uses the common unmap runner but selects the DEV flavour. The sweep
accepts ``assigned_dev_dev``, ``assigned_dev_empty`` and
``assigned_dev_destroyed`` entries at any supported device mapping level. Other
live states produce ``RMI_ERROR_RTT(level)`` when they are encountered as the
first entry of the sweep.

The replacement S2TTE mirrors the DATA RIPAS-style behaviour for device
entries:

- ``assigned_dev_dev`` becomes ``unassigned_destroyed`` and owes TLBI.
- ``assigned_dev_empty`` becomes ``unassigned_empty`` and does not owe TLBI.
- ``assigned_dev_destroyed`` becomes ``unassigned_destroyed`` and does not owe
  TLBI.

After TLBI, every freed MAPPED dev granule is transitioned back to DELEGATED.
No data-cache maintenance is required for device memory, but the drain still
uses the same cooperative yield structure as DATA unmap.
