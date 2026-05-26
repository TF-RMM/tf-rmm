.. SPDX-License-Identifier: BSD-3-Clause
.. SPDX-FileCopyrightText: Copyright TF-RMM Contributors.

################################################
ASID Management and TLB Maintenance for EL0 Apps
################################################

************
Introduction
************

This document describes the Address Space Identifier (ASID) management and
Translation Lookaside Buffer (TLB) maintenance strategy used by TF-RMM for
EL0 apps (see :ref:`el0_apps_in_rmm`). EL0 apps run deprivileged using
FEAT_VHE. Each app is assigned a unique ASID, and each instance of an
app has its own isolated address space (page tables) sharing that ASID.

Correct ASID management and TLB maintenance is critical to ensure:

- Isolation between different app address spaces.
- Isolation between app address spaces and the RMM core address space.
- No stale or conflicting TLB entries exist after TTBR switches.
- System register fields cached in TLB entries are correctly invalidated
  when modified.

***************************
Translation Regime Overview
***************************

RMM uses the EL2&0 translation regime with VHE enabled. Two VA ranges are
available:

+-------------------+----------------+------------------+-------------------+
| VA Range          | TTBR           | Used By          | ASID Source       |
+===================+================+==================+===================+
| Low VA (TTBR0)    | TTBR0_EL2      | RMM core         | N/A (TCR_EL2.A1)  |
+-------------------+----------------+------------------+-------------------+
| High VA (TTBR1)   | TTBR1_EL2      | EL0 apps / RMM   | TTBR1_EL2[63:48]  |
+-------------------+----------------+------------------+-------------------+

``TCR_EL2.A1`` is set to 1, which means the active ASID is sourced from
TTBR1_EL2 bits [63:48].

The Low VA range (TTBR0) is configured as global (nG = 0) and shared across
all PEs — it uses the CnP (Common not Private) bit, and since all entries are
global the ASID is ignored for TLB lookup (ARM ARM rule RQGKGF), so its TLB
entries are identical system-wide. In contrast, the High VA range (TTBR1) is
PE-local: each PE may have a different TTBR1 value (with a different ASID and
page table base) depending on which app instance is active. This distinction
is important for TLB maintenance — High VA invalidations only need to target
the local PE.

High VA Usage by RMM Core (Slot Buffer)
========================================

When no EL0 app is executing, TTBR1_EL2 points to the RMM core's own High VA
page tables (ASID = 0, CnP = 0). The High VA region is used for:

1. **Slot buffer**: Dynamic transient mappings used by RMM
   to temporarily access granule memory (NS data, Realm Descriptors, RECs,
   RTTs, etc.). Each slot is one 4KB page at a fixed VA computed as
   ``SLOT_VIRT + (slot_index * GRANULE_SIZE)``.

2. **Per-CPU stacks**: General stack and exception handler stack, each with a
   guard page gap.

The slot buffer translation tables are **per-CPU private** (CnP = 0) — each PE
has its own last-level page table allowing independent dynamic mappings without
cross-CPU coordination. All high VA mappings — both RMM core (slot buffer,
stacks) and EL0 app — use the **nG (non-global)** bit (``MT_NG``), making
their TLB entries ASID-tagged.

TTBR1 Time-Multiplexing
========================

The High VA region is time-multiplexed between RMM core and EL0 apps:

+---------------------+-------+---------------------------------------------+
| TTBR1 Active Owner  | ASID  | High VA Contains                            |
+=====================+=======+=============================================+
| RMM core            | 0     | Slot buffer + per-CPU stacks                |
+---------------------+-------+---------------------------------------------+
| EL0 app instance    | 1-N   | App context + text/RO/RW/BSS + heap/stack   |
+---------------------+-------+---------------------------------------------+

When switching TTBR1 to an app, the slot buffer becomes inaccessible. This
imposes a critical constraint: **all slot buffer operations must complete
before calling** ``run_app()``. After returning from the app, the RMM TTBR1
is restored and slot buffer access resumes.

Since both the RMM core High VA and app High VA contexts set CnP = 0, their
page table entries are never shared across PEs (ARM ARM rule RFWQJZ,
D8.16.3.4). This ensures that TLB entries from one PE's slot buffer or app
instance never appear on another PE.

***************
ASID Allocation
***************

ASIDs are allocated statically at compile time. Each app binary contains a
unique ``app_id`` in its header (see ``struct app_header``), and this
value is used directly as the ASID. The IDs are defined in each app's
CMakeLists.txt and in ``app/common/framework/include/app.h``.

+------------------------+------+-------------------------------------------+
| Component              | ASID | Notes                                     |
+========================+======+===========================================+
| RMM core               | 0    | Defined as ``RMM_ASID`` in xlat_contexts.h|
+------------------------+------+-------------------------------------------+
| Random app             | 103  | ``RMM_RANDOM_APP_ID``                     |
+------------------------+------+-------------------------------------------+
| Device Assignment app  | 110  | ``RMM_DEV_ASSIGN_APP_ID``                 |
+------------------------+------+-------------------------------------------+
| Attestation app        | 211  | ``ATTESTATION_APP_ID``                    |
+------------------------+------+-------------------------------------------+

The RMM core's ASID (0) is embedded into TTBR1_EL2 during
``xlat_arch_setup_mmu_cfg`` via the ``INPLACE(TTBRx_EL2_ASID, ctx_cfg->asid)``
macro, placing it in bits [63:48] of the TTBR value.

For EL0 apps, the ASID is programmed dynamically at app entry time: the
``run_app`` assembly code loads the app's pre-computed TTBR1_EL2 value (which
already contains the app's ASID in bits [63:48]) from
``struct app_data_cfg.mmu_config`` and writes it to TTBR1_EL2 via
``msr ttbr1_el2``. This effectively switches the active ASID to the app's
``app_id`` for the duration of app execution.

The ASID field width is IMPLEMENTATION DEFINED as either 8 or 16 bits
(``ID_AA64MMFR0_EL1.ASIDBits``), supporting up to 256 or 65536 unique values
respectively — far exceeding the current requirement.

.. _el0_app_tlb_asid_instance_model:

Instance Model
==============

Each app may have multiple instances; for example, instances may be allocated
per CPU, per REC, or per device depending on the app. All instances of the
same app share the same ASID. The translation tables differ per instance
(different stack, heap, and shared page mappings), but the ASID remains
constant for a given app_id.

For details on instance memory layout and initialization, see
:ref:`el0_app_instance`.

The number and lifetime of instances varies by app:

- **Random app**: One instance per CPU (statically allocated).
- **Attestation app**: One instance per CPU (for hash accumulations during
  realm creation) **and** one instance per REC (for signing the CCA token).
  The per-REC instance uses memory from REC auxiliary pages.
- **Device Assignment app**: One instance per PDEV (physical device). The
  instance uses memory from PDEV auxiliary pages.

Even though each app creates and owns instances differently, the ASID
remains the same for all instances of a given app — it is always derived
from the app's ``app_id``. The TLB maintenance strategy is unaffected
because only one instance can be active on a PE at any time, and the
TLBI targets the app's ASID before each TTBR switch.

**********************************
TLB Maintenance on TTBR1 Switching
**********************************

When switching TTBR1_EL2 between the RMM core and an app (or between different
apps), TLB maintenance is required to prevent:

1. **Conflicting TLB entries**: If TLB entries cached from different
   translation tables coexist for the same ASID, the PE may exhibit
   UNPREDICTABLE behavior (ARM ARM rule RFVQCK).

2. **Stale entries**: Old TLB entries from a previous TTBR value being used
   after the switch.

Entry to EL0 App (run_app)
==========================

The sequence when entering an app is:

.. code-block::

   /* 1. Switch TTBR1_EL2 to app page tables */
   ldr     x1, [x0, #APP_TTBR1_EL2_OFFSET]
   msr     ttbr1_el2, x1

   /* 2. ISB deferred until after vbar_el2 write (no high-VA access before) */
   msr     vbar_el2, <app_vectors>
   isb

No TLBI is required on entry because the ``back_from_el0`` exit path always
performs ``TLBI ASIDE1`` for the app ASID, guaranteeing that no stale entries
for the app ASID exist when re-entering.

No DSB is required before the TTBR switch: the ARM ARM defines "Same Location"
as same Physical Address (B2.3.4), so same-PE coherence is guaranteed across
different VAs mapping the same PA without explicit barriers.

No explicit ISB is required immediately after the ``msr ttbr1_el2`` because no
memory access through the new TTBR1 mapping occurs until after the subsequent
ISB. Speculative table walks using the new TTBR1 value are benign since no
conflicting entries can exist (guaranteed by the exit-path TLBI).

Return from EL0 App (back_from_el0)
====================================

The sequence when returning to RMM is:

.. code-block:: asm

   /* 1. Extract app ASID from current TTBR1 */
   mrs     x3, ttbr1_el2
   and     x3, x3, #(~((1 << 48) - 1))    // Extract ASID

   /* 2. Restore RMM TTBR1 */
   ldr     x2, [x1, #RMM_TTBR1_EL2_OFFSET]
   msr     ttbr1_el2, x2
   isb

   /* 3. Invalidate TLB for the app ASID */
   tlbi    aside1, x3                       // Invalidate by ASID
   dsb     nsh                              // Ensure completion
   isb                                      // Context synchronization

The TTBR1 is restored **before** the TLBI to ensure that it is not possible
to allocate new TLB entries for the app ASID after completion of the TLBI.
If the TLBI were issued first (while TTBR1 still points to the app tables),
speculative table walks could re-populate TLB entries for the app ASID between
the TLBI and the TTBR switch, defeating the invalidation. The ISB between the
TTBR1 restore and the TLBI context-synchronizes the TTBR change, ensuring
subsequent speculative walks use the new TTBR1 value (RMM's ASID 0) and cannot
re-populate entries for the app ASID.

The TLBI after the TTBR restore cleans up stale app TLB entries so they do not
persist until the next ``run_app`` invocation.

*************************************
TCR_EL2.E0PD0 — Static Configuration
*************************************

``TCR_EL2.E0PD0`` controls whether unprivileged (EL0) accesses to the TTBR0
(low VA) range generate a Translation Fault without performing a table walk.
Setting this bit prevents EL0 apps from accessing RMM core memory mapped via
TTBR0.

This field is permitted to be cached in TLB entries. If toggled dynamically,
TLB maintenance (TLBI + DSB after a context synchronization event) would be
required to ensure the new value is observed.

**Design decision:** ``TCR_EL2.E0PD0`` is set **statically** during MMU
initialization in ``xlat_arch_setup_mmu_cfg()`` and is never modified at
runtime. This eliminates the need for any TLB maintenance related to this
field during app entry/exit, and provides a constant security guarantee that
EL0 code cannot access the low VA range.

The bit is set alongside other static TCR fields:

.. code-block:: c

   tcr |= TCR_EL2_AS | TCR_EL2_HPD0 | TCR_EL2_HPD1 | TCR_EL2_E0PD0;

*********************
Scope of Invalidation
*********************

The current implementation uses ``TLBI ASIDE1`` which invalidates **all** TLB
entries matching the specified ASID (for the current VMID, EL2 regime). This
is a conservative approach that ensures correctness.

Potential optimizations (not yet implemented):

1. **Per-CPU ASID optimization**: If CPU-affine app instances used a distinct
   ASID (e.g., with MSB set), TLB invalidation for those instances can be
   omitted entirely since the same instance always runs on the same CPU and
   the TLB entries remain valid across invocations.

2. **VA-range TLBI for instance-specific pages**: Since text, RO, and RW/BSS
   sections are shared across all instances of an app, only instance-specific
   pages (stack, heap, shared page) change between invocations. A targeted
   ``TLBI VAE1`` for only those pages would reduce TLB pressure. However,
   this optimization is only feasible when the app uses a single L3 page table
   hierarchy (no intermediate levels). If intermediate translation table levels
   exist and their walk entries are cached in the TLB, a VA-range TLBI would
   not invalidate those cached intermediate entries.

*******************
DSB Scope Selection
*******************

All TLB invalidations use ``DSB NSH`` (Non-Shareable domain) and the TLBI
operations themselves are CPU-local (non-broadcast) because:

- EL0 apps are strictly CPU-local — an app instance is never migrated between
  CPUs while active.
- TTBR1_EL2 is banked per-PE in the EL2&0 regime.
- The ASID namespace is not shared across PEs for app contexts (each PE manages
  its own TLB entries for app ASIDs independently).
- ``TLBI ASIDE1`` (without the ``IS`` suffix) only invalidates TLB entries on
  the local PE — it is not broadcast to other PEs. This is sufficient because
  only the local PE can hold TLB entries for the app ASID being switched.

This avoids the cost of an Inner Shareable (ISH) DSB which would require
cross-CPU synchronization, and avoids broadcast TLBI overhead on other cores.

*****************
Summary of Rules
*****************

1. **On entry (run_app)**: No TLBI needed — the exit path guarantees no
   stale entries exist for the app ASID.

2. **On exit (back_from_el0)**: Restore RMM TTBR1 **first**, followed by
   TLBI + DSB + ISB to clean up stale app entries. No RFVQCK conflict exists
   because RMM uses a different ASID (0).

3. **All TLB operations are PE-local**: non-broadcast TLBI, NSH-scoped DSB.

4. **TCR_EL2.E0PD0** is set once at init — never toggled at runtime.
