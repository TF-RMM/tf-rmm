.. SPDX-License-Identifier: BSD-3-Clause
.. SPDX-FileCopyrightText: Copyright TF-RMM Contributors.

############################
Change-log and Release notes
############################

******
v0.3.0
******

The following sections have the details on the release. This release has been
verified with `TF-A v2.9`_ release.

============================
New features in this release
============================

- Add support to create Realms which can make use of SVE, if present in
  hardware.

- Refactor the Stage 1 translation table library `lib/xlat` API to better
  fit RMM usage.  Also harden dynamic mapping via slot buffer mechanism by
  use of ``TRANSIENT`` software defined attribute.

- Add PMU support for Realms as described by RMM v1.0 Beta0 specification.

- Support getting DRAM info from the Boot manifest dynamically at runtime.

  * RMM can now support the 2nd DDR bank on FVP.

==========================
Build/Testing improvements
==========================

- Define a unit test framework using CppUTest for RMM.

- Add unittests for `granule`, `slot-buffer` and Stage 1 translation table lib
  `xlat`.

- Improve the ``fake-host`` mock capability by adding support for per PE sysreg
  emulation.

- Improve the VA to PA mock layer for ``fake-host``.

- Enable generation of gprof profiling data as part of ``fake-host`` runs.

- Improve the sample application on ``host-build`` platform by adding the cold
  attestation initialization flow. Also a sample minimal Realm create, run and
  destroy sequence is added to showcase the RMI calls involved.

- Further improvements to the unit test framework :

  * Restore the sysreg state between test runs so each test gets a known
    sysreg state.
  * Add capability to test assertions.
  * Support dynamic behaviour for test harness depending on requirement.
  * Add support for coverage report generation as part of unit test run.

- Build improvements in RMM:

  * Move mbedTLS build from configure stage to build stage.
  * Simplify QCBOR build.
  * Fix build artefact directory path to better cater to multi-config builds.

=========================
Bug fixes in this release
=========================

- Remove HVC exit handling from RMI_REC_ENTER handler.

- Fix parameter in measurement_extend_sha512().

- Fix issues in `lib/xlat` for some corner cases.

- Mask MTE capability from `id_aa64pfr1_el1` so that Realms
  can see that MTE is not supported.

- Add isb() after writes to `cptr_el2` system register.

- Fix the granule alignment check on granule_addr.

- Fix some cppcheck warnings.

- Properly handle errors for granule (un)delegate calls.

- Fix the incorrect bit map manipulation for tracking VMID for realms.

- Fix some incorrect Block mapping cases in Stage 2 translation.

=================
Upcoming features
=================

- RMM EAC Specification alignment.

- Support Self-Hosted Debug Realms.

- Support FEAT_PAuth for Realms and utilize the same for RMM.

- Support LPA2 for Stage 2 Realm translation tables.

- Threat model covering RMM data flows.

- Enable Bounded Model Checker (CBMC) for source analysis.

- Save and restore SME/SME2 context belonging to NS Host. This allows NS Host
  to make use of SME/SME2 when Realms are scheduled.

============================
Known issues and limitations
============================

- The size of ``RsiHostCall`` structure is 256 bytes in the implementation
  and aligns to `RMM Beta1 specification`_ rather than the 4 KB size
  specified in `RMM Beta0 specification`_.

- The `RMM Beta0 specification`_ does not require to have a CBOR bytestream
  wrapper around the cca-platform-token and cca-realm-delegated-token, but
  the RMM implementation does so and this is aligned with later versions
  of the RMM specification (Beta2 onwards).

- The RMM config ``RMM_FPU_USE_AT_REL2`` does not work as intended and
  this config is disabled by default. This will be fixed in a future release.

- When the ``RSI_ATTEST_TOKEN_CONTINUE`` call is interrupted and then resumed
  later by Host via ``RMI_REC_ENTER``, the original SMC is replayed again
  with the original arguments rather than returning ``RSI_INCOMPLETE`` error
  code to Realm. The result is that the interrupted RSI call is continued
  again till completion and then returns back to Realm with the appropriate
  error code.

.. _TF-A v2.9: https://git.trustedfirmware.org/TF-A/trusted-firmware-a.git/tag/?h=v2.9.0


******
v0.2.0
******

- This release has been verified with `TF-A v2.8`_ release.

- The release has the following fixes and enhancements:

   * Add support to render documentation on read-the-docs.
   * Fix the known issue with RSI_IPA_STATE_GET returning
     ``RSI_ERROR_INPUT`` for a `destroyed` IPA instead of
     emulating data abort to NS Host.
   * Fix an issue with RSI_HOST_CALL not returning back to Host
     to emulate a stage2 data abort.
   * Harden an assertion check for ``do_host_call()``.

- The other known issues and limitations remain the same as
  listed for v0.1.0_.

.. _TF-A v2.8: https://git.trustedfirmware.org/TF-A/trusted-firmware-a.git/tag/?h=v2.8.0

******
v0.1.0
******

-  First TF-RMM source release aligned to `RMM Beta0 specification`_.
   The specified interfaces : Realm Management Interface (RMI) and
   Realm Service Interface (RSI) are implemented which can attest
   and run Realm VMs as described by the `Arm CCA`_ Architecture.

=================
Upcoming features
=================

-  Support SVE, Self-Hosted Debug and PMU in Realms
-  Support LPA2 for Stage 2 Realm translation tables.
-  Threat model covering RMM data flows.
-  Enable Bounded Model Checker (CBMC) for source analysis.
-  Unit test framework based on :ref:`RMM Fake host architecture`.

============================
Known issues and limitations
============================

The following is a list of issues which are expected to be fixed in the future
releases of TF-RMM :

-  The size of ``RsiHostCall`` structure is 256 bytes in the implementation
   and aligns to `RMM Beta1 specification`_ rather than the 4 KB size
   specified in `RMM Beta0 specification`_.

-  The RSI_IPA_STATE_GET command returns error ``RSI_ERROR_INPUT`` for a
   `destroyed` IPA instead of emulating data abort to Host.

-  The `RMM Beta0 specification`_ does not require to have a CBOR bytestream
   wrapper around the cca-platform-token and cca-realm-delegated-token, but
   the RMM implementation does so.

---------------------------

.. _RMM Beta0 specification: https://developer.arm.com/documentation/den0137/1-0bet0/?lang=en
.. _RMM Beta1 specification: https://developer.arm.com/documentation/den0137/1-0bet1/?lang=en
.. _Arm CCA: https://www.arm.com/architecture/security-features/arm-confidential-compute-architecture
