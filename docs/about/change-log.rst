.. SPDX-License-Identifier: BSD-3-Clause
.. SPDX-FileCopyrightText: Copyright TF-RMM Contributors.

############################
Change-log and Release notes
############################

******
v0.5.0
******

The following sections have the details on the release. This release has been
verified with `TF-A v2.11`_ release.

============================
New features in this release
============================

- Enabled FEAT_DIT for RMM execution.

- Added support for FEAT_LPA2 to S2TT component.

  *  This enables creating Realms with LPA2 support.

- Introduced the dynamic console framework for RMM.

  *  This framework allows EL3 to dynamically describe the console for use by
     RMM and configure the console during boot.

- Introduced the ``arm`` platform layer.

  *  The common ``arm`` platform is added which can be used
     by any compatible SoC. This allows reuse of code across multiple
     SoCs and possibly a single binary across them.
  *  Both FVP and QEMU are migrated to this common ``arm`` platform layer and
     only requires platform specific defconfig file to configure RMM.

======================================
Bug fixes/improvements in this release
======================================

- Improvements to Exception handling in RMM.

  *  Separated Exception Stack for RMM exceptions.
  *  Added crashlog of register values for R-EL2 exceptions.
  *  Added backtrace to exception handler.

- Improvements to S2TT component in RMM.

  *  Several optimizations to S2TT component are done.
  *  MISRA errors are fixed.
  *  The component is moved to its own folder in `lib`.
  *  All S2TT APIs now accept `realm_s2_context` as an argument.
  *  Issue related to the NS attributes not being checked during FOLD is fixed.

- Reduced the memory required for `struct granule`.

  *  The data structure is optimized such that it is 4 bytes in size
     compared to the previous 16 bytes.

- Use DC ZVA for granule zeroing instead of memset().

- Allow RTT FOLD to level 1 as mandated by RMM specification.

- Additional clang-tidy checks are enabled for the project.

  *  The clang-tidy configuration can be found in ``.clang-tidy`` file at the
     the root of the source tree.
  *  The errors flagged by the static analysis are corrected and the project
     expects 0 errors for clang-tidy checks.

- Enabled alignment fault check in RMM.

  *  Enabled Alignment fault check in SCTLR_EL2 register when
     RMM_FPU_USE_AT_REL2=OFF. Associated fixes for some data structures
     are also done as part of this work.

- Fixed MISRA C 2012 violations detected by Coverity scan.

- Fix to report accurate breakpoint and watchpoint numbers via RMI_FEATURES.

- Fix to properly initialize MDCR_EL2.HPMN for each REC.

- Fix to inject SEA for Realm access outside IPA space.

- Allocate parameters for RIM extension on stack rather than global data.

- Fixed spinlock_acquire() implementation on the fake_host architecture.

- Fix to add +nosve compiler option to prevent compiler from generating SVE
  instructions.

- Fix to use -march=armv9.2 option to build RMM depending on compiler support.

- Fixed build issue for Yocto by adding system includes to the CMAKE search
  path.

- Fix to retry RDNR instruction if it fails during attestation initialization.

- Refactored lib/realm component. This component is split now into 2 new
  libraries: `lib/granule` and `lib/slot_buf`.

- Fix to make RMI_INJECT_SEA flag mutually exclusive to RMI EMUL_MMIO flag
  during RMI_REC_ENTER.

==================================
Build/Testing/Tooling improvements
==================================

- Extended CBMC analysis to more RMI commands:

  *  Added CBMC testbench and analysis for the following RMI APIs:
     RMI_VERSION, RMI_FEATURES, RMI_REALM_ACTIVATE, RMI_REALM_DESTROY,
     RMI_REC_AUX_COUNT, RMI_REC_DESTROY.
  *  Increased CBMC coverage for RMI_DELEGATE and RMI_UNDELEGATE APIs.
  *  Integrated cbmc-viewer tool to CBMC analysis.
  *  Added option to build with GCC.
  *  Added tooling to detect CBMC result differences. Added a script that
     compares the CBMC results to the baseline summary and this helps to
     detect additional CBMC failures from baseline results.
  *  An application note is added to the documentation to describe
     the CBMC integration with the project.

- Improvements to unit-tests in RMM.

  *  Added unit testing framework and unit tests to SIMD layer in RMM.

- Improvements to Cppcheck static analysis.

  *  The Cppcheck was already integrated into the build system and more work
     was done to bring it inline with other static checks in the project.
  *  Fixed violations detected by Cppcheck MISRA addon.
  *  An application note is added to describe the Cppcheck integration.

- Changes to logging for Release build.

  *  The default Release build LOG_LEVEL is reduced to 20 (LOG_LEVEL_NOTICE).

- Fixed the broken CMAKE Ninja Generator Multi-config build.

=========
Platforms
=========

- Added base support for RD-Fremont platform.

  *  RD-Fremont also use the ``arm`` platform layer and only needs a
     defconfig file to configure RMM appropriately.

============================
Known issues and limitations
============================

- Some capabilities as mentioned in `RMM v1.0 EAC5 specification`_ are
  restricted or absent in TF-RMM as listed below:

  * The support for Self-hosted debug in Realms is not implemented (`issue#23`_).
  * Although the RMM allows CCA attestation token sizes of larger than 4KB,
    there is a limitation on the size of the Platform attestation token part.
    On the RMM-EL3 interface, there is only a shared buffer of 4KB that is
    currently shared on the FVP. This needs to be enhanced so that larger
    platform token sizes can be tested (`issue#24`_).

- The attest_init_realm_attestation_key() does not always reset the RMM to the correct
  state on encountering an error (`issue#25`_).

=================
Upcoming features
=================

- Prototype new features as described in `RMM v1.1 Alpha specification`_.

  *  Realm Device Assignment - A feature which allows devices to be assigned to Realms,
     attested and granted permission to access Realm owned memory.
  *  Planes - A feature which allows a Realm to be divided into multiple
     mutually isolated execution environments, called Planes.

- Add unit-tests for Stage 2 MMU code (s2tt).

- Continue to Enhance CBMC analysis to more RMI commands.

- Fuzz testing for RMM utilizing the `fake_host` architecture.

- Integrate more static analyzers into RMM build system.

- Implement support for Self-hosted debug in realms.

- Support FEAT_MEC in RMM.

.. _TF-A v2.11: https://git.trustedfirmware.org/TF-A/trusted-firmware-a/+/refs/tags/v2.11.0
.. _RMM v1.1 Alpha specification: https://developer.arm.com/-/cdn-downloads/PDF/Architectures/DEN0137_1.1-alp5_rmm-arch_external.pdf?__token__=st=1714479850~exp=2029839850~hmac=cca7b8c22f7b94e6c929d53176ac57c51487558b73fb27e5c181f4cc7231a83b
.. _issue#23: https://github.com/TF-RMM/tf-rmm/issues/23
.. _issue#24: https://github.com/TF-RMM/tf-rmm/issues/24
.. _issue#25: https://github.com/TF-RMM/tf-rmm/issues/25

******
v0.4.0
******

The following sections have the details on the release. This release has been
verified with `TF-A v2.10`_ release.

============================
New features in this release
============================

- Added initial partial support for analysing RMM source code with
  CBMC (https://www.cprover.org/cbmc/).

  * A new HOST_VARIANT, `host_cbmc`, has been introduced for this purpose.
  * The CBMC testbench files and autogenerated files from RMM machine
    readable specification are imported into the source tree.
  * An application note for the same is added to the documentation.

- Aligned the implementation to `RMM v1.0 EAC5 specification`_.

  * The relevant tag for the alignment is `rmm-spec-v1.0-eac5`_.
  * There is also an intermediate RMM v1.0 EAC2 alignment which
    is tagged `rmm-spec-v1.0-eac2`_.

- Supported save and restore of Non Secure SME context when Realms are
  scheduled.

  * The SIMD abstraction in RMM was reworked to cater for this requirement.
  * Added support to emulate SME specific feature ID registers.
  * Support injecting UNDEF exception into realm when SME is accessed
    within it.
  * Also RMM now can handle SVE hint bit as specified by SMCCC v1.3
    specification.

- Added `TF-RMM Threat Model`_ to the documentation.

- Added capability to privately map the per-CPU stack.

  * This contains any stack overflows to the particular CPU and prevents
    a CPU from corrupting another CPU stack.

-  Added FEAT_PAUTH and FEAT_BTI support to RMM and also capability to
   use FEAT_PAUTH within realms.

- Migrate to PSA Crypto API for attestation and measurement functionality
  in RMM.

- Added FEAT_LPA2 support to Stage 1 MMU code (lib/xlat) in RMM.

- Added Stage 1 MMU setup design document.

==================================
Build/Testing/Tooling improvements
==================================

- Added static commit message checker which enforces the commit message
  guidelines mandated for the project.

- Added clang-tidy checker as one of the static analyzers.

  * Several fixes to errors flagged by the static checker have been fixed.

- Fixed issues found in xlat lib unittests.

- Added github workflow for git submodules so that the TF-RMM dependencies
  display correctly in github.

- Added github workflow to configure an automatic message for PRs on GitHub
  and also build and run RMM unittests for every update of the `main` branch.

- Added FEAT_LPA2 unit tests for lib/xlat module.

- Added RSI logger unit tests.

=========
Platforms
=========

- The support for QEMU virt platform was merged.

======================================
Bug fixes/improvements in this release
======================================

- Fixed issue with TLB invalidations for unprotected mappings during
  RMI_RTT_DESTROY command.

- Fixed an issue wherein attest token write may return without releasing
  lock on the last level RTT of the mapped buffer.

- Enable TSW bit in hcr_el2 when executing in Realm world so as to trap
  any data cache maintenance instructions that operate by Set/Way.

- Fixed issues flagged by coverity online scan. The defects detected
  can be found in the `TF-RMM coverity scan online`_ homepage.

- Fixed issues in s2tt management related to NS memory assignment/unassignment.

- Added missing check to gicv3_hcr field.

- Cache line align xlat lib data structures accessed by secondary CPUs to avoid
  data corruption due to mismatched memory attribute accesses by RMM during
  warm boot.

- Corrected linker options when building qcbor library.

- Fixes to comply with MISRA coding guidelines.

- Adjusted mbedTLS heap size depending on MAX_CPUS in RMM.

- Fixed issue with RMI_DATA_CREATE_UNKNOWN setting RIPAS to RAM.

- Added 'ipa_bound' failure condition in RMI_DATA_DESTROY handler. Also added
  'level_bound' failure condition for RMI_RTT_MAP_UNPROTECTED and
  RMI_RTT_UNMAP_UNPROTECTED command handlers.

- Fixed issue with rsi_log_on_exit() and modified the logging format.

- Fixed issue with change `ipa_align` failure condition.

- Unified design of RSI/PSCI handlers.

- The issue with RMM config ``RMM_FPU_USE_AT_REL2`` is fixed and the SIMD
  registers are saved and restored depending on the live register context in
  use which be one of FPU, SVE or SME.

- The compatibility check for RMM-EL3 interface version is hardened.

- Issue related to attestation token interruption flow is fixed.

- Enhanced the `fake_host` sample application to do Realm token creation.

- Fixed D-cache maintenance in fvp_set_dram_layout().

- Updated t_cose submodule to use upstream version rather than a forked
  version.

============================
Known issues and limitations
============================

- Some capabilities as mentioned in `RMM v1.0 EAC5 specification`_ are
  restricted or absent in TF-RMM as listed below:

  * The RMI_RTT_FOLD command only allows folding upto Level 2 even though
    the specification allows upto Level 1.
  * The support for Self-hosted debug in Realms is not implemented.
  * Although the RMM allows CCA attestation token sizes of larger than 4KB,
    there is a limitation on the size of the Platform attestation token part.
    On the RMM-EL3 interface, there is only a shared buffer of 4KB that is
    currently shared on the FVP. This needs to be enhanced so that larger
    platform token sizes can be tested.

- The `rmm-el3-ifc` component does not always reset the RMM to the correct
  state on encountering an error. This needs to be corrected.

- The invocation of mmio_emulation() and sea_inj() functions need to be
  mutually exclusive during schedule of a REC. Currently both the cases
  are allowed to be satisfied at the same time which is incorrect.

=================
Upcoming features
=================

- FEAT_LPA2 support for Stage 2 MMU code (s2tt) in RMM.

- Add unit-tests for Stage 2 MMU code (s2tt) and also any associated rework
  for the s2tt component.

- Enhance CBMC analysis to more RMI commands.

- Fuzz testing for RMM utilizing the `fake_host` architecture.

- Support for new capabilities like Device assignment as mandated by future
  versions of RMM specification.

- Integrate more static analyzers into RMM build system.

- Implement support for Self-hosted debug in realms.


.. _TF-A v2.10: https://git.trustedfirmware.org/TF-A/trusted-firmware-a.git/tag/?h=v2.10.0
.. _RMM v1.0 EAC5 specification: https://developer.arm.com/documentation/den0137/1-0eac5/?lang=en
.. _rmm-spec-v1.0-eac5: https://git.trustedfirmware.org/TF-RMM/tf-rmm.git/tag/?h=rmm-spec-v1.0-eac5
.. _rmm-spec-v1.0-eac2: https://git.trustedfirmware.org/TF-RMM/tf-rmm.git/tag/?h=rmm-spec-v1.0-eac2
.. _TF-RMM coverity scan online: https://scan.coverity.com/projects/tf-rmm-tf-rmm
.. _TF-RMM Threat Model: https://tf-rmm.readthedocs.io/en/latest/security/threat_model/index.html

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
