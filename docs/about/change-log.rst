.. SPDX-License-Identifier: BSD-3-Clause
.. SPDX-FileCopyrightText: Copyright TF-RMM Contributors.

############################
Change-log and Release notes
############################

******
v0.8.0
******

The following sections have the details on the release candidate. This
release has been verified with `TF-A v2.14`_ release.

============================
New features in this release
============================

- Planes support (RMM v1.1 feature)

  *  Added Plane support across runtime (core, REC, Realm components), RMI/RSI
     libraries and SMC interface.
  *  Implemented Plane PMU, timer, interrupt and GIC ownership transfer
     capabilities.
  *  Added Plane support to S2TT, S2AP libraries and architectural changes
     enabling auxiliary granule map/unmap (aligned to alp13/alp14 revisions).
  *  Added support for FEAT_S1PIE/S1POE, FEAT_S2PIE/S2POE (including unittests).
  *  Added shrinkwrap overlay to enable FEAT_SxPIE and FEAT_SxPOE for planes.
  *  Added CBMC and fake_host wrappers for new Plane RMIs.

- Realm Device Assignment support aligned with `RMM v1.1 Alpha 12 specification`_.

  *  Implemented RMI_VDEV ABIs (CREATE, COMMUNICATE, COMPLETE) and related
     pending operation handling.
  *  Added PDEV lifecycle and capability commands (CREATE, DESTROY, GET_STATE,
     COMMUNICATE, ABORT, STOP, AUX_COUNT, SET_PUBKEY, NOTIFY, IDE_RESET,
     DEV_MEM_VALIDATE).
  *  Enhanced the device assignment EL0 app with DVSEC discovery, IDE key
     management, PCI TDISP flows, device measurement retrieval, secure SPDM
     messaging and non-secure MMIO helpers.
  *  Introduced Arm and host platform updates plus EL3 SMC handlers to program
     root port IDE keys and describe PCIe root complex information.
  *  Added helpers for measurements, secured SPDM messaging, certificate
     retrieval, caching of device interface reports and public key validation.
  *  Moved SPDM requester logic into EL0 App; imported required libraries from
     spdm_emu.
  *  Added support in S2TT library to support device memory.

- FEAT_MEC (Memory Encryption Context) enablement

  *  Added MEC library/component, MEC policy claims, MECID programming and
     granule/table updates (XLAT + shared MECID handling).
  *  Added helpers to reserve, program and sanitize MECIDs plus
     slot buffer modifications for MEC support.
  *  Added shrinkwrap overlays for MEC feature stack.

- ID regs management framework in RMM

  *  The new framework queries EL3 capabilities using the ARCH_FEATURE_AVAILABILITY
     SMC call and RMM sanitizes values of ID regs and caches them at cold boot.
     Includes forward-looking support for FEAT_IDTE3 in TF-A.

- Additional architectural feature enablement

  *  Added support and enablement for FEAT_TCR2.
  *  Added FEAT_D128 support for Realms.
  *  Added 32-bit single-copy-atomics, undefined behavior sanitizer build option,
     sanitize helpers and ID register caching.
  *  Updated RSI feature register 0 and feature reporting (RMI/RSI_VERSION).

- Tooling & overlays

  *  Added shrinkwrap overlays for: RMM v1.1 features, DA feature stack, FVP
     DA testing arguments.

======================================
Bug fixes/improvements in this release
======================================

- Mutiple fixes on  Planes:

  *  SIMD trap management between planes
  *  VMID release on failure
  *  Exit path correctness
  *  SEA injection handling

- Refactored the granule scrub flow which was needed for FEAT_MEC
  support in RMM and also removed some redundant granule zeroing in
  the Realm Creation flow.

- HCR_EL2 define fixes to better rationalize the init value.

- Device Assignment: numerous fixes to locking, state transitions, random
  number usage, unaligned buffer writes, key length validation and Coverity
  reported issues.

- Fix Realm MEC Policy key value in the attestation report.

- Runtime/core: annotation and logging improvements (system_abort, panic,
  command logging), shortened PSTATE access and NULL pointer checks across
  subsystems.

- Corrected translation table handling for LPA2, device memory RIPAS updates,
  slot buffer assertions and S2TT macros.

- Addressed numerous Coverity findings through additional null checks, overflow
  mitigations and annotations.

- Updated external dependency versions (libspdm 3.6.0, mbedTLS v3.6.2).

==================================
Build/Testing/Tooling improvements
==================================

- Enabled Undefined Behavior Sanitizer (UBSAN) support and fixed related
  issues.

- Added new unittests (S2TT device memory tests, S2PIE/POE support, ns_buffer
  write alignment cases).
- Added Shrinkwrap overlays for DA, MEC and Planes features.

- Tooling/static analysis: bumped up cppcheck/clang-tidy versions, fixed
  Coverity errors; pyelftools bumped to v0.32.

- Improved logging, error reporting and static analysis integration (Coverity,
  cppcheck, clang-tidy version minimum update).

=========
Platforms
=========

- Added Arm platform descriptions for PCIe root complex capabilities to support
  DA workflows.

============================
Known issues and limitations
============================

- Self-hosted debug for Realm is still not implemented (`issue#23`_).
- Some capabilities from latest RMM specifications remain restricted or
  experimental.

=================
Upcoming features
=================

- Further hardening and performance tuning for Planes, MEC and
  Device Assignment features.
- Continued CBMC coverage expansion and static analysis improvements.
- Fuzz testing leveraging the `fake_host` architecture.
- Support for Self-hosted debug in Realms.
- Live Firmware Activation for RMM.


.. _TF-A v2.14: https://git.trustedfirmware.org/TF-A/trusted-firmware-a/+/refs/tags/v2.14.0
.. _RMM v1.1 Alpha 12 specification: https://developer.arm.com/-/cdn-downloads/permalink/Architectures/Armv9/DEN0137_1.1-alp12.zip

******
v0.7.0
******

The following sections have the details on the release. This release has been
verified with `TF-A v2.13`_ release.

============================
New features in this release
============================

- Deprivileging RMM code via EL0 App support

  *  Introduced a framework for building, packaging, and executing EL0 apps.
  *  Restructured the RMM code base to build certain components as separate
     EL0 applications.
  *  Moved the Attestation and pseudo-random number generator functionality
     to EL0 Apps.
  *  Added `fake-host` support to run EL0 applications.
  *  Added a supporting design document.

- Added some RMMv1.1 APIs

  *  Implemented ``RMI_DEV_MEM_(UN)MAP`` commands.
  *  Added support for device granules in ``RMI_GRANULE_DELEGATE`` and
     ``RMI_GRANULE_UNDELEGATE`` commands.

======================================
Bug fixes/improvements in this release
======================================

- EL0 App framework fixes and improvements

  *  Collected app artifacts in a single location.
  *  Fixed the path to the EL0 apps linker script.
  *  Refactored the host-common layer to separate El2-EL0 shared and
     EL2-specific code.
  *  Enforced 64KB alignment for the RMM Core to meet ELF loader requirements.
  *  Forced lld to apply link time reloc values - this is to resolve issue
     with App execution when linked using LLD.

- Enable Generic PL011 UART config - This reduces the PL011 driver
  to operate on the SBSA Generic UART register subset.

- Enabled ``-fstack-protector-strong`` compiler flag for stack protection.

- Added support to read device memory info from the Boot manifest at EL3 and
  handle DEV granules in RMM.

- Fixed various ``clang-tidy-18`` errors.

- Hid MPAM from Realms and trap access to MPAM registers from Realm. Since RMM
  does not support configuring MPAM for Realms, disabled FEAT_MPAM for Realms.

- Disabled BRBE at R-EL2 and R-EL1.

- Modified ``handle_sysreg_access_trap`` to skip advancing PC to allow injecting
  UNDEF abort back into Realms.

- Added -Wstrict-aliasing compiler flag.

- Fixed PMU save/restore register sequence in RMM.

  * RMM now saves/restores all NS event counters, even if realm is not
    using all counters.
  * Removed pmxevcntr_el0 and pmxevtyper_el0 registers from
    saving/restoring as they are aliases for pmevcntrN_el0 and pmevtyperN_el0,
    selected by pmselr_el0.sel.
  * Removed saving pmcntenclr_el0, pmintenclr_el1 and pmovsclr_el0. These
    registers are restored with inverted values of pmcntenset_el0,
    pmintenset_el1 and pmovsset_el0.

- Improved performance by clearing granule memory after MMU is enabled.

- Updated default cases for handling SEAs and SEIs so that they call
  system_abort() instead of asserting.

- Corrected the DFSC macro value for asynchronous SError exceptions
  from ``0x1`` to ``0x11``.

- Fixed missing ``break`` in ``fake_host`` when processing monitor call ID.

- Added ``-fno-delete-null-pointer-checks`` to disable optimization that can
  remove such checks.

- Added -Wextra compile flag for more warnings.

- Introduced additional compiler options: `-Wstrict-overflow` and
  ``-D_FORTIFY_SOURCE=2``. Note: `FORTIFY_SOURCE` is added for
  future-proofing; RMM does not currently link against ``glibc``.

- Added the `-Wnull-dereference` compile option to Debug build of RMM.
  It is added only to Debug build as it shows false positives for Release
  build.

- Removed the redundant granule_unlock() in smc_rec_create error path
  when Aux granule is not found.

- Fixed Coverity MISRA compliance issues.

- Correctly configured PSTATE flags (``TCO``, ``DIT``, ``UAO``, ``PAN``,
  ``SSBS``, ``BTYPE``) during abort injection to R-EL1.

- Added missing `top_gran_align` check to `RMI_RTT_SET_RIPAS` ABI.

- Added support in RMI_VERSION and RSI_VERSION commands to report lower and
  higher supported interface revisions.

- Fixed a missing call to release the shared buffer between EL3 and RMM in
  one of the error code paths of the EL3_TOKEN_SIGN attestation flow.

==================================
Build/Testing/Tooling improvements
==================================

- Updated minimum CMake version requirement to 3.20. This is needed
  to support the build for EL0 app framework.

- Upgraded jinja2 from 3.1.5 to 3.1.6 for document generation

- Explicitly set C++ standard for Unit tests (which are written in C++).

- Removed variable size arrays in some unittests.

- Added support for updating git submodules during configuration of RMM.
  This ensures updated dependencies are automatically integrated during
  builds, particularly after project rebases. This also ties in with the
  patching mechanism in RMM wherein a particular SHA is assumed for the
  submodules.

- Updated Shrinkwrap overlay to add PCIE DOE and IDE parameters for
  the FVP to facilitate CCA DA development.

- Switched to importing `libspdm` via git submodules instead of a custom
  CMake mechanism.

- Moved git utils cmake helpers to ``cmake/`` folder.

=========
Platforms
=========

- Added initial platform support for RD-V3-R1. RD-V3-R1 and
  RD-V3-R1-Cfg1 Fixed Virtual Platforms are Arm Neoverse Reference Design
  platforms with ARMv9 RME enabled CPUs.

============================
Known issues and limitations
============================

- Some capabilities mentioned in `RMM v1.0 REL0 specification`_ are
  restricted or absent in TF-RMM as listed below:

  * The support for Self-hosted debug in Realms is not implemented (`issue#23`_).

=================
Upcoming features
=================

- Prototype new features as described in `RMM v1.1 Alpha 13 specification`_.

  *  Realm Device Assignment - A feature which allows devices to be assigned to Realms,
     attested and granted permission to access Realm owned memory.
  *  Planes - A feature which allows a Realm to be divided into multiple
     mutually isolated execution environments, called Planes.
  *  Support FEAT_MEC in the Realm world.

- Continue to enhance CBMC analysis to support more RMI commands.

- Fuzz testing for RMM utilizing the `fake_host` architecture.

- Implement support for Self-hosted debug in Realms.

- Support Live Firmware Activation of RMM.


.. _TF-A v2.13: https://git.trustedfirmware.org/TF-A/trusted-firmware-a/+/refs/tags/v2.13.0
.. _RMM v1.1 Alpha 13 specification: https://developer.arm.com/-/cdn-downloads/permalink/Architectures/Armv9/DEN0137_1.1-alp13.zip

******
v0.6.0
******

The following sections have the details on the release. This release has been
verified with `TF-A v2.12`_ release.

============================
New features in this release
============================

- Changes to align to `RMM v1.0 REL0 specification`_.

- Support for alternative attestation token signing via EL3 which includes:

  *  A new config flag, ``ATTEST_EL3_TOKEN_SIGN``, is introduced.
  *  New RMM-EL3 interface APIs to query EL3_FEATURES, push and pull
     EL3 Attest token sign requests and retrieve Realm attestation
     public key from EL3.
  *  Add support in fake_host architecture for validating the attestation
     flow.
  *  Patch to enable EL3 based signing flow in t_cose.

======================================
Bug fixes/improvements in this release
======================================

- Reduce memory footprint of RMM : redefine granule structure to reduce granule
  struct from 4 bytes to 2 bytes.

- Add support for FEAT_DoubleFault2 for Realms.

- Improve RMM performance : remove broadcast invalidates when mapping and
  unmapping slot buffers.

- RMM hardening : invalidate caches during boot.

- Add libspdm version 3.4.0 as an external dependency to TF-RMM.

- Enable FEAT_DIT on a fine-grained basis in RMM.

- Upgrade Mbed TLS to v3.6.0.

- Add binary search algorithm to improve DRAM bank lookup. As a result,
  the platform API implementation can be made common for all platforms.

- Add capability to `xlat` library to map UNPRIV memory in preparation
  for EL0 app support.

- Refactor attestation component to allow RMM to continue functioning even
  if attestation initialization fails.

- Enhance lib/attestation component to handle platform token request in
  hunks. This allows to transfer tokens larger than 4KB from EL3
  (`issue#24`_).

- Rename previous build option RMM_CCA_DA to RMM_V1_1. Some base
  support patches related to `RMM v1.1 Alpha 9 specification`_ are also
  merged, which includes:

  *  Update RMI feature register0 with Device Assignment(DA) fields.
  *  Add aarch64_stub libraries required by libspdm.
  *  Define PDEV AUX granules map/unmap helpers.
  *  Add DA specific granule state.

- Fix checksum calculation of `console_info` data structure in RMM-EL3 boot
  manifest.

  *  Note that this is a breaking change and EL3 firmware needs to be updated
     to send the correct checksum.

- Fix RTT_READ_ENTRY to set x3 correctly.

- Fix deadlock in RMI_REC_CREATE.

  *  An error when aux granules are locked during REC_CREATE would have
     resulted in a deadlock in RMM. This is fixed.

- Fix error handling in attest key init sequence.

- Fix checks on s2tte_get_ripas() in lib/s2tt.

- Fix simd_context_init() call for SIMD_OWNER_NWD in unit tests.

- Fix rmm-runtime to add `sb` instruction on realm_exit().

- Fix outstanding Misra C 2012 issues in the source code.

- Refactor `lib/attestation` to manage token state within the component.

- Fix runtime to unlock RTT if the RTT walk succeeds in a corner case.

- Add build option for plat token buffer size.

- Fix calculation of VMPIDR_EL2 value to align with the specification.

- Fix to ensure that physical address <= 48 bits for LPA2 disabled Realm
  when running on a LPA2 capable hardware.

- Remove hard-coded configuration of VTRC_EL2.PS.

- Add workaround for Clang 18.x failure.

- Fix usage of psa_hash_finish() in lib/measurement component.

- Clear ISV bit for non emulatable data abort in rec->last_run_info.esr.

- Fix to adjust heap size based on MAX_CPUS.

- Revert setting of TSW bit in Realm HCR_EL2 flags.

- Fix error handling in attest_init_realm_attestation_key() sequence
  (`issue#25`_).

==================================
Build/Testing/Tooling improvements
==================================

- Add shrinkwrap overlays to facilitate RMM development and testing.

- Add git helper to apply patches in submodule.

- Add unittests for the s2tt library.

- Enhance Cppcheck build target to fail the build if static
  analysis errors are detected.

=========
Platforms
=========

- Rename the Rdfremont platform config to RD-V3.

- Add support for QEMU SBSA platform.

============================
Known issues and limitations
============================

- Some capabilities mentioned in `RMM v1.0 REL0 specification`_ are
  restricted or absent in TF-RMM as listed below:

  * The support for Self-hosted debug in Realms is not implemented (`issue#23`_).

=================
Upcoming features
=================

- Prototype new features as described in `RMM v1.1 Alpha 9 specification`_.

  *  Realm Device Assignment - A feature which allows devices to be assigned to Realms,
     attested and granted permission to access Realm owned memory.
  *  Planes - A feature which allows a Realm to be divided into multiple
     mutually isolated execution environments, called Planes.
  *  Support FEAT_MEC in the Realm world.

- Continue to enhance CBMC analysis to support more RMI commands.

- Fuzz testing for RMM utilizing the `fake_host` architecture.

- Implement support for Self-hosted debug in Realms.

- Support Live Firmware Activation of RMM.

- EL0 app support to run parts of RMM at EL0.

.. _TF-A v2.12: https://git.trustedfirmware.org/TF-A/trusted-firmware-a/+/refs/tags/v2.12.0
.. _RMM v1.0 REL0 specification: https://developer.arm.com/documentation/den0137/1-0rel0/?lang=en
.. _RMM v1.1 Alpha 9 specification: https://developer.arm.com/-/cdn-downloads/permalink/Architectures/Armv9/DEN0137_1.1-alp9.zip

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
