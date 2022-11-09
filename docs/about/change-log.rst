.. SPDX-License-Identifier: BSD-3-Clause
.. SPDX-FileCopyrightText: Copyright TF-RMM Contributors.

############################
Change-log and Release notes
############################

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
