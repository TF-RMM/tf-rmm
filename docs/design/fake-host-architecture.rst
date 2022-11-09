.. SPDX-License-Identifier: BSD-3-Clause
.. SPDX-FileCopyrightText: Copyright TF-RMM Contributors.

##########################
RMM Fake host architecture
##########################

RMM supports building and running the program natively as a regular user-space
application on the host machine. It achieves this by emulating the ``aarch64``
specific parts of the program on the host machine by suitable hooks in the
program. The implementation of the hooks can differ based on the target
employment of running the program in this mode. Some of the foreseen
employment scenarios of this architecture includes:

1. Facilitate development of architecture independent parts of
   RMM on the host machine.
2. Enable unit testing of components within RMM with the benefit of
   not having to mock all the dependencies of the component.
3. Leverage host development environment and tools for various
   purposes like debugging, measure code coverage, fuzz testing,
   stress testing, runtime analysis of program etc.
4. Enable RMM compliance testing and verification of state machine
   and locking rules on the host machine.
5. Profile RMM on the host machine and generate useful insights
   for possible optimizations.

We expect the fake host architecture to be developed over time in future to
cover some of the employment scenarios described above. The current code
may not reflect the full scope of this architecture as discussed in this
document.

The fake host architecture has some limitations:

1. The architecture is not intended to support multi-thread execution.
   The intrisics to support critical section and atomics are emulated
   as NOP.
2. Cannot execute AArch64 assembly code on the host due to obvious
   reasons.
3. Cannot emulate AArch64 exceptions during RMM execution although
   some limited form of handling exceptions occurring in Realms can
   probably be emulated.
4. The program links against the native compiler libraries which enables
   use of development and debug features available on the host machine.
   This means the libc implementation in RMM cannot be verified using
   this architecture.

The fake host architecture config is selected by setting the config
``RMM_ARCH=fake_host`` and the platform has to be set to a variant
of `host` when building RMM. The different variants of the `host`
platform allow to build RMM for each of the target employment
scenarios as listed above.

*****************************
Fake host architecture design
*****************************

|Fake Host Architecture Diagram|


The above figure shows the fake host architecture design.
The architecture independent parts of RMM are linked against
suitable host emulation blocks to enable the program to run
on the host platform.

The EL3 (monitor) emulation layer emulates the entry and exception
from EL3 into Realm-EL2. This includes entry and exit from RMM
as part of RMI handling, entry into RMM as part of warm/cold boot,
and EL3 service invocations by RMM using SMC calls. Similarly the
Realm entry/exit emulation block allows emulation of running
a Realm. It would also allow to emulate exit from Realm due to
synchronous or asynchronous exceptions like SMC calls, IRQs, etc.

The hardware emulation block allows to emulate sysreg accesses,
granule memory delegation and NS memory accesses needed for RMM. Since
RMM is running as a user space application, it does not have the ability
to map granule memory to a Virtual Address space. This capability is
needed for the ``slot buffer`` component in RMM. Hence there is
also need to emulate VA mapping for this case.

The AArch64 intrinsics emulation block allows emulation of exclusives,
assembly instructions for various architecture extensions, barriers and
atomics, cache and TLB operations although most of them are defined
as NOP at the moment.

Within the RMM source tree, all files within the ``fake_host``
folder of each component implement the necessary emulation on host.
Depending on the target employment for the fake host
architecture, it is necessary to adapt the behaviour of
the emulation layer. This is facilitated by the APIs defined
in ``host_harness.h`` header. The implementation of the API
is done by the ``host`` platform and each variant of the ``host``
can have a different implementation of the API suiting its
target employment. The API also facilitates test and verification
of the emulated property as needed by the employment.


******************************************************************
Fake host architecture employment scenarios implemented or ongoing
******************************************************************

This section describes the currently implemented scenarios utilizing
the fake host architecture.

1. Unit testing framework in RMM which allows testing public API of
   components and generation of code coverage data.

.. |Fake Host Architecture Diagram| image:: ./diagrams/fake_host_arch.drawio.png

