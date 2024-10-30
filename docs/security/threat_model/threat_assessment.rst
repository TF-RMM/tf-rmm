.. SPDX-License-Identifier: BSD-3-Clause
.. SPDX-FileCopyrightText: Copyright TF-RMM Contributors.

Threat Assessment
=================

The following threats were identified by applying STRIDE analysis on
each diagram element of the data flow diagram. The threats are related to
software and implementation specific to TF-RMM.

For each threat, we strive to indicate whether the mitigations are currently
implemented or not. However, the answer to this question is not always
straightforward. Some mitigations are partially implemented in the generic code
but also rely on the platform code to implement some bits of it. This threat
model aims to be platform-independent and it is important to keep in mind that
such threats only get mitigated if the platform properly fulfills its
responsibilities.

Also, some mitigations might require enabling specific features, which must be
explicitly turned on via a build flag.

The ``Pending actions?`` box highlights any action that needs to be done in
order to implement the mitigations.

+------------------------+---------------------------------------------------+
| ID                     | 01                                                |
+========================+===================================================+
| Threat                 | | Information leak via UART logs.                 |
|                        |                                                   |
|                        | | During the development stages of software it is |
|                        |   common to print all sorts of information on the |
|                        | | console, including sensitive or confidential    |
|                        |   information such as crash reports with detailed |
|                        | | information of the CPU state, current registers |
|                        |   values, privilege level or stack dumps.         |
|                        |                                                   |
|                        | | This information is useful when debugging       |
|                        |   problems before releasing the production        |
|                        | | version but it could be used by an adversary    |
|                        |   to develop a working exploit if left enabled in |
|                        | | the production version.                         |
|                        |                                                   |
|                        | | This happens when directly logging sensitive    |
|                        |   information and more subtly when logging based  |
|                        | | on sensitive data that can be used as a         |
|                        |   side-channel information by an adversary.       |
+------------------------+---------------------------------------------------+
| Diagram Elements       | DF2                                               |
+------------------------+---------------------------------------------------+
| Assets                 | Sensitive Data                                    |
+------------------------+---------------------------------------------------+
| Threat Agent           | AppDebug                                          |
+------------------------+---------------------------------------------------+
| Threat Type            | Information Disclosure                            |
+------------------------+---------------------------------------------------+
| Impact                 | Informational (1)                                 |
+------------------------+---------------------------------------------------+
| Likelihood             | Informational (1)                                 |
+------------------------+---------------------------------------------------+
| Total Risk Rating      | Informational (1)                                 |
+------------------------+---------------------------------------------------+
| Mitigations            | | 1) For production releases:                     |
|                        | |   i) Remove sensitive information logging.      |
|                        | |   ii) Do not conditionally log based on         |
|                        |        sensitive data.                            |
|                        | |   iii) Do not log high precision timing         |
|                        |        information.                               |
|                        | |   iv) Do not log register contents which may    |
|                        |        reveal secrets during crashes (Error       |
|                        | |      Syndrome registers are allowed to be       |
|                        |        logged).                                   |
|                        |                                                   |
|                        | | 2) Provide option to fully disable RMM logging  |
|                        |      for production releases.                     |
+------------------------+---------------------------------------------------+
| Mitigations            | | 1) Yes/Platform-specific.                       |
| implemented?           | |    The default log level does not output verbose|
|                        |      log. RMM does not implement crash reporting. |
|                        | |    Messages produced by the platform code       |
|                        |      should use the appropriate level of verbosity|
|                        | |    so as not to leak sensitive information in   |
|                        |      production builds.                           |
|                        | | 2) Yes.                                         |
|                        | |    RMM provides the ``LOG_LEVEL`` build option  |
|                        |      which can be used to disable all logging.    |
+------------------------+---------------------------------------------------+
| Pending actions?       | | 1) Ensure the right verbosity level is used for |
|                        |      the type of information that it is logged.   |
+------------------------+---------------------------------------------------+

+------------------------+---------------------------------------------------+
| ID                     | 02                                                |
+========================+===================================================+
| Threat                 | | An adversary can try stealing information by    |
|                        |   using RMM ABI.                                  |
|                        |                                                   |
|                        | | NS Host accesses RMM through RMM ABI. Malicious |
|                        |   code can attempt to invoke services that would  |
|                        | | result in disclosing private information or     |
|                        |   secrets.                                        |
+------------------------+---------------------------------------------------+
| Diagram Elements       | DF7                                               |
+------------------------+---------------------------------------------------+
| Assets                 | Sensitive Data                                    |
+------------------------+---------------------------------------------------+
| Threat Agent           | HostSoftware                                      |
+------------------------+---------------------------------------------------+
| Threat Type            | Information Disclosure                            |
+------------------------+---------------------------------------------------+
| Impact                 | High (4)                                          |
+------------------------+---------------------------------------------------+
| Likelihood             | High (4)                                          |
+------------------------+---------------------------------------------------+
| Total Risk Rating      | High (16)                                         |
+------------------------+---------------------------------------------------+
| Mitigations            | | 1) Ensure that RMM protects the Realm memory by |
|                        |      using GPT service provided by EL3 Firmware   |
|                        | |    and appropriate Stage 2 protections. NS Host |
|                        |      must not be able to change or access Realm   |
|                        | |    memory.                                      |
|                        | | 2) NS host must not be able to change or access |
|                        |      Realm CPU register contents other than what  |
|                        | |    is allowed by RMM ABI. Root code should      |
|                        |      perform proper context switching of certain  |
|                        | |    subset of CPU registers as mandated in       |
|                        |      `RMM-EL3 Communication Interface`_ when      |
|                        | |    entering and exiting the Realm world.        |
|                        |      Similarly, RMM should context switch any     |
|                        | |    registers not managed by EL3 when            |
|                        |      entering/exiting Realms.                     |
|                        | | 3) The RME Architecture provides means to       |
|                        |      configure memory isolation to the Realm      |
|                        | |    world. RMM relies on Root code for correct   |
|                        |      RME setup. But when undelegating memory to   |
|                        | |    the Normal world, RMM needs to ensure that   |
|                        |      suitable memory scrubbing is implemented.    |
|                        | |    Also, RMM should ensure any architectural    |
|                        |      caches are invalidated before returning back |
|                        | |    to NS Host.                                  |
+------------------------+---------------------------------------------------+
| Mitigations            | | 1) Yes.                                         |
| implemented?           | | 2) Yes.                                         |
|                        | | 3) Yes.                                         |
+------------------------+---------------------------------------------------+
| Pending actions?       | | None.                                           |
+------------------------+---------------------------------------------------+

+------------------------+---------------------------------------------------+
| ID                     | 03                                                |
+========================+===================================================+
| Threat                 | | An adversary can perform a denial-of-service    |
|                        |   attack on the system by causing the Realm       |
|                        | | world/RMM to deadlock, crash or enter into an   |
|                        |   unknown state.                                  |
+------------------------+---------------------------------------------------+
| Diagram Elements       | DF5, DF7                                          |
+------------------------+---------------------------------------------------+
| Assets                 | Availability                                      |
+------------------------+---------------------------------------------------+
| Threat Agent           | RealmCode, HostSoftware                           |
+------------------------+---------------------------------------------------+
| Threat Type            | Denial of Service                                 |
+------------------------+---------------------------------------------------+
| Impact                 | Medium (3)                                        |
+------------------------+---------------------------------------------------+
| Likelihood             | Low (2)                                           |
+------------------------+---------------------------------------------------+
| Total Risk Rating      | Medium (6)                                        |
+------------------------+---------------------------------------------------+
| Mitigations            | | 1) Upon an unrecoverable/catastrophic condition,|
|                        |      RMM should issue a ``panic()``. This would   |
|                        | |    return to EL3 Firmware, keeping the          |
|                        |      availability of the overall system. It would |
|                        | |    be EL3 responsibility to decide how to       |
|                        |      proceed (e.g. by disabling the whole Realm   |
|                        | |    world).                                      |
|                        | | 2) EL3 Firmware needs to implement a watchdog   |
|                        |      mechanism to recover CPUs from Realm World.  |
+------------------------+---------------------------------------------------+
| Mitigations            | | 1) No.                                          |
| implemented?           | | 2) Mitigation would need support from EL3       |
|                        |      Firmware.                                    |
+------------------------+---------------------------------------------------+
| Pending actions?       | | ``panic()`` needs appropriate implementation to |
|                        |   return to EL3 Firmware.                         |
+------------------------+---------------------------------------------------+

+------------------------+---------------------------------------------------+
| ID                     | 04                                                |
+========================+===================================================+
| Threat                 | | Malicious Host or Realm code can attempt to     |
|                        |   place the RMM into an inconsistent state due to |
|                        | | incorrect implementation of RMM state machines. |
|                        |   This inconsistency can be exploited to lead     |
|                        | | incorrect operation of RMM.                     |
+------------------------+---------------------------------------------------+
| Diagram Elements       | DF5, DF7                                          |
+------------------------+---------------------------------------------------+
| Assets                 | Availability, Sensitive Data, Code Execution      |
+------------------------+---------------------------------------------------+
| Threat Agent           | RealmCode, HostSoftware                           |
+------------------------+---------------------------------------------------+
| Threat Type            | Denial of Service, Tampering, Elevation of        |
|                        | privilege, Information Disclosure                 |
+------------------------+---------------------------------------------------+
| Impact                 | Medium (3)                                        |
+------------------------+---------------------------------------------------+
| Likelihood             | Low (2)                                           |
+------------------------+---------------------------------------------------+
| Total Risk Rating      | Medium (6)                                        |
+------------------------+---------------------------------------------------+
| Mitigations            | | 1) State machines should be tested for all the  |
|                        |      transitions and validated that all invalid   |
|                        | |    transitions and inputs are rejected.         |
|                        | | 2) The RMM ABI mandates pre and post conditions |
|                        |      for each ABI. The tests should verify that   |
|                        | |    these conditions are adhered to and          |
|                        |      implemented.                                 |
|                        | | 3) Static analyzers and model checkers can be   |
|                        |      used to uncover bugs in implementation.      |
|                        | | 4) Fuzz testing can be employed to uncover      |
|                        |      further issues in implementation.            |
|                        | | 5) Upon an unrecoverable/catastrophic condition |
|                        |      occurs, RMM should issue a ``panic()`` to    |
|                        | |    prevent further corruption of data or        |
|                        |      propagation of errors.                       |
+------------------------+---------------------------------------------------+
| Mitigations            | | 1) Partial.                                     |
| implemented?           | |    There are various tests in TFTF, ACS and     |
|                        |      kvm-unit-tests for exercising the ABI which  |
|                        | |    triggers the state machines. Unit tests are  |
|                        |      also present for some components to exercise |
|                        | |    internal APIs which can further test         |
|                        |      conditions and invalid cases which cannot be |
|                        | |    triggered via RMM ABI.                       |
|                        | | 2) Partial.                                     |
|                        | |    Code reviews to ensure the implementation    |
|                        |      complies the required conditions. Automated  |
|                        | |    checking via CBMC to validate the same is    |
|                        |      also being implemented.                      |
|                        | | 3) Yes.                                         |
|                        | |    CPPCheck and Coverity scan are used to detect|
|                        |      issues. CBMC is also utilized as a model     |
|                        | |    checker.                                     |
|                        | | 4) No.                                          |
|                        | | 5) Yes.                                         |
+------------------------+---------------------------------------------------+
| Pending actions?       | | Expand coverage of unittests in RMM. Evolve     |
|                        |   tests in other test frameworks in an ongoing    |
|                        | | manner. Integrate CBMC into RMM testing.        |
|                        |   Implement Fuzz testing for RMM.                 |
+------------------------+---------------------------------------------------+

+------------------------+---------------------------------------------------+
| ID                     | 05                                                |
+========================+===================================================+
| Threat                 | | Malicious Host or Realm code can attack RMM by  |
|                        |   calling unimplemented SMC calls or by passing   |
|                        | | invalid arguments to the ABI.                   |
+------------------------+---------------------------------------------------+
| Diagram Elements       | DF5, DF7                                          |
+------------------------+---------------------------------------------------+
| Assets                 | Sensitive Data, Code Execution                    |
+------------------------+---------------------------------------------------+
| Threat Agent           | RealmCode, HostSoftware                           |
+------------------------+---------------------------------------------------+
| Threat Type            | Denial of Service, Tampering, Elevation of        |
|                        | privilege, Information Disclosure                 |
+------------------------+---------------------------------------------------+
| Impact                 | High (4)                                          |
+------------------------+---------------------------------------------------+
| Likelihood             | High (4)                                          |
+------------------------+---------------------------------------------------+
| Total Risk Rating      | High (16)                                         |
+------------------------+---------------------------------------------------+
| Mitigations            | | 1) Validate SMC function IDs and arguments      |
|                        |      before using them.                           |
|                        | | 2) Invalid/Unimplemented SMCs should return back|
|                        |      to caller with error code.                   |
|                        | | 3) Tests to exercise invalid arguments and      |
|                        |      unimplemented SMCs.                          |
+------------------------+---------------------------------------------------+
| Mitigations            | | 1) Yes.                                         |
| implemented?           | | 2) Yes.                                         |
|                        | | 3) Partial.                                     |
|                        | |    The ACS test utility exercises many invalid  |
|                        |      inputs. Unit tests also test various invalid |
|                        | |    cases.                                       |
+------------------------+---------------------------------------------------+
| Pending actions?       | | Expand unit tests to cover the RMM ABI interface|
|                        |   and test for invalid inputs.                    |
+------------------------+---------------------------------------------------+

+------------------------+---------------------------------------------------+
| ID                     | 06                                                |
+========================+===================================================+
| Threat                 | | An adversary can make use of incorrect          |
|                        |   implementation of concurrent sections in RMM to |
|                        | | cause data corruption or dead/live locks.       |
+------------------------+---------------------------------------------------+
| Diagram Elements       | DF5, DF7                                          |
+------------------------+---------------------------------------------------+
| Assets                 | Availability, Sensitive Data, Code Execution      |
+------------------------+---------------------------------------------------+
| Threat Agent           | RealmCode, HostSoftware                           |
+------------------------+---------------------------------------------------+
| Threat Type            | Denial of Service, Tampering, Elevation of        |
|                        | privilege, Information Disclosure                 |
+------------------------+---------------------------------------------------+
| Impact                 | Medium (3)                                        |
+------------------------+---------------------------------------------------+
| Likelihood             | Low (2)                                           |
+------------------------+---------------------------------------------------+
| Total Risk Rating      | Medium (6)                                        |
+------------------------+---------------------------------------------------+
| Mitigations            | | 1) Follow locking discipline described in       |
|                        |      `RMM Locking Guidelines`_ when implementing  |
|                        | |    concurrent sections in RMM.                  |
|                        | | 2) Validate locking discipline using tests which|
|                        |      can run multiple threads in RMM.             |
|                        | | 3) Fuzz tests on RMM with multiple threads.     |
+------------------------+---------------------------------------------------+
| Mitigations            | | 1) Yes.                                         |
| implemented?           | | 2) Yes.                                         |
|                        | |    The TFX test has tests which can test        |
|                        |      concurrent sections in RMM. Also, stress     |
|                        | |    tests in CI will also test this scenario.    |
|                        | | 3) No.                                          |
|                        | |    Need further investigation.                  |
+------------------------+---------------------------------------------------+
| Pending actions?       | | Enhance TFX tests to test more concurrent       |
|                        |   sections in RMM. Investigate the possibility of |
|                        | | multithread Fuzz Testing.                       |
+------------------------+---------------------------------------------------+

+------------------------+---------------------------------------------------+
| ID                     | 07                                                |
+========================+===================================================+
| Threat                 | | A Realm can claim to be another Realm. NS Host  |
|                        |   can associate the PA of one Realm to another    |
|                        | | Realm.                                          |
+------------------------+---------------------------------------------------+
| Diagram Elements       | DF5, DF7                                          |
+------------------------+---------------------------------------------------+
| Assets                 | Sensitive Data                                    |
+------------------------+---------------------------------------------------+
| Threat Agent           | RealmCode, HostSoftware                           |
+------------------------+---------------------------------------------------+
| Threat Type            | Spoofing                                          |
+------------------------+---------------------------------------------------+
| Impact                 | High (4)                                          |
+------------------------+---------------------------------------------------+
| Likelihood             | Low (2)                                           |
+------------------------+---------------------------------------------------+
| Total Risk Rating      | Medium (8)                                        |
+------------------------+---------------------------------------------------+
| Mitigations            | | 1) A Realm should not be able to spoof another  |
|                        |      realm. The NSHost must not be able to assign |
|                        | |    a granule/metadata to a Realm which is       |
|                        |      already assigned to another Realm.           |
+------------------------+---------------------------------------------------+
| Mitigations            | | 1) Yes.                                         |
| Implemented?           | |    This mitigation is inherently supported by   |
|                        |      the RMM ABI. SMC call from realm is always   |
|                        | |    associated to the Realm Descriptor (RD) and  |
|                        |      the RMM ABI does not allow spoofing of RD.   |
|                        | |    NS Host always has to pass the address of a  |
|                        |      valid RD to make requests to the             |
|                        | |    corresponding Realm. RMM maintains a global  |
|                        |      granule array and every granule linked to a  |
|                        | |    Realm has a specific State and reference     |
|                        |      count associated with it. Hence, the NS Host |
|                        | |    cannot associate an already Realm associated |
|                        |      granule to another Realm.                    |
+------------------------+---------------------------------------------------+
| Pending actions?       | | None.                                           |
+------------------------+---------------------------------------------------+

+------------------------+---------------------------------------------------+
| ID                     | 08                                                |
+========================+===================================================+
| Threat                 | | An adversary could execute arbitrary code,      |
|                        |   modify some state variables, change the normal  |
|                        | | flow of the program or leak sensitive           |
|                        |   information if memory overflows and boundary    |
|                        | | checks when accessing resources are not properly|
|                        |   handled. In the particular case in which the    |
|                        | | control flow can be changed by a stack overflow,|
|                        |   code execution can also be subverted by an      |
|                        | | adversary.                                      |
|                        |                                                   |
|                        | | Like in other software, RMM has multiple points |
|                        |   where memory corruption and security errors can |
|                        | | arise.                                          |
|                        |                                                   |
|                        | | Some of the errors include integer overflow,    |
|                        |   buffer overflow, incorrect array boundary checks|
|                        | | and incorrect error management.                 |
|                        |   Improper use of asserts instead of proper input |
|                        | | validations might also result in these kinds of |
|                        |   errors in release builds.                       |
+------------------------+---------------------------------------------------+
| Diagram Elements       | DF5, DF7                                          |
+------------------------+---------------------------------------------------+
| Assets                 | Code Execution, Sensitive Data, Availability      |
+------------------------+---------------------------------------------------+
| Threat Agent           | RealmCode, HostSoftware                           |
+------------------------+---------------------------------------------------+
| Threat Type            | Tampering, Information Disclosure,                |
|                        | Elevation of Privilege                            |
+------------------------+---------------------------------------------------+
| Impact                 | Medium (3)                                        |
+------------------------+---------------------------------------------------+
| Likelihood             | Low (2)                                           |
+------------------------+---------------------------------------------------+
| Total Risk Rating      | Medium (6)                                        |
+------------------------+---------------------------------------------------+
| Mitigations            | | 1) Use proper input validation.                 |
|                        | | 2) Enable Architecture security features to     |
|                        |      mitigate buffer overflow and ROP/JOP issues. |
|                        | | 3) Utilize stack protection mechanism provided  |
|                        |      by the compiler.                             |
|                        | | 4) Design suitable per CPU stack protection, so |
|                        |      another CPU cannot corrupt stack which does  |
|                        | |    not belong to it.                            |
|                        | | 5) Suitable testing to test bounds of inputs.   |
|                        | | 6) Employ secure coding guidelines like MISRA to|
|                        |      remove many of the type safety issues        |
|                        | |    associated with the C language.              |
|                        | | 7) Use static analyzers to check for common     |
|                        |      issues. Also, make use of model checkers to  |
|                        | |    validate loop bounds and other bounds in the |
|                        |      source code.                                 |
+------------------------+---------------------------------------------------+
| Mitigations            | | 1) Yes.                                         |
| implemented?           | | 2) Yes.                                         |
|                        | |    RMM Enables many Architecture security       |
|                        |      features like PAuth and BTI but there is     |
|                        | |    ongoing action to enable more architectural  |
|                        |      security features.                           |
|                        | | 3) No.                                          |
|                        | | 4) No.                                          |
|                        | | 5) Partial.                                     |
|                        | |    Some tests are present, but more tests needed|
|                        |      to ensure the bounds are validated.          |
|                        | | 6) Yes.                                         |
|                        | | 7) Partial.                                     |
|                        |      RMM uses CPPCheck and Coverity Scan to detect|
|                        | |    issues. RMM also utilizes CMBC to ensure that|
|                        |      bounds in loops and other program constructs |
|                        | |    are proper.                                  |
+------------------------+---------------------------------------------------+
| Pending actions?       | | Add sanitizers like ASAN, MSAN or UBSAN.        |
|                        |   Implement further Architecture extensions       |
|                        | | related to security. RMM needs to implement     |
|                        |   per-CPU stack protection and also provide       |
|                        | | capability to add compiler stack protection     |
|                        |   features as a user option.                      |
+------------------------+---------------------------------------------------+

+------------------------+---------------------------------------------------+
| ID                     | 09                                                |
+========================+===================================================+
| Threat                 | | SMC calls can leak sensitive information from   |
|                        |   RMM memory via microarchitectural side channels.|
|                        |                                                   |
|                        | | Microarchitectural side-channel attacks such as |
|                        |   `Spectre`_ can be used to leak data across      |
|                        | | security boundaries. An adversary might attempt |
|                        |   to use this kind of attack to leak sensitive    |
|                        | | data from RMM memory.                           |
|                        |                                                   |
|                        | | Also, some SMC calls, such as the ones involving|
|                        |   encryption when applicable, might take different|
|                        | | amount of time to complete depending upon the   |
|                        |   parameters. An adversary might attempt to use   |
|                        | | that information in order to infer secrets or to|
|                        |   leak sensitive information.                     |
+------------------------+---------------------------------------------------+
| Diagram Elements       | DF5, DF7                                          |
+------------------------+---------------------------------------------------+
| Assets                 | Sensitive Data                                    |
+------------------------+---------------------------------------------------+
| Threat Agent           | RealmCode, HostSoftware                           |
+------------------------+---------------------------------------------------+
| Threat Type            | Information Disclosure                            |
+------------------------+---------------------------------------------------+
| Impact                 | Medium (3)                                        |
+------------------------+---------------------------------------------------+
| Likelihood             | Informational (1)                                 |
+------------------------+---------------------------------------------------+
| Total Risk Rating      | Low (3)                                           |
+------------------------+---------------------------------------------------+
| Mitigations            | | 1) Enable appropriate speculation side-channel  |
|                        |      mitigations as recommended by the            |
|                        | |    Architecture.                                |
|                        | | 2) Enable appropriate timing side-channel       |
|                        |      protections available in the Architecture.   |
|                        | | 3) Ensure the software components dealing with  |
|                        |      sensitive data use Data Independent          |
|                        | |    algorithms.                                  |
|                        | | 4) Ensure that only required memory is mapped   |
|                        |      when executing a Realm or doing operations in|
|                        | |    RMM so as to minimize effects of CPU         |
|                        |      speculation.                                 |
+------------------------+---------------------------------------------------+
| Mitigations            | | 1) Yes.                                         |
| implemented?           | | 2) Yes.                                         |
|                        | |    ``FEAT_DIT`` is enabled for RMM during       |
|                        |      attestation initialization and token signing |
|                        |      phase.                                       |
|                        | | 3) Yes.                                         |
|                        | |    RMM relies on MbedTLS library to use         |
|                        |      algorithms which are data independent when   |
|                        | |    handling sensitive data.                     |
|                        | | 4) Yes.                                         |
|                        | |    The slot buffer design for dynamically       |
|                        |      mapping memory ensures that only required    |
|                        | |    memory is mapped into RMM.                   |
+------------------------+---------------------------------------------------+
| Pending actions?       | | Review speculation vulnerabilities and ensure   |
|                        |   RMM implements all mitigations provided by the  |
|                        | | Architecture.                                   |
|                        |                                                   |
+------------------------+---------------------------------------------------+

+------------------------+---------------------------------------------------+
| ID                     | 10                                                |
+========================+===================================================+
| Threat                 | | Misconfiguration of the S2 MMU tables may allow |
|                        |   Realms to access sensitive data belonging to    |
|                        | | other Realms or incorrect mapping of NS memory  |
|                        |   may allow Realms to corrupt NSHost memory.      |
+------------------------+---------------------------------------------------+
| Diagram Elements       | DF5, DF7                                          |
+------------------------+---------------------------------------------------+
| Assets                 | Sensitive Data, Code execution                    |
+------------------------+---------------------------------------------------+
| Threat Agent           | RealmCode, HostSoftware                           |
+------------------------+---------------------------------------------------+
| Threat Type            | Information Disclosure                            |
+------------------------+---------------------------------------------------+
| Impact                 | High (4)                                          |
+------------------------+---------------------------------------------------+
| Likelihood             | Low (2)                                           |
+------------------------+---------------------------------------------------+
| Total Risk Rating      | Medium (8)                                        |
+------------------------+---------------------------------------------------+
| Mitigations            | | 1) Ensure proper implementation of S2 table     |
|                        |      management code in RMM. It should not be     |
|                        | |    possible to trigger misconfiguration of S2   |
|                        |      tables using RMM ABI. Appropriate tests to   |
|                        | |    ensure that the implementation is robust.    |
|                        | | 2) The RMM specification mandates the rules for |
|                        |      assigning memory to a Realm and IPA          |
|                        | |    management. Ensure the rules mandated by the |
|                        |      RMM specification are validated by suitable  |
|                        | |    tooling.                                     |
+------------------------+---------------------------------------------------+
| Mitigations            | | 1) Partially.                                   |
| implemented?           | |    There are various tests like kvm-unit-tests, |
|                        |      TFTF, TFX and ACS to test the                |
|                        | |    implementation. Unit tests of S2 tables need |
|                        |      to be implemented. Static analysis is in     |
|                        | |    place to detect issues.                      |
|                        | | 2) Partially.                                   |
|                        | |    Code reviews to ensure the implementation    |
|                        |      complies with the required conditions.       |
|                        | |    Automated checking via CBMC to validate the  |
|                        |      same is also being implemented.              |
+------------------------+---------------------------------------------------+
| Pending actions?       | | Increase testing coverage of S2 table management|
|                        |   code in RMM.                                    |
|                        | | Integrate CMBC into RMM testing.                |
+------------------------+---------------------------------------------------+

+------------------------+---------------------------------------------------+
| ID                     | 11                                                |
+========================+===================================================+
| Threat                 | | Realm code flow diversion through REC metadata  |
|                        |   manipulation from Host Software.                |
|                        |                                                   |
|                        | | An adversary with access to a Realm's REC could |
|                        |   tamper with the structure content and affect the|
|                        | | Realm's execution flow.                         |
+------------------------+---------------------------------------------------+
| Diagram Elements       | DF7                                               |
+------------------------+---------------------------------------------------+
| Assets                 | Code Execution                                    |
+------------------------+---------------------------------------------------+
| Threat Agent           | HostSoftware                                      |
+------------------------+---------------------------------------------------+
| Threat Type            | Tampering                                         |
+------------------------+---------------------------------------------------+
| Impact                 | High (4)                                          |
+------------------------+---------------------------------------------------+
| Likelihood             | Low (2)                                           |
+------------------------+---------------------------------------------------+
| Total Risk Rating      | Medium (8)                                        |
+------------------------+---------------------------------------------------+
| Mitigations            | | 1) The RMM specification mandates that sensitive|
|                        |      metadata like REC should be stored in Realm  |
|                        | |    PAS. Also, the specification does not allow  |
|                        |      NSHost to manipulate REC contents via RMI    |
|                        | |    once the associated Realm is Activated.      |
|                        |      Ensure that the RMM specification guidelines |
|                        | |    are enforced.                                |
|                        | | 2) Map sensitive metadata into RMM S1 tables    |
|                        |      only when manipulating the Realm/REC. Once   |
|                        | |    RMM is finished manipulating the metadata,   |
|                        |      unmap it from S1 tables. Thus the time window|
|                        | |    when RMM can access the metadata is kept to a|
|                        |      minimum thus reducing the opportunity to     |
|                        | |    corrupt the metadata.                        |
+------------------------+---------------------------------------------------+
| Mitigations            | | 1) Yes.                                         |
| implemented?           | | 2) Yes.                                         |
|                        | |    The slot-buffer mechanism in RMM is used to  |
|                        |      map metadata only when needed and it is      |
|                        | |    unmapped when the access is not required.    |
+------------------------+---------------------------------------------------+
| Pending actions?       | None                                              |
+------------------------+---------------------------------------------------+

+------------------------+---------------------------------------------------+
| ID                     | 12                                                |
+========================+===================================================+
| Threat                 | | Use of PMU and MPAM statistics to increase the  |
|                        |   the accuracy of side channel attacks.           |
+------------------------+---------------------------------------------------+
| Diagram Elements       | DF5, DF7                                          |
+------------------------+---------------------------------------------------+
| Assets                 | Sensitive Data                                    |
+------------------------+---------------------------------------------------+
| Threat Agent           | RealmCode, HostSoftware                           |
+------------------------+---------------------------------------------------+
| Threat Type            | Information Disclosure                            |
+------------------------+---------------------------------------------------+
| Impact                 | Medium (3)                                        |
+------------------------+---------------------------------------------------+
| Likelihood             | Informational (1)                                 |
+------------------------+---------------------------------------------------+
| Total Risk Rating      | Low (3)                                           |
+------------------------+---------------------------------------------------+
| Mitigations            | | 1) Save/Restore performance counters on         |
|                        |      on transitions between security domains or   |
|                        | |    between Realms.                              |
|                        | | 2) Configure MPAM so that is either disabled or |
|                        |      set to default values for Realm world.       |
+------------------------+---------------------------------------------------+
| Mitigations            | | 1) PMU is saved and restored.                   |
| implemented?           | | 2) MPAM is not enabled for Realm world.         |
+------------------------+---------------------------------------------------+
| Pending actions?       | None.                                             |
+------------------------+---------------------------------------------------+

+------------------------+---------------------------------------------------+
| ID                     | 13                                                |
+========================+===================================================+
| Threat                 | | Misconfiguration of the hardware IPs and        |
|                        |   registers may lead to data leaks or incorrect   |
|                        | | behaviour that could be damaging on its own as  |
|                        |   well as being exploited by a threatening agent. |
|                        |                                                   |
|                        | | RMM needs to interact with several hardware IPs |
|                        |   as well as system registers for which it uses   |
|                        | | its own libraries and/or drivers.               |
|                        |   Misconfiguration of such elements could cause   |
|                        | | data leaks and/or system malfunction.           |
+------------------------+---------------------------------------------------+
| Diagram Elements       | DF5, DF7                                          |
+------------------------+---------------------------------------------------+
| Assets                 | Sensitive Data, Availability                      |
+------------------------+---------------------------------------------------+
| Threat Agent           | RealmCode, HostSoftware                           |
+------------------------+---------------------------------------------------+
| Threat Type            | Information Disclosure, Denial of Service         |
+------------------------+---------------------------------------------------+
| Impact                 | High (4)                                          |
+------------------------+---------------------------------------------------+
| Likelihood             | Low (2)                                           |
+------------------------+---------------------------------------------------+
| Total Risk Rating      | Medium (8)                                        |
+------------------------+---------------------------------------------------+
| Mitigations            | | 1) Code reviews.                                |
|                        | | 2) Testing on FVPs and other hardware and       |
|                        |      emulation platforms to check for correct     |
|                        | |    behaviour.                                   |
+------------------------+---------------------------------------------------+
| Mitigations            | | 1) Yes.                                         |
| implemented?           | | 2) Yes.                                         |
|                        | |    RMM is tested regularly on FVP and more      |
|                        |      platforms will be added in future as they    |
|                        | |    become available.                            |
+------------------------+---------------------------------------------------+
| Pending actions?       | None                                              |
+------------------------+---------------------------------------------------+

--------------

.. _RMM Boot Interface specification: https://trustedfirmware-a.readthedocs.io/en/latest/components/rmm-el3-comms-spec.html#rmm-boot-interface
.. _Spectre: https://developer.arm.com/support/arm-security-updates/speculative-processor-vulnerability
.. _RMM Locking Guidelines: https://tf-rmm.readthedocs.io/en/latest/design/locking.html
.. _RMM-EL3 Communication Interface: https://trustedfirmware-a.readthedocs.io/en/latest/components/rmm-el3-comms-spec.html
