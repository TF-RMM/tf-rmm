.. SPDX-License-Identifier: BSD-3-Clause
.. SPDX-FileCopyrightText: Copyright TF-RMM Contributors.


.. _build_options_examples:

#####################
RMM Build Examples
#####################

The |RMM| supports a wide range of build configuration options. Some of these options
are more regularly exercised by developers, while others are for **advanced** and
**experimental** usage only.

|RMM| can be built using either GNU(GCC) or :ref:`LLVM(Clang)<llvm_build>`
toolchain. See :ref:`this section<getting_started_toolchain>` for toolchain
setup and the supported versions.

The build is performed in 2 stages:

**Configure Stage:** In this stage, a default config file can be specified which configures
a sane config for the chosen platform. If this default config needs to be modified, it is
recommended to first perform a default config and then modify using the cmake ncurses as
shown in :ref:`CMake UI Example<build_config_example>`.

**Build Stage:** In this stage, the source build is performed by specifying the `--build` option.
See any of the commands below for an example.

.. note::

    It is recommended to clean build if any of the build options are changed from previous build.

Below are some of the typical build and configuration examples frequently used in |RMM| development
for the FVP Platform. Detailed configuration options are described :ref:`here<build_options_table>`.

RMM also supports a ``fake_host`` build which can be used to build RMM for test
and code analysis on the host machine. See
:ref:`this section here<fake_host_build>` for more details.

1. Perform an initial default build with minimum configuration options:

Build using gnu toolchain

.. code-block:: bash

    cmake -DRMM_CONFIG=fvp_defcfg -S ${RMM_SOURCE_DIR} -B ${RMM_BUILD_DIR}
    cmake --build ${RMM_BUILD_DIR}

Build using LLVM toolchain

.. code-block:: bash

    cmake -DRMM_CONFIG=fvp_defcfg -DRMM_TOOLCHAIN=llvm -S ${RMM_SOURCE_DIR} -B ${RMM_BUILD_DIR}
    cmake --build ${RMM_BUILD_DIR}

.. _build_config_example:

2. Perform an initial default config, then modify using ccmake ncurses UI:

.. code-block:: bash

    cmake -DRMM_CONFIG=fvp_defcfg -S ${RMM_SOURCE_DIR} -B ${RMM_BUILD_DIR}
    ccmake -S ${RMM_SOURCE_DIR} -B ${RMM_BUILD_DIR}
    cmake --build ${RMM_BUILD_DIR}

3. Perform a debug build and specify a log level:

.. code-block:: bash

    cmake -DRMM_CONFIG=fvp_defcfg -S ${RMM_SOURCE_DIR} -B ${RMM_BUILD_DIR} -DCMAKE_BUILD_TYPE=Debug -DLOG_LEVEL=50
    cmake --build ${RMM_BUILD_DIR}

4. Perform a documentation build:

.. code-block:: bash

    cmake -DRMM_CONFIG=fvp_defcfg -S ${RMM_SOURCE_DIR} -B ${RMM_BUILD_DIR} -DRMM_DOCS=ON
    cmake --build ${RMM_BUILD_DIR} -- docs

5. Perform a clean verbose build:

.. code-block:: bash

    cmake -DRMM_CONFIG=fvp_defcfg -S ${RMM_SOURCE_DIR} -B ${RMM_BUILD_DIR}
    cmake --build ${RMM_BUILD_DIR} --clean-first --verbose

6. Perform a build with Ninja Genenerator:

.. code-block:: bash

    cmake -DRMM_CONFIG=fvp_defcfg -S ${RMM_SOURCE_DIR} -B ${RMM_BUILD_DIR} -DCMAKE_BUILD_TYPE=${BUILD_TYPE} -G "Ninja" -DLOG_LEVEL=50
    cmake --build ${RMM_BUILD_DIR}

7. Perform a build with Ninja Multi Config Genenerator:

.. code-block:: bash

    cmake -DRMM_CONFIG=fvp_defcfg -S ${RMM_SOURCE_DIR} -B ${RMM_BUILD_DIR} -G "Ninja Multi-Config" -DLOG_LEVEL=50
    cmake --build ${RMM_BUILD_DIR} --config ${BUILD_TYPE}

8. Perform a Cppcheck static analysis:

.. code-block:: bash

    cmake -DRMM_CONFIG=fvp_defcfg -DRMM_STATIC_ANALYSIS_CPPCHECK=ON -S ${RMM_SOURCE_DIR} -B ${RMM_BUILD_DIR}
    cmake --build ${RMM_BUILD_DIR} -- cppcheck
    cat ${BUILD_DIR}/tools/cppcheck/cppcheck.xml

9. Perform a Cppcheck static analysis with CERT_C/MISRA/THREAD SAFETY (example with MISRA):

.. code-block:: bash

    cmake -DRMM_CONFIG=fvp_defcfg -DRMM_STATIC_ANALYSIS_CPPCHECK=ON -DRMM_STATIC_ANALYSIS_CPPCHECK_CHECKER_MISRA=ON -S ${RMM_SOURCE_DIR} -B ${RMM_BUILD_DIR}
    cmake --build ${RMM_BUILD_DIR} -- cppcheck
    cat ${BUILD_DIR}/tools/cppcheck/cppcheck.xml

10. Perform a checkpatch analysis:

Run checkpatch on commits in the current branch against BASE_COMMIT (default origin/master):

.. code-block:: bash

    cmake -DRMM_CONFIG=fvp_defcfg -S ${RMM_SOURCE_DIR} -B ${RMM_BUILD_DIR}
    cmake --build ${RMM_BUILD_DIR} -- checkpatch

Run checkpatch on entire codebase:

.. code-block:: bash

    cmake -DRMM_CONFIG=fvp_defcfg -S ${RMM_SOURCE_DIR} -B ${RMM_BUILD_DIR}
    cmake --build ${RMM_BUILD_DIR} -- checkcodebase

11. Perform a checkspdx analysis:

Run checkspdx on commits in the current branch against BASE_COMMIT (default origin/master):

.. code-block:: bash

    cmake -DRMM_CONFIG=fvp_defcfg -S ${RMM_SOURCE_DIR} -B ${RMM_BUILD_DIR}
    cmake --build ${RMM_BUILD_DIR} -- checkspdx-patch

Run checkspdx on entire codebase:

.. code-block:: bash

    cmake -DRMM_CONFIG=fvp_defcfg -S ${RMM_SOURCE_DIR} -B ${RMM_BUILD_DIR}
    cmake --build ${RMM_BUILD_DIR} -- checkspdx-codebase

13. Check header file include order:

Run checkincludes-patch on commits in the current branch against BASE_COMMIT (default origin/master):

.. code-block:: bash

    cmake -DRMM_CONFIG=fvp_defcfg -S ${RMM_SOURCE_DIR} -B ${RMM_BUILD_DIR}
    cmake --build ${RMM_BUILD_DIR} -- checkincludes-patch

Run checkincludes on entire codebase:

.. code-block:: bash

    cmake -DRMM_CONFIG=fvp_defcfg -S ${RMM_SOURCE_DIR} -B ${RMM_BUILD_DIR}
    cmake --build ${RMM_BUILD_DIR} -- checkincludes-codebase

14. Perform unit tests on development host:

Build and run unit tests on host platform. It is recommended to enable the
Debug build of RMM.

.. code-block:: bash

    cmake -DRMM_CONFIG=host_defcfg -DHOST_VARIANT=host_test -DCMAKE_BUILD_TYPE=Debug -S ${RMM_SOURCE_DIR} -B ${RMM_BUILD_DIR}
    cmake --build ${RMM_BUILD_DIR} -- run-unittests

Run unittests for a specific test group(s) (e.g. unittests whose group starts with 'xlat')

.. code-block:: bash

    cmake -DRMM_CONFIG=host_defcfg -DHOST_VARIANT=host_test -DCMAKE_BUILD_TYPE=Debug -S ${RMM_SOURCE_DIR} -B ${RMM_BUILD_DIR}
    cmake --build ${RMM_BUILD_DIR} -- build -j
    ${RMM_BUILD_DIR}/Debug/rmm.elf -gxlat -v -r${NUMBER_OF_TEST_ITERATIONS}

15. Generate Coverage Report.

It is possible to generate a coverage report for a last execution of the host
platform (whichever the variant) by using the `run-coverage` build target.

For example, to generate coverate report on the whole set of unittests:

.. code-block:: bash

    cmake -DRMM_CONFIG=host_defcfg -DHOST_VARIANT=host_test -DRMM_COVERAGE=ON -DCMAKE_BUILD_TYPE=Debug -S ${RMM_SOURCE_DIR} -B ${RMM_BUILD_DIR}
    cmake --build ${RMM_BUILD_DIR} -- run-unittests
    cmake --build ${RMM_BUILD_DIR} -- run-coverage

Run coverage analysis on a specific set of unittests (e.g. unittests whose group starts with 'xlat')

.. code-block:: bash

    cmake -DRMM_CONFIG=host_defcfg -DHOST_VARIANT=host_test -DRMM_COVERAGE=ON -DCMAKE_BUILD_TYPE=Debug -S ${RMM_SOURCE_DIR} -B ${RMM_BUILD_DIR}
    cmake --build ${RMM_BUILD_DIR} -- build -j
    ${RMM_BUILD_DIR}/Debug/rmm.elf -gxlat
    cmake --build ${RMM_BUILD_DIR} -- run-coverage

Run coverage analysis on the `host_build` variant of host platform:

.. code-block:: bash

    cmake -DRMM_CONFIG=host_defcfg -DHOST_VARIANT=host_build -DRMM_COVERAGE=ON -DCMAKE_BUILD_TYPE=Debug -S ${RMM_SOURCE_DIR} -B ${RMM_BUILD_DIR}
    ${RMM_BUILD_DIR}/Debug/rmm.elf
    cmake --build ${RMM_BUILD_DIR} -- run-coverage

The above commands will automatically generate the HTML coverage report in folder
`build/Debug/coverage` within the build directory. The HTML generation can be
disabled by setting `RMM_HTML_COV_REPORT=OFF`.

.. _build_options_table:

###################
RMM Build Options
###################

The |RMM| build system supports the following CMake build options.

.. csv-table:: RMM CMake Options Table
   :header: "Option", "Valid values", "Default", "Description"

   RMM_CONFIG			,			,			,"Platform build configuration, eg: fvp_defcfg for the FVP"
   RMM_ARCH			,aarch64 | fake_host	,aarch64		,"Target Architecture for RMM build"
   RMM_MAX_SIZE			,			,0x0			,"Maximum size for RMM image"
   MAX_CPUS			,			,16			,"Maximum number of CPUs supported by RMM"
   GRANULE_SIZE			,			,4096			,"Granule Size used by RMM"
   RMM_DOCS			,ON | OFF		,OFF			,"RMM Documentation build"
   CMAKE_BUILD_TYPE		,Debug | Release	,Release		,"CMake Build type"
   CMAKE_CONFIGURATION_TYPES	,Debug & Release	,Debug & Release	,"Multi-generator configuration types"
   CMAKE_DEFAULT_BUILD_TYPE	,Debug | Release	,Release		,"Default multi-generator configuration type"
   MbedTLS_BUILD_TYPE		,Debug | Release	,Release		,"MbedTLS build type"
   RMM_PLATFORM			,fvp | host		,			,"Platform to build"
   RMM_TOOLCHAIN		,gnu | llvm		,			,"Toolchain name"
   LOG_LEVEL			,			,40			,"Log level to apply for RMM (0 - 50)"
   RMM_STATIC_ANALYSIS		,			,			,"Enable static analysis checkers"
   RMM_STATIC_ANALYSIS_CPPCHECK				,ON | OFF	,ON	,"Enable Cppcheck static analysis"
   RMM_STATIC_ANALYSIS_CPPCHECK_CHECKER_CERT_C		,ON | OFF	,ON	,"Enable Cppcheck's SEI CERT C checker"
   RMM_STATIC_ANALYSIS_CPPCHECK_CHECKER_MISRA		,ON | OFF	,ON	,"Enable Cppcheck's MISRA C:2012 checker"
   RMM_STATIC_ANALYSIS_CPPCHECK_CHECKER_THREAD_SAFETY	,ON | OFF	,ON	,"Enable Cppcheck's thread safety checker"
   RMM_UART_ADDR		,			,0x0			,"Base addr of UART to be used for RMM logs"
   PLAT_CMN_CTX_MAX_XLAT_TABLES ,			,0			,"Maximum number of translation tables used by the runtime context"
   PLAT_CMN_EXTRA_MMAP_REGIONS	,			,0			,"Extra platform mmap regions that need to be mapped in S1 xlat tables"
   RMM_NUM_PAGES_PER_STACK	,			,3			,"Number of pages to use per CPU stack"
   MBEDTLS_ECP_MAX_OPS		,248 -			,1000			,"Number of max operations per ECC signing iteration"
   RMM_FPU_USE_AT_REL2		,ON | OFF		,OFF(fake_host) ON(aarch64),"Enable FPU/SIMD usage in RMM."
   RMM_MAX_GRANULES		,			,0			,"Maximum number of memory granules available to the system"
   HOST_VARIANT			,host_build | host_test	,host_build		,"Variant to build for the host platform. Only available when RMM_PLATFORM=host"
   RMM_COVERAGE 		,ON | OFF		,OFF			,"Enable coverage analysis"
   RMM_HTML_COV_REPORT		,ON | OFF		,ON			,"Enable HTML output report for coverage analysis"

.. _llvm_build:

################
RMM LLVM Build
################

RMM can be built using LLVM Toolchain (Clang). To build using LLVM
toolchain, set RMM_TOOLCHAIN=llvm during configuration stage.

.. _fake_host_build:

#####################
RMM Fake Host Build
#####################

RMM also provides a ``fake_host`` target architecture which allows the code to
be built natively on the host using the host toolchain. To build for
``fake_host`` architecture, set RMM_CONFIG=host_defcfg during the
configuration stage.
