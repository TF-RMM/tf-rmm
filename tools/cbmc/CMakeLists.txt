#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#
include("SourceCollectHelpers.cmake")

arm_config_option(
  NAME RMM_CBMC_VIEWER_OUTPUT
  HELP "Use XML format for CBMC output and generate cbmc-viewer report."
  DEFAULT OFF)

arm_config_option(
    NAME RMM_CBMC_SINGLE_TESTBENCH
    HELP "Run CBMC on a single testbench instead on all of them."
    DEFAULT OFF)

if("${RMM_CBMC_STATIC_ANALYSIS}")

  set (TESTBENCH_DIR "${CMAKE_CURRENT_SOURCE_DIR}/testbenches")

  if (NOT (${HOST_VARIANT} STREQUAL "host_cbmc"))
    message(FATAL_ERROR "cbmc analysis requires host variant `host_cbmc`. (Add `-DHOST_VARIANT=host_cbmc`)")
  endif()

  file(GLOB_RECURSE TESTBENCH_FILES "${TESTBENCH_DIR}/*.c")
  if(RMM_CBMC_SINGLE_TESTBENCH)
    set(TESTBENCH_NAMES ${TESTBENCH_FILES})
    list(TRANSFORM TESTBENCH_NAMES REPLACE "\\.c" "")
    list(TRANSFORM TESTBENCH_NAMES REPLACE "${TESTBENCH_DIR}/" "")
    if (NOT "${RMM_CBMC_SINGLE_TESTBENCH}" IN_LIST TESTBENCH_NAMES)
      message(STATUS "Invalid testbench name '${RMM_CBMC_SINGLE_TESTBENCH}'")
      message(STATUS "The valid options are: ")
      foreach(tb ${TESTBENCH_NAMES})
        message(STATUS "  ${tb}")
      endforeach()
      message(FATAL_ERROR "Invalid testbench name '${RMM_CBMC_SINGLE_TESTBENCH}'")
    else()
      set(TESTBENCH_FILES "${TESTBENCH_DIR}/${RMM_CBMC_SINGLE_TESTBENCH}.c")
    endif()
  endif()

  #
  # Create the list of source files and include directories that are to be
  # included in the analysis.
  #

  set(rmm_implementation_srcs)
  set(rmm_implementation_includes)

  add_source_and_include_recursively(rmm-runtime)

  list(APPEND rmm_implementation_includes
    "-I${CMAKE_CURRENT_SOURCE_DIR}/include"
    "-I${CMAKE_CURRENT_SOURCE_DIR}/testbenches")

  list(REMOVE_DUPLICATES rmm_implementation_includes)
  list(REMOVE_DUPLICATES rmm_implementation_srcs)

  # Filter source files that are not analysed by CBMC
  set(src_filters
    "lib/allocator/src"
    "lib/timers/src"
    "plat/common/src"
    )

  foreach(filter ${src_filters})
    list(FILTER rmm_implementation_srcs EXCLUDE REGEX "${filter}")
  endforeach()

  #
  # Rules for running cbmc analysis
  #
  add_custom_target(cbmc-coverage
  WORKING_DIRECTORY "${CMAKE_SOURCE_DIR}"
  COMMAND ${CMAKE_COMMAND}
    -DRMM_CBMC_CONFIGURATION=COVERAGE
    -DSOURCE_DIR=${CMAKE_SOURCE_DIR}
    -DBINARY_DIR=${CMAKE_CURRENT_BINARY_DIR}
    -DTESTBENCH_DIR="${TESTBENCH_DIR}"
    -DTESTBENCH_FILES="${TESTBENCH_FILES}"
    -DRMM_IMP_SRCS="${rmm_implementation_srcs}"
    -DRMM_IMP_INCS="${rmm_implementation_includes}"
    -P ${CMAKE_SOURCE_DIR}/tools/cbmc/CheckCBMC.cmake
  )

  add_custom_target(cbmc-analysis
  WORKING_DIRECTORY "${CMAKE_SOURCE_DIR}"
  COMMAND ${CMAKE_COMMAND}
    -DRMM_CBMC_CONFIGURATION=ANALYSIS
    -DRMM_CBMC_VIEWER_OUTPUT=${RMM_CBMC_VIEWER_OUTPUT}
    -DSOURCE_DIR=${CMAKE_SOURCE_DIR}
    -DBINARY_DIR=${CMAKE_CURRENT_BINARY_DIR}
    -DTESTBENCH_DIR="${TESTBENCH_DIR}"
    -DTESTBENCH_FILES="${TESTBENCH_FILES}"
    -DRMM_IMP_SRCS="${rmm_implementation_srcs}"
    -DRMM_IMP_INCS="${rmm_implementation_includes}"
    -P ${CMAKE_SOURCE_DIR}/tools/cbmc/CheckCBMC.cmake
  )

  add_custom_target(cbmc-assert
  WORKING_DIRECTORY "${CMAKE_SOURCE_DIR}"
  COMMAND ${CMAKE_COMMAND}
    -DRMM_CBMC_CONFIGURATION=ASSERT
    -DRMM_CBMC_VIEWER_OUTPUT=${RMM_CBMC_VIEWER_OUTPUT}
    -DSOURCE_DIR=${CMAKE_SOURCE_DIR}
    -DBINARY_DIR=${CMAKE_CURRENT_BINARY_DIR}
    -DTESTBENCH_DIR="${TESTBENCH_DIR}"
    -DTESTBENCH_FILES="${TESTBENCH_FILES}"
    -DRMM_IMP_SRCS="${rmm_implementation_srcs}"
    -DRMM_IMP_INCS="${rmm_implementation_includes}"
    -P ${CMAKE_SOURCE_DIR}/tools/cbmc/CheckCBMC.cmake
  )

  add_custom_target(cbmc-gcc
  WORKING_DIRECTORY "${CMAKE_SOURCE_DIR}"
  COMMAND ${CMAKE_COMMAND}
    -DRMM_CBMC_CONFIGURATION=GCC
    -DSOURCE_DIR=${CMAKE_SOURCE_DIR}
    -DBINARY_DIR=${CMAKE_CURRENT_BINARY_DIR}
    -DTESTBENCH_DIR="${TESTBENCH_DIR}"
    -DTESTBENCH_FILES="${TESTBENCH_FILES}"
    -DRMM_IMP_SRCS="${rmm_implementation_srcs}"
    -DRMM_IMP_INCS="${rmm_implementation_includes}"
    -P ${CMAKE_SOURCE_DIR}/tools/cbmc/CheckCBMC.cmake
  )

endif() # RMM_CBMC_STATIC_ANALYSIS