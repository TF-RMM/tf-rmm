#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#
include("SourceCollectHelpers.cmake")

if("${RMM_CBMC_STATIC_ANALYSIS}")

  if (NOT (${HOST_VARIANT} STREQUAL "host_cbmc"))
    message(FATAL_ERROR "cbmc analysis requires host variant `host_cbmc`. (Add `-DHOST_VARIANT=host_cbmc`)")
  endif()

  #
  # Create the list of source files and include directories that are to be
  # included in the analysis.
  #

  set(rmm_implementation_srcs)
  set(rmm_implementation_includes)

  add_source_and_include_recursively(rmm-runtime)

  list(APPEND rmm_implementation_srcs
    "${CMAKE_CURRENT_SOURCE_DIR}/src/tb.c"
    "${CMAKE_CURRENT_SOURCE_DIR}/src/tb_common.c"
    "${CMAKE_CURRENT_SOURCE_DIR}/src/tb_granules.c")

  list(APPEND rmm_implementation_includes
    "-I${CMAKE_CURRENT_SOURCE_DIR}/include"
    "-I${CMAKE_CURRENT_SOURCE_DIR}/testbenches")

  list(REMOVE_DUPLICATES rmm_implementation_includes)
  list(REMOVE_DUPLICATES rmm_implementation_srcs)

  # Filter source files that are not analysed by CBMC
  set(src_filters
    "lib/allocator/src"
    "lib/arch/src"
    "lib/attestation/src"
    "lib/measurement/src"
    "lib/rmm_el3_ifc/src"
    "lib/timers/src"
    "lib/xlat/src"
    "plat/common/src"
    "runtime/rsi"
    "runtime/core/run.c"
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
    -DTESTBENCH_DIR="${CMAKE_CURRENT_SOURCE_DIR}/testbenches"
    -DRMM_IMP_SRCS="${rmm_implementation_srcs}"
    -DRMM_IMP_INCS="${rmm_implementation_includes}"
    -P ${CMAKE_SOURCE_DIR}/tools/cbmc/CheckCBMC.cmake
  )

  add_custom_target(cbmc-analysis
  WORKING_DIRECTORY "${CMAKE_SOURCE_DIR}"
  COMMAND ${CMAKE_COMMAND}
    -DRMM_CBMC_CONFIGURATION=ANALYSIS
    -DSOURCE_DIR=${CMAKE_SOURCE_DIR}
    -DBINARY_DIR=${CMAKE_CURRENT_BINARY_DIR}
    -DTESTBENCH_DIR="${CMAKE_CURRENT_SOURCE_DIR}/testbenches"
    -DRMM_IMP_SRCS="${rmm_implementation_srcs}"
    -DRMM_IMP_INCS="${rmm_implementation_includes}"
    -P ${CMAKE_SOURCE_DIR}/tools/cbmc/CheckCBMC.cmake
  )

  add_custom_target(cbmc-assert
  WORKING_DIRECTORY "${CMAKE_SOURCE_DIR}"
  COMMAND ${CMAKE_COMMAND}
    -DRMM_CBMC_CONFIGURATION=ASSERT
    -DSOURCE_DIR=${CMAKE_SOURCE_DIR}
    -DBINARY_DIR=${CMAKE_CURRENT_BINARY_DIR}
    -DTESTBENCH_DIR="${CMAKE_CURRENT_SOURCE_DIR}/testbenches"
    -DRMM_IMP_SRCS="${rmm_implementation_srcs}"
    -DRMM_IMP_INCS="${rmm_implementation_includes}"
    -P ${CMAKE_SOURCE_DIR}/tools/cbmc/CheckCBMC.cmake
  )

endif() # RMM_CBMC_STATIC_ANALYSIS