#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

arm_config_option(
    NAME RMM_STATIC_ANALYSIS
    HELP "Enable static analysis checkers.")

add_subdirectory("cbmc")

#
# Additional static checks build targets
#

#
# Rules for checkpatch
#
add_custom_target(checkcodebase
  WORKING_DIRECTORY "${CMAKE_SOURCE_DIR}"
  COMMAND ${CMAKE_COMMAND} -DCHECKCODEBASE_RUN=1 -P ${CMAKE_SOURCE_DIR}/tools/checkpatch/CheckPatch.cmake
  )

add_custom_target(checkpatch
  WORKING_DIRECTORY "${CMAKE_SOURCE_DIR}"
  COMMAND ${CMAKE_COMMAND} -DCHECKPATCH_RUN=1 -P ${CMAKE_SOURCE_DIR}/tools/checkpatch/CheckPatch.cmake
  )

#
# Rules for checking license and copyright headers
#
add_custom_target(checkspdx-codebase
  WORKING_DIRECTORY "${CMAKE_SOURCE_DIR}"
  COMMAND ${CMAKE_COMMAND} -DCHECKSPDX_CODEBASE=1 -P ${CMAKE_SOURCE_DIR}/tools/checkspdx/CheckSPDX.cmake
  )

add_custom_target(checkspdx-patch
  WORKING_DIRECTORY "${CMAKE_SOURCE_DIR}"
  COMMAND ${CMAKE_COMMAND} -DCHECKSPDX_PATCH=1 -P ${CMAKE_SOURCE_DIR}/tools/checkspdx/CheckSPDX.cmake
  )

#
# Rules for checking header files include order
#
add_custom_target(checkincludes-codebase
  WORKING_DIRECTORY "${CMAKE_SOURCE_DIR}"
  COMMAND ${CMAKE_COMMAND} -DCHECKINCLUDES_CODEBASE=1 -P ${CMAKE_SOURCE_DIR}/tools/checkincludes/CheckIncludes.cmake
  )

add_custom_target(checkincludes-patch
  WORKING_DIRECTORY "${CMAKE_SOURCE_DIR}"
  COMMAND ${CMAKE_COMMAND} -DCHECKINCLUDES_PATCH=1 -P ${CMAKE_SOURCE_DIR}/tools/checkincludes/CheckIncludes.cmake
  )

#
# Rules for running clang-tidy checks
#
# Pass through the value of RMM_TOOLCHAIN as this must be verified before
# clang-tidy can be run.
#
# Also pass through the build directory as this cannot be accessed when the
# clang-tidy target is built.
#
add_custom_target(clang-tidy-codebase
  WORKING_DIRECTORY "${CMAKE_SOURCE_DIR}"
  COMMAND ${CMAKE_COMMAND} -DCLANG-TIDY_CODEBASE=1
    -DRMM_TOOLCHAIN=${RMM_TOOLCHAIN}
    -DBUILD_DIR=${CMAKE_BINARY_DIR}
    -P ${CMAKE_SOURCE_DIR}/tools/clang-tidy/clang-tidy.cmake
  )

add_custom_target(clang-tidy-patch
  WORKING_DIRECTORY "${CMAKE_SOURCE_DIR}"
  COMMAND ${CMAKE_COMMAND} -DCLANG-TIDY_PATCH=1
    -DRMM_TOOLCHAIN=${RMM_TOOLCHAIN}
    -DBUILD_DIR=${CMAKE_BINARY_DIR}
    -P ${CMAKE_SOURCE_DIR}/tools/clang-tidy/clang-tidy.cmake
  )

#
# Rules for running CPPCheck
#
add_custom_target(cppcheck
  WORKING_DIRECTORY "${CMAKE_SOURCE_DIR}"
  COMMAND ${CMAKE_COMMAND}
    -DSOURCE_DIR=${CMAKE_SOURCE_DIR}
    -DBUILD_DIR=${CMAKE_BINARY_DIR}
    -P ${CMAKE_SOURCE_DIR}/tools/cppcheck/CPPCheck.cmake
  )

add_custom_target(cppcheck-misra
  WORKING_DIRECTORY "${CMAKE_SOURCE_DIR}"
  COMMAND ${CMAKE_COMMAND}
    -DSOURCE_DIR=${CMAKE_SOURCE_DIR}
    -DBUILD_DIR=${CMAKE_BINARY_DIR}
    -DCPPCHECK_MISRA=1
    -P ${CMAKE_SOURCE_DIR}/tools/cppcheck/CPPCheck.cmake
  )
