#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

find_program(RMM_CPPCHECK_EXE "cppcheck" DOC "Path to Cppcheck")

if(NOT RMM_CPPCHECK_EXE)
  message(FATAL_ERROR "Could not find cppcheck executable.")
endif()

#
# Set up checkers.
#
set(cppcheck-flags)

list(APPEND cppcheck-flags "--enable=all")
list(APPEND cppcheck-flags "--xml")
list(APPEND cppcheck-flags "--xml-version=2")
list(APPEND cppcheck-flags "--template=gcc")


if(CPPCHECK_MISRA)
    list(APPEND cppcheck-flags "--addon=${SOURCE_DIR}/tools/cppcheck/misra.json")
    set(CPPCHECK_OUTPUT "${BUILD_DIR}/tools/cppcheck/cppcheck_misra.xml")
    set(CPPCHECK_BUILD_DIR "${BUILD_DIR}/tools/cppcheck/dump_misra")
else()
    set(CPPCHECK_OUTPUT "${BUILD_DIR}/tools/cppcheck/cppcheck.xml")
    set(CPPCHECK_BUILD_DIR "${BUILD_DIR}/tools/cppcheck/dump")
endif()

list(APPEND cppcheck-flags "--output-file=${CPPCHECK_OUTPUT}")
list(APPEND cppcheck-flags "--cppcheck-build-dir=${CPPCHECK_BUILD_DIR}")

#
# Exclude files or directories we don't want to receive warnings about.
#
list(APPEND cppcheck-flags "-i${SOURCE_DIR}/ext/")
list(APPEND cppcheck-flags "-i${SOURCE_DIR}/lib/libc")

#
# If you want to suppress specific files without using an inline suppression,
# do it in `suppressions.txt`.
#
list(APPEND cppcheck-flags
    "--inline-suppr" # Allow inline suppressions
    "--suppressions-list=${SOURCE_DIR}/tools/cppcheck/suppressions.txt")

#
# Configure the platform file. This communicates certain implementation details to
# Cppcheck and avoid false positives.
#
set(toolchain-xml
    "${SOURCE_DIR}/tools/cppcheck-aarch64-platform.xml")

list(APPEND cppcheck-flags "--platform=${toolchain-xml}")
set(COMPILE_COMMANDS_FILE "${BUILD_DIR}/compile_commands.json")
if(NOT EXISTS "${COMPILE_COMMANDS_FILE}")
    message(FATAL_ERROR "Please configure with -DCMAKE_EXPORT_COMPILE_COMMANDS=ON.")
endif()

#
# Create the output directory
#
file(MAKE_DIRECTORY "${CPPCHECK_BUILD_DIR}")

set(EXE_CPPCHECK_TWICE)

#
# Workaround for "internal errors" reported for cppcheck-misra.
# Run CPPCheck 2nd time if the output file is not created.
#
if(CPPCHECK_MISRA AND (NOT EXISTS "${CPPCHECK_OUTPUT}"))
    set(EXE_CPPCHECK_TWICE 1)
endif()

execute_process(
    WORKING_DIRECTORY ${SOURCE_DIR}
    COMMAND ${RMM_CPPCHECK_EXE}
      --project=${COMPILE_COMMANDS_FILE} ${cppcheck-flags}
    )

if(EXE_CPPCHECK_TWICE)
    execute_process(
        WORKING_DIRECTORY ${SOURCE_DIR}
        COMMAND ${RMM_CPPCHECK_EXE}
          --project=${COMPILE_COMMANDS_FILE} ${cppcheck-flags}
    )
endif()
