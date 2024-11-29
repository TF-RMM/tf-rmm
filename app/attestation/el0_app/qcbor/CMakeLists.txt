#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

# The QCBOR library is not included in the CBMC analysis
if(RMM_CBMC_STATIC_ANALYSIS)
    add_library(qcbor INTERFACE)
    return()
endif()

#
# Set qcbor options to not use FPU.
#
set(QCBOR_OPT_DISABLE_FLOAT_HW_USE  ON CACHE BOOL "Override QCBOR flag" FORCE)
set(QCBOR_OPT_DISABLE_FLOAT_ALL     ON CACHE BOOL "Override QCBOR flag" FORCE)

#
# Add the qcbor subdirectory.
#
add_subdirectory("${RMM_SOURCE_DIR}/ext/qcbor" "${CMAKE_BINARY_DIR}/ext/qcbor")

target_link_libraries(qcbor
       PRIVATE
       rmm-lib-libc
)

# Add the relevant build flags.
string(PREPEND qcbor_C_FLAGS "${CMAKE_C_FLAGS} ")
string(PREPEND qcbor_C_FLAGS "-Wno-maybe-uninitialized ")

string(REPLACE " " ";" qcbor_C_FLAGS ${qcbor_C_FLAGS})

#
# qcbor's build system ignores and overwrites the flags we specify in our
# toolchain files. Un-overwrite them, because they're there for a good reason.
#
target_include_directories(qcbor
    PUBLIC "${RMM_SOURCE_DIR}/ext/qcbor/inc"
)

target_compile_options(qcbor
    PRIVATE
        ${qcbor_C_FLAGS}
)
