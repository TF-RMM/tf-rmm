#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

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

target_compile_definitions(qcbor PRIVATE QCBOR_DISABLE_FLOAT_HW_USE)
target_compile_definitions(qcbor PRIVATE USEFULBUF_DISABLE_ALL_FLOAT)
