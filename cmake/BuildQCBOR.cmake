#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

add_subdirectory("ext/qcbor")

#
# Set up qcbor using our own libc. This is done by getting certain properties
# from our libc target and applying them to qcbor - not ideal, but qcbor
# doesn't provide an interface library for us to use.
#
get_target_property(system_includes rmm-lib-libc
    INTERFACE_SYSTEM_INCLUDE_DIRECTORIES)
get_target_property(includes rmm-lib-libc
    INTERFACE_INCLUDE_DIRECTORIES)
get_target_property(definitions rmm-lib-libc
    INTERFACE_COMPILE_DEFINITIONS)
get_target_property(options rmm-lib-libc
    INTERFACE_COMPILE_OPTIONS)

#
# System include directories appear in both the `SYSTEM_INCLUDE_DIRECTORIES` and
# `INCLUDE_DIRECTORIES` properties, so filter them out of the latter.
#
list(REMOVE_ITEM includes ${system_includes})

#
# Target properties that are not set return `<PROPERTY>-NOTFOUND`. Clear any
# variables where this occurred.
#
foreach(set IN ITEMS system_includes includes definitions options)
    if(NOT ${set})
        set(${set})
    endif()
endforeach()

# QCBOR custom definitions
list(APPEND definitions "QCBOR_DISABLE_FLOAT_HW_USE")
list(APPEND definitions "USEFULBUF_DISABLE_ALL_FLOAT")

#
# Create compiler flags from the libc properties we retrieved.
#
list(TRANSFORM definitions PREPEND " -D")

foreach(set IN ITEMS options definitions)
    string(REPLACE ";" " " ${set} "${${set}}")
endforeach()

string(PREPEND qcbor_C_FLAGS "${definitions} ")
# Add the relevant build flags. TODO: Currently CBOR is only passed Release build flag
string(PREPEND qcbor_C_FLAGS "${options} ${CMAKE_C_FLAGS} ${CMAKE_C_FLAGS_RELEASE} ")
string(PREPEND qcbor_C_FLAGS "-Wno-maybe-uninitialized ")

string(REPLACE " " ";" qcbor_C_FLAGS ${qcbor_C_FLAGS})

#
# qcbor's build system ignores and overwrites the flags we specify in our
# toolchain files. Un-overwrite them, because they're there for a good reason.
#
target_include_directories(qcbor
    PUBLIC "${RMM_SOURCE_DIR}/ext/qcbor/inc"
)

target_include_directories(qcbor
    PRIVATE
        ${includes}
        ${system_includes}
)

target_compile_options(qcbor
    PRIVATE
        ${qcbor_C_FLAGS}
)

target_link_libraries(qcbor
	PRIVATE
	rmm-lib-libc
)

link_libraries(qcbor)
