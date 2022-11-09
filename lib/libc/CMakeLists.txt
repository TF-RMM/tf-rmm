#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

if(NOT RMM_ARCH STREQUAL fake_host)
    add_library(rmm-lib-libc)

    target_link_libraries(rmm-lib-libc
    PUBLIC rmm-lib-arch
           rmm-lib-common
           rmm-lib-debug)

    target_include_directories(rmm-lib-libc SYSTEM
        PUBLIC "include")

    target_sources(rmm-lib-libc
        PRIVATE "src/abort.c"
            "src/assert.c"
            "src/memcmp.c"
            "src/memcpy.c"
            "src/memmove.c"
            "src/printf.c"
            "src/strlen.c"
            "src/strcmp.c"
            "src/strlcpy.c"
            "src/strncmp.c"
            "src/strnlen.c")

    target_sources(rmm-lib-libc
        PRIVATE
           "src/aarch64/memset.S")

target_compile_definitions(rmm-lib-libc
    PRIVATE "PRINTF_DISABLE_SUPPORT_FLOAT")
else()
   add_library(rmm-lib-libc INTERFACE)
endif()
