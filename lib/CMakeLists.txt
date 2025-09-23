#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

add_library(rmm-lib INTERFACE)

target_link_libraries(rmm-lib
    INTERFACE rmm-lib-arch
              rmm-lib-common
              rmm-lib-console
              rmm-lib-debug
              rmm-lib-gic
              rmm-lib-granule
              rmm-lib-mec
              rmm-lib-rmm_el3_ifc
              rmm-lib-smc
              rmm-lib-s2tt
              rmm-lib-slot_buf
              rmm-lib-stack_protector
              rmm-lib-xlat)

add_subdirectory("arch")
add_subdirectory("common")
add_subdirectory("console")
add_subdirectory("debug")
add_subdirectory("gic")
add_subdirectory("granule")
add_subdirectory("mbedtls")
add_subdirectory("mec")
add_subdirectory("rmm_el3_ifc")
add_subdirectory("smc")
add_subdirectory("s2tt")
add_subdirectory("slot_buf")
add_subdirectory("stack_protector")
add_subdirectory("xlat")
