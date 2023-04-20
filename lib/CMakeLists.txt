#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

add_library(rmm-lib INTERFACE)

target_link_libraries(rmm-lib
    INTERFACE rmm-lib-allocator
              rmm-lib-arch
              rmm-lib-attestation
              rmm-lib-common
              rmm-lib-debug
              rmm-lib-gic
              rmm-lib-measurement
              rmm-lib-realm
              rmm-lib-rmm_el3_ifc
              rmm-lib-smc
              rmm-lib-timers
              rmm-lib-xlat
              t_cose)

add_subdirectory("allocator")
add_subdirectory("arch")
add_subdirectory("attestation")
add_subdirectory("common")
add_subdirectory("debug")
add_subdirectory("gic")
add_subdirectory("mbedtls")
add_subdirectory("measurement")
add_subdirectory("qcbor")
add_subdirectory("realm")
add_subdirectory("rmm_el3_ifc")
add_subdirectory("smc")
add_subdirectory("t_cose")
add_subdirectory("timers")
add_subdirectory("xlat")
