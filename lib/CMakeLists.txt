#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

list(APPEND CMAKE_MODULE_PATH "${CMAKE_SOURCE_DIR}/tools/common")
include(GitUtils)

add_library(rmm-lib INTERFACE)

target_link_libraries(rmm-lib
    INTERFACE rmm-lib-allocator
              rmm-lib-arch
              rmm-lib-attestation
              rmm-lib-common
              rmm-lib-console
              rmm-lib-debug
              rmm-lib-gic
              rmm-lib-granule
              rmm-lib-measurement
              rmm-lib-rmm_el3_ifc
              rmm-lib-smc
              rmm-lib-s2tt
              rmm-lib-slot_buf
              rmm-lib-xlat
              t_cose)

add_subdirectory("allocator")
add_subdirectory("arch")
add_subdirectory("attestation")
add_subdirectory("common")
add_subdirectory("console")
add_subdirectory("debug")
add_subdirectory("gic")
add_subdirectory("granule")
add_subdirectory("mbedtls")
add_subdirectory("measurement")
add_subdirectory("qcbor")
add_subdirectory("rmm_el3_ifc")
add_subdirectory("smc")
add_subdirectory("s2tt")
add_subdirectory("slot_buf")
add_subdirectory("t_cose")
add_subdirectory("xlat")

# Device Assignment feature in RMM v1.1 needs rmm-lib-spdm_requester
if(RMM_V1_1)
    target_link_libraries(rmm-lib INTERFACE rmm-lib-spdm_requester)
    add_subdirectory("spdm_requester")
endif()
