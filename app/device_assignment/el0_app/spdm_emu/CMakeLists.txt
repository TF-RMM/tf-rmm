#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

# Make this library as an empty interface library when RMM_V1_1 is not set or
# for CBMC build
if(RMM_CBMC_STATIC_ANALYSIS)
    add_library(rmm-pci_tdisp_requester_lib INTERFACE)
    return()
endif()

set(SPDM_EMU_SOURCE_DIR "${RMM_SOURCE_DIR}/ext/spdm-emu")

# Patch spdm-emu
set(SPDM_EMU_PATCH_DIR "${RMM_SOURCE_DIR}/configs/spdm-emu")
set(SPDM_EMU_PATCH_FILES
    "${SPDM_EMU_PATCH_DIR}/0001-Do-not-store-tdisp_interface_response.patch")

Git_Apply_Patches(${SPDM_EMU_SOURCE_DIR} "${SPDM_EMU_PATCH_FILES}")

#
# Add rmm-pci_doe_requester_lib
#

add_library(rmm-pci_doe_requester_lib)

target_link_libraries(rmm-pci_doe_requester_lib
    PUBLIC  rmm-spdm_requester
    PRIVATE rmm-lib-common
            rmm-lib-debug)

target_include_directories(rmm-pci_doe_requester_lib
    PUBLIC  "${SPDM_EMU_SOURCE_DIR}/include"
    PRIVATE "${RMM_SOURCE_DIR}/app/device_assignment/el0_app/spdm_requester")

target_sources(rmm-pci_doe_requester_lib
    PRIVATE "${SPDM_EMU_SOURCE_DIR}/library/pci_doe_requester_lib/pci_doe_spdm_vendor_send_receive.c")

#
# Add rmm-pci_tdisp_requester_lib library
#

add_library(rmm-pci_tdisp_requester_lib)

target_compile_options(rmm-pci_tdisp_requester_lib
    PRIVATE
        "-Wno-unused-parameter")

target_link_libraries(rmm-pci_tdisp_requester_lib
    PUBLIC  rmm-pci_doe_requester_lib
    PRIVATE rmm-lib-common
            rmm-lib-debug)

target_include_directories(rmm-pci_tdisp_requester_lib
    PUBLIC  "${SPDM_EMU_SOURCE_DIR}/include"
    PRIVATE "${RMM_SOURCE_DIR}/app/device_assignment/el0_app/spdm_requester")

target_sources(rmm-pci_tdisp_requester_lib
    PRIVATE "${SPDM_EMU_SOURCE_DIR}/library/pci_tdisp_requester_lib/pci_tdisp_req_get_version.c"
            "${SPDM_EMU_SOURCE_DIR}/library/pci_tdisp_requester_lib/pci_tdisp_req_get_capabilities.c"
            "${SPDM_EMU_SOURCE_DIR}/library/pci_tdisp_requester_lib/pci_tdisp_req_get_interface_report.c"
            "${SPDM_EMU_SOURCE_DIR}/library/pci_tdisp_requester_lib/pci_tdisp_req_get_interface_state.c"
            "${SPDM_EMU_SOURCE_DIR}/library/pci_tdisp_requester_lib/pci_tdisp_req_lock_interface.c"
            "${SPDM_EMU_SOURCE_DIR}/library/pci_tdisp_requester_lib/pci_tdisp_req_start_interface.c"
            "${SPDM_EMU_SOURCE_DIR}/library/pci_tdisp_requester_lib/pci_tdisp_req_stop_interface.c"
            "${SPDM_EMU_SOURCE_DIR}/library/pci_tdisp_requester_lib/pci_tdisp_send_receive.c")
