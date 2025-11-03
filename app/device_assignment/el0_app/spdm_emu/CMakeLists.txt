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
    "${SPDM_EMU_PATCH_DIR}/0001-Do-not-store-tdisp_interface_response.patch"
    "${SPDM_EMU_PATCH_DIR}/0002-Skip-SPDM-Responder-Validator-components.patch")

Git_Apply_Patches(${SPDM_EMU_SOURCE_DIR} "${SPDM_EMU_PATCH_FILES}")

if(RMM_ARCH STREQUAL fake_host AND RMM_V1_1)
    # Initialize spdm-emu submodules (only libspdm, not SPDM-Responder-Validator)
    execute_process(COMMAND ${GIT_EXECUTABLE} submodule update --init --depth 1 libspdm
            WORKING_DIRECTORY ${SPDM_EMU_SOURCE_DIR}
            RESULT_VARIABLE GIT_SPDM_SUBMOD_RESULT)
    if(NOT GIT_SPDM_SUBMOD_RESULT EQUAL "0")
        message(FATAL_ERROR "git submodule update for ext/spdm-emu/libspdm failed with error: ${GIT_SPDM_SUBMOD_RESULT}")
    endif()

    # Initialize only mbedtls within libspdm (not openssl or cmocka)
    execute_process(COMMAND ${GIT_EXECUTABLE} submodule update --init --depth 1 os_stub/mbedtlslib/mbedtls
            WORKING_DIRECTORY ${SPDM_EMU_SOURCE_DIR}/libspdm
            RESULT_VARIABLE GIT_SPDM_MBEDTLS_RESULT)
    if(NOT GIT_SPDM_MBEDTLS_RESULT EQUAL "0")
        message(FATAL_ERROR "git submodule update for ext/spdm-emu/libspdm/os_stub/mbedtlslib/mbedtls failed with error: ${GIT_SPDM_MBEDTLS_RESULT}")
    endif()

    set(SPDM_EMU_BINARY_DIR "${CMAKE_BINARY_DIR}/ext/spdm-emu")
    set(SPDM_EMU_RESPONDER_BIN
        "${SPDM_EMU_BINARY_DIR}/bin/spdm_responder_emu${CMAKE_EXECUTABLE_SUFFIX}")
    string(TOLOWER "${CMAKE_HOST_SYSTEM_PROCESSOR}" SPDM_EMU_HOST_PROCESSOR)
    if(SPDM_EMU_HOST_PROCESSOR MATCHES "^(x86_64|amd64)$")
        set(SPDM_EMU_ARCH x64)
    elseif(SPDM_EMU_HOST_PROCESSOR MATCHES "^(i[3-6]86)$")
        set(SPDM_EMU_ARCH ia32)
    elseif(SPDM_EMU_HOST_PROCESSOR MATCHES "^(aarch64|arm64)$")
        set(SPDM_EMU_ARCH aarch64)
    elseif(SPDM_EMU_HOST_PROCESSOR MATCHES "^(arm|armv[0-9]+l)$")
        set(SPDM_EMU_ARCH arm)
    else()
        message(FATAL_ERROR "Unsupported host arch for spdm-emu: ${CMAKE_HOST_SYSTEM_PROCESSOR}")
    endif()

    # Always use GCC for spdm-emu to avoid LLVM LTO plugin issues
    # (spdm-emu is a host utility and doesn't need to match target toolchain)
    set(SPDM_EMU_TOOLCHAIN GCC)

    add_custom_command(
        OUTPUT "${SPDM_EMU_RESPONDER_BIN}"
        COMMAND ${CMAKE_COMMAND} -S "${SPDM_EMU_SOURCE_DIR}" -B "${SPDM_EMU_BINARY_DIR}"
                -DARCH=${SPDM_EMU_ARCH} -DTOOLCHAIN=${SPDM_EMU_TOOLCHAIN} -DTARGET=Release -DCRYPTO=mbedtls
        COMMAND ${CMAKE_COMMAND} --build "${SPDM_EMU_BINARY_DIR}" --target spdm_responder_emu -j
        COMMENT "Building spdm-emu host utilities for fake_host runs"
        WORKING_DIRECTORY "${SPDM_EMU_SOURCE_DIR}")

    add_custom_target(spdm-emu-host-build DEPENDS "${SPDM_EMU_RESPONDER_BIN}")
    set_property(TARGET spdm-emu-host-build PROPERTY USES_TERMINAL TRUE)

    set(SPDM_EMU_STAGE_DIR "${CMAKE_BINARY_DIR}/$<CONFIG>/spdm_emu")
    set(SPDM_EMU_STAGE_KEYS_DIR "${SPDM_EMU_STAGE_DIR}/keys")
    set(SPDM_EMU_STAGE_BIN "${SPDM_EMU_STAGE_DIR}/spdm_responder_emu")

    add_custom_target(stage-spdm-emu ALL
        COMMAND ${CMAKE_COMMAND} -E make_directory "${SPDM_EMU_STAGE_KEYS_DIR}"
        COMMAND ${CMAKE_COMMAND} -E copy_if_different
                "${SPDM_EMU_RESPONDER_BIN}" "${SPDM_EMU_STAGE_BIN}"
        COMMAND ${CMAKE_COMMAND} -E copy_directory
                "${RMM_SOURCE_DIR}/ext/libspdm/unit_test/sample_key" "${SPDM_EMU_STAGE_KEYS_DIR}"
        DEPENDS spdm-emu-host-build
        COMMENT "Staging spdm_responder_emu and keys next to rmm.elf")
endif()

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
        "-Wno-unused-parameter"
        "-Wno-unaligned-access")

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

#
# Add rmm-pci-ide-km-requester-lib library
#

add_library(rmm-pci-ide-km-requester-lib)

target_compile_options(rmm-pci-ide-km-requester-lib
    PRIVATE
        "-Wno-unused-parameter"
        "-Wno-unaligned-access")

target_link_libraries(rmm-pci-ide-km-requester-lib
    PUBLIC  rmm-pci_doe_requester_lib
    PRIVATE rmm-lib-common
            rmm-lib-debug)

target_include_directories(rmm-pci-ide-km-requester-lib
    PUBLIC  "${SPDM_EMU_SOURCE_DIR}/include"
    PRIVATE "${RMM_SOURCE_DIR}/app/device_assignment/el0_app/spdm_requester")

target_sources(rmm-pci-ide-km-requester-lib
    PRIVATE "${SPDM_EMU_SOURCE_DIR}/library/pci_ide_km_requester_lib/pci_ide_km_req_key_prog.c"
            "${SPDM_EMU_SOURCE_DIR}/library/pci_ide_km_requester_lib/pci_ide_km_req_key_set_go.c"
            "${SPDM_EMU_SOURCE_DIR}/library/pci_ide_km_requester_lib/pci_ide_km_req_key_set_stop.c"
            "${SPDM_EMU_SOURCE_DIR}/library/pci_ide_km_requester_lib/pci_ide_km_req_query.c"
            "${SPDM_EMU_SOURCE_DIR}/library/pci_ide_km_requester_lib/pci_ide_km_send_receive.c")
