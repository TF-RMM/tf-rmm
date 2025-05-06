#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

# TODO: The C file generating logic is general for all the apps.
# need to move it to a common location somehow.

# The attestation app is not included in the CBMC analysis
if(RMM_CBMC_STATIC_ANALYSIS)
    add_library(rmm-app-attestation-elf INTERFACE)
    return()
endif()

add_subdirectory("mbedtls_attest")
add_subdirectory("qcbor")
add_subdirectory("t_cose")

include(ArmTargetLinkerScript)

find_package(Python3 REQUIRED)
find_program(GEN_APP_BIN "gen_app_bin.py"
    PATHS ${CMAKE_SOURCE_DIR}
    PATH_SUFFIXES app
    DOC "gen_app_bin.py"
    )

# Compile the app as a separate executable (add_library would skip the linking step)
add_executable(rmm-app-attestation-elf)

set(ATTESTATION_APP_ID 211)

arm_config_option(
    NAME ATTESTATION_APP_STACK_SIZE
    HELP "Number of pages to use for the Attestation app stack"
    TYPE STRING
    DEFAULT 2
    ADVANCED)

arm_config_option(
    NAME ATTESTATION_APP_HEAP_SIZE
    HELP "Number of pages to use for the Attestation app heap"
    TYPE STRING
    DEFAULT 3
    ADVANCED)

arm_config_option(
    NAME MBEDTLS_ECP_MAX_OPS
    HELP "Set the number of max operations per ECC signing iteration [0..PSA_INTERRUPTIBLE_MAX_OPS_UNLIMITED]"
    TYPE STRING
    DEFAULT 1000
    ADVANCED)

arm_config_option(
    NAME ATTEST_PLAT_TOKEN_SIZE
    HELP "Maximum size in bytes expected for the Attestation platform token"
    TYPE STRING
    DEFAULT 0x1000
    ADVANCED)

target_compile_definitions(rmm-app-attestation-elf
    PRIVATE "ATTEST_PLAT_TOKEN_SIZE=U(${ATTEST_PLAT_TOKEN_SIZE})")

MATH(EXPR CCA_TOKEN_BUFFER_BYTES "${RMM_CCA_TOKEN_BUFFER} * 0x1000")
if (${CCA_TOKEN_BUFFER_BYTES} LESS ${ATTEST_PLAT_TOKEN_SIZE})
    message(FATAL_ERROR "RMM_CCA_TOKEN_BUFFER size is less than ATTEST_PLAT_TOKEN_SIZE")
endif()

target_compile_definitions(rmm-app-attestation-elf
    PRIVATE "MBEDTLS_ECP_MAX_OPS=${MBEDTLS_ECP_MAX_OPS}U")

target_include_directories(rmm-app-attestation-elf
    PRIVATE
        "src"
        "${CMAKE_CURRENT_SOURCE_DIR}/../../common/include"
        "${CMAKE_CURRENT_SOURCE_DIR}/../rmm_stub/include")

target_link_libraries(rmm-app-attestation-elf
    PRIVATE
        qcbor
        rmm-app-common-el0_app
        rmm-lib-arch
        rmm-lib-common
        rmm-lib-console
        rmm-lib-debug
        rmm-lib-libc
        rmm-lib-smc
        rmm-lib-xlat
        t_cose)

if(RMM_ARCH STREQUAL fake_host)
    target_link_libraries(rmm-app-attestation-elf
        PRIVATE
            rmm-host-support)
endif()

# Target for output directory.
add_custom_target(attest_app_output_dir
    COMMAND "${CMAKE_COMMAND}" -E make_directory "${CMAKE_BINARY_DIR}/$<CONFIG>"
    COMMENT "Creating output directory"
)

add_custom_command(
    COMMAND "${CMAKE_COMMAND}" -E copy_if_different "$<TARGET_FILE:rmm-app-attestation-elf>" "${CMAKE_BINARY_DIR}/$<CONFIG>/rmm_app_attestation.elf"
    COMMAND "${CMAKE_COMMAND}" -E copy_if_different "$<TARGET_FILE:rmm-app-attestation-elf>.map" "${CMAKE_BINARY_DIR}/$<CONFIG>/rmm_app_attestation.map"
    OUTPUT rmm_app_attestation.elf
    DEPENDS rmm-app-attestation-elf attest_app_output_dir)

# Create the dump file using whatever tool comes with the toolchain.
if(CMAKE_OBJDUMP)
    add_custom_command(
        COMMAND "${CMAKE_OBJDUMP}" -dxS "${CMAKE_BINARY_DIR}/$<CONFIG>/rmm_app_attestation.elf" > "${CMAKE_BINARY_DIR}/$<CONFIG>/rmm_app_attestation.dump"
        OUTPUT rmm_app_attestation.dump
        DEPENDS rmm_app_attestation.elf)
endif()

target_sources(rmm-app-attestation-elf
    PRIVATE
        "src/attest_app.c"
        "src/attest_measurement.c"
        "src/attestation_key.c"
        "src/attestation_token.c"
        "src/attestation_utils.c")

if (RMM_ARCH STREQUAL fake_host)
    target_sources(rmm-app-attestation-elf
        PRIVATE "src/fake_host/attest_app_host.c")
endif()

target_link_options(rmm-app-attestation-elf
    PRIVATE "-Wl,-Map=$<TARGET_FILE:rmm-app-attestation-elf>.map")

target_compile_definitions(rmm-app-attestation-elf
    PRIVATE "HEAP_PAGE_COUNT=U(${ATTESTATION_APP_HEAP_SIZE})")

if(NOT RMM_ARCH STREQUAL fake_host)
    set(COMMON_APP_LINKER_SCRIPT "${CMAKE_CURRENT_SOURCE_DIR}/../../common/el0_app/linker.lds")

    arm_target_linker_script(rmm-app-attestation-elf "${COMMON_APP_LINKER_SCRIPT}")

    set_property(TARGET rmm-app-attestation-elf-lds APPEND
        PROPERTY COMPILE_DEFINITIONS "__LINKER__")

    set_property(TARGET rmm-app-attestation-elf-lds APPEND
        PROPERTY COMPILE_DEFINITIONS "GRANULE_SHIFT=U(${GRANULE_SHIFT})")

    # Get the name of the bin file that will contain the app data
    get_filename_component(RAW_DATA_OUTPUT_FILE ${CMAKE_BINARY_DIR}/$<CONFIG>/rmm_app_attestation.bin ABSOLUTE)

    list(APPEND EL0_APP_BIN_LIST "${RAW_DATA_OUTPUT_FILE}")
    set(EL0_APP_BIN_LIST ${EL0_APP_BIN_LIST} PARENT_SCOPE)

    # Add a command that will run the bin file generation. Make it depend on the app elf file
    add_custom_command(
    OUTPUT ${RAW_DATA_OUTPUT_FILE}
    COMMAND ${GEN_APP_BIN}
        --elf-file $<TARGET_FILE:rmm-app-attestation-elf>
        --app-name "attestation_app"
        --app-id ${ATTESTATION_APP_ID}
        --stack-page-count ${ATTESTATION_APP_STACK_SIZE}
        --heap-page-count ${ATTESTATION_APP_HEAP_SIZE}
        --out-bin ${RAW_DATA_OUTPUT_FILE}
    DEPENDS rmm-app-attestation-elf rmm-app-attestation-elf-lds
    )

    # Add a custom target that depends on the bin file. This is necessary so that
    # the bundled image can depend on it.
    add_custom_target(rmm-attestation-app DEPENDS ${RAW_DATA_OUTPUT_FILE} rmm_app_attestation.dump)
else()
    add_custom_target(rmm-attestation-app DEPENDS rmm_app_attestation.dump)
endif()
