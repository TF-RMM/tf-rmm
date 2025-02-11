#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

# TODO: The C file generating logic is general for all the apps.
# need to move it to a common location somehow.

# The dev_assign app is not included in the CBMC analysis
if(RMM_CBMC_STATIC_ANALYSIS)
    return()
endif()

add_subdirectory("mbedtls_da")
add_subdirectory("spdm_requester")
add_subdirectory("spdm_emu")

include(ArmTargetLinkerScript)

find_package(Python3 REQUIRED)
find_program(GEN_APP_BIN "gen_app_bin.py"
    PATHS ${CMAKE_SOURCE_DIR}
    PATH_SUFFIXES app
    DOC "gen_app_bin.py"
    )

# Compile the app as a separate executable (add_library would skip the linking step)
add_executable(rmm-app-dev-assign-elf)

set(RMM_DEV_ASSIGN_APP_ID 110)

arm_config_option(
    NAME DEV_ASSIGN_APP_STACK_SIZE
    HELP "Number of pages to use for the Device Assignment app stack"
    TYPE STRING
    DEFAULT 2
    ADVANCED)

arm_config_option(
    NAME DEV_ASSIGN_APP_HEAP_SIZE
    HELP "Number of pages to use for the Device Assignment app heap"
    TYPE STRING
    DEFAULT 13
    ADVANCED)

target_include_directories(rmm-app-dev-assign-elf
    PRIVATE
        "src"
        "${CMAKE_CURRENT_SOURCE_DIR}/../rmm_stub/include"
        "${CMAKE_CURRENT_SOURCE_DIR}/../../common/include"
        "${RMM_SOURCE_DIR}/app/device_assignment/el0_app/spdm_requester"
        "${RMM_SOURCE_DIR}/app/device_assignment/el0_app/mbedtls_da")

target_link_libraries(rmm-app-dev-assign-elf
    PRIVATE
        rmm-app-common-el0_app
        rmm-app-da-mbedtls
        rmm-pci_tdisp_requester_lib
        rmm-lib-common
        rmm-lib-debug
        rmm-lib-smc
        rmm-lib-xlat
        rmm-spdm_requester)

if(RMM_ARCH STREQUAL fake_host)
    target_link_libraries(rmm-app-dev-assign-elf
        PRIVATE
            rmm-host-el2-el0-cmn)
endif()

# Target for output directory.
add_custom_target(dev_assign_app_output_dir
    COMMAND "${CMAKE_COMMAND}" -E make_directory "${CMAKE_BINARY_DIR}/$<CONFIG>"
    COMMENT "Creating output directory"
)

add_custom_command(
    COMMAND "${CMAKE_COMMAND}" -E copy_if_different "$<TARGET_FILE:rmm-app-dev-assign-elf>" "${CMAKE_CURRENT_BINARY_DIR}/rmm_app_dev_assign.elf"
    COMMAND "${CMAKE_COMMAND}" -E copy_if_different "$<TARGET_FILE:rmm-app-dev-assign-elf>.map" "${CMAKE_BINARY_DIR}/$<CONFIG>/rmm_app_dev-assign.map"
    OUTPUT rmm_app_dev_assign.elf
    DEPENDS rmm-app-dev-assign-elf dev_assign_app_output_dir)

# Create the dump file using whatever tool comes with the toolchain.
if(CMAKE_OBJDUMP)
    add_custom_command(
        COMMAND "${CMAKE_OBJDUMP}" -dxS "${CMAKE_CURRENT_BINARY_DIR}/rmm_app_dev_assign.elf" > "${CMAKE_CURRENT_BINARY_DIR}/rmm_app_dev_assign.dump"
        OUTPUT rmm_app_dev_assign.dump
        DEPENDS rmm_app_dev_assign.elf)
endif()

target_sources(rmm-app-dev-assign-elf
    PRIVATE
        "src/dev_assign_el0_app.c"
        "src/dev_assign_cmds.c"
        "src/dev_assign_helper.c"
        "src/dev_tdisp_cmds.c")

if (RMM_ARCH STREQUAL fake_host)
    target_sources(rmm-app-dev-assign-elf
        PRIVATE "src/fake_host/dev_assign_app_host.c")
endif()

target_link_options(rmm-app-dev-assign-elf
    PRIVATE "-Wl,-Map=$<TARGET_FILE:rmm-app-dev-assign-elf>.map")

# pass the heap size to the app
target_compile_definitions(rmm-app-dev-assign-elf
    PRIVATE "HEAP_PAGE_COUNT=U(${DEV_ASSIGN_APP_HEAP_SIZE})")

if(NOT RMM_ARCH STREQUAL fake_host)
    set(COMMON_APP_LINKER_SCRIPT "${CMAKE_CURRENT_SOURCE_DIR}/../../common/el0_app/linker.lds")

    arm_target_linker_script(rmm-app-dev-assign-elf "${COMMON_APP_LINKER_SCRIPT}")

    set_property(TARGET rmm-app-dev-assign-elf-lds APPEND
        PROPERTY COMPILE_DEFINITIONS "__LINKER__")

    set_property(TARGET rmm-app-dev-assign-elf-lds APPEND
        PROPERTY COMPILE_DEFINITIONS "GRANULE_SHIFT=U(${GRANULE_SHIFT})")

    # Get the name of the bin file that will contain the app data
    get_filename_component(RAW_DATA_OUTPUT_FILE ${CMAKE_BINARY_DIR}/$<CONFIG>/rmm_app_dev_assign.bin ABSOLUTE)

    list(APPEND EL0_APP_BIN_LIST "${RAW_DATA_OUTPUT_FILE}")
    set(EL0_APP_BIN_LIST ${EL0_APP_BIN_LIST} PARENT_SCOPE)

    # Add a command that will run the bin file generation. Make it depend on the app elf file
    add_custom_command(
    OUTPUT ${RAW_DATA_OUTPUT_FILE}
    COMMAND ${GEN_APP_BIN}
        --elf-file $<TARGET_FILE:rmm-app-dev-assign-elf>
        --app-name "device_assignment_app"
        --app-id ${RMM_DEV_ASSIGN_APP_ID}
        --stack-page-count ${DEV_ASSIGN_APP_STACK_SIZE}
        --heap-page-count ${DEV_ASSIGN_APP_HEAP_SIZE}
        --out-bin ${RAW_DATA_OUTPUT_FILE}
    DEPENDS rmm-app-dev-assign-elf rmm-app-dev-assign-elf-lds
    )

    # Add a custom target that depends on the bin file. This is necessary so that
    # the bundled image can depend on it.
    add_custom_target(rmm-dev-assign-app DEPENDS ${RAW_DATA_OUTPUT_FILE} rmm_app_dev_assign.dump)
else()
    add_custom_target(rmm-dev-assign-app DEPENDS rmm_app_dev_assign.dump)
endif()
