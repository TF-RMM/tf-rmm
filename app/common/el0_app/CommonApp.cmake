#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

#
# Common CMake configuration for EL0 applications
# This function sets up the build for an EL0 app with common patterns.
#
# Parameters:
#   APP_NAME        - Name of the app (e.g., "random", "attestation",
#                     "dev_assign")
#   APP_ID          - Numeric app ID
#   APP_DISPLAY_NAME - Display name for the app (e.g., "random_app",
#                      "attestation_app")
#   STACK_SIZE_VAR  - Name of the CMake variable for stack size
#   HEAP_SIZE_VAR   - Name of the CMake variable for heap size
#   SOURCES         - List of source files for the app
#   LINK_LIBRARIES  - List of libraries to link against
#

function(add_el0_app)
    set(options "")
    set(oneValueArgs
        APP_NAME
        APP_ID
        APP_DISPLAY_NAME
        STACK_SIZE_VAR
        HEAP_SIZE_VAR)
    set(multiValueArgs SOURCES LINK_LIBRARIES)
    cmake_parse_arguments(APP
        "${options}"
        "${oneValueArgs}"
        "${multiValueArgs}"
        ${ARGN})

    # Replace underscores with dashes for target names
    string(REPLACE "_" "-" APP_TARGET_NAME "${APP_APP_NAME}")

    # Compile the app as a separate executable
    add_executable(rmm-app-${APP_TARGET_NAME}-elf)

    # Common include directories
    target_include_directories(rmm-app-${APP_TARGET_NAME}-elf
        PRIVATE
            "src"
            "${CMAKE_CURRENT_SOURCE_DIR}/../rmm_stub/include"
            "${CMAKE_CURRENT_SOURCE_DIR}/../../common/include")

    # Link libraries
    target_link_libraries(rmm-app-${APP_TARGET_NAME}-elf
        PRIVATE
            rmm-app-common-el0_app
            ${APP_LINK_LIBRARIES})

    if(RMM_ARCH STREQUAL fake_host)
        target_link_libraries(rmm-app-${APP_TARGET_NAME}-elf
            PRIVATE
                rmm-host-el2-el0-cmn)
    endif()

    # Target for output directory
    add_custom_target(${APP_TARGET_NAME}_app_output_dir
        COMMAND "${CMAKE_COMMAND}" -E make_directory
            "${CMAKE_BINARY_DIR}/$<CONFIG>"
        COMMENT "Creating output directory"
    )

    # Copy ELF and map files to output directory
    add_custom_command(
        COMMAND "${CMAKE_COMMAND}" -E copy_if_different
            "$<TARGET_FILE:rmm-app-${APP_TARGET_NAME}-elf>"
            "${CMAKE_BINARY_DIR}/$<CONFIG>/rmm_app_${APP_APP_NAME}.elf"
        COMMAND "${CMAKE_COMMAND}" -E copy_if_different
            "$<TARGET_FILE:rmm-app-${APP_TARGET_NAME}-elf>.map"
            "${CMAKE_BINARY_DIR}/$<CONFIG>/rmm_app_${APP_APP_NAME}.map"
        OUTPUT rmm_app_${APP_APP_NAME}.elf
        DEPENDS rmm-app-${APP_TARGET_NAME}-elf
            ${APP_TARGET_NAME}_app_output_dir)

    # Create the dump file using whatever tool comes with the toolchain
    if(CMAKE_OBJDUMP)
        add_custom_command(
            COMMAND "${CMAKE_OBJDUMP}" -dxS
                "${CMAKE_BINARY_DIR}/$<CONFIG>/rmm_app_${APP_APP_NAME}.elf"
                > "${CMAKE_BINARY_DIR}/$<CONFIG>/rmm_app_${APP_APP_NAME}.dump"
            OUTPUT rmm_app_${APP_APP_NAME}.dump
            DEPENDS rmm_app_${APP_APP_NAME}.elf)
    endif()

    # Add source files
    target_sources(rmm-app-${APP_TARGET_NAME}-elf
        PRIVATE
            ${APP_SOURCES})

    # Link options for map file
    target_link_options(rmm-app-${APP_TARGET_NAME}-elf
        PRIVATE
            "-Wl,-Map=$<TARGET_FILE:rmm-app-${APP_TARGET_NAME}-elf>.map")

    # Pass the heap size to the app
    target_compile_definitions(rmm-app-${APP_TARGET_NAME}-elf
        PRIVATE
            "HEAP_PAGE_COUNT=U(${${APP_HEAP_SIZE_VAR}})")

    if(NOT RMM_ARCH STREQUAL fake_host)
        set(COMMON_APP_LINKER_SCRIPT
            "${CMAKE_CURRENT_SOURCE_DIR}/../../common/el0_app/linker.lds")

        include(ArmTargetLinkerScript)
        arm_target_linker_script(rmm-app-${APP_TARGET_NAME}-elf
            "${COMMON_APP_LINKER_SCRIPT}")

        set_property(TARGET rmm-app-${APP_TARGET_NAME}-elf-lds APPEND
            PROPERTY COMPILE_DEFINITIONS "__LINKER__")

        set_property(TARGET rmm-app-${APP_TARGET_NAME}-elf-lds APPEND
            PROPERTY COMPILE_DEFINITIONS
                "GRANULE_SHIFT=U(${GRANULE_SHIFT})")

        # Get the name of the bin file that will contain the app data
        get_filename_component(RAW_DATA_OUTPUT_FILE
            ${CMAKE_BINARY_DIR}/$<CONFIG>/rmm_app_${APP_APP_NAME}.bin
            ABSOLUTE)

        # Append to the parent scope's EL0_APP_BIN_LIST
        set(EL0_APP_BIN_LIST ${EL0_APP_BIN_LIST}
            "${RAW_DATA_OUTPUT_FILE}"
            PARENT_SCOPE)

        # Add a command that will run the bin file generation.
        # Make it depend on the app elf file
        find_package(Python3 REQUIRED)
        find_program(GEN_APP_BIN "gen_app_bin.py"
            PATHS ${CMAKE_SOURCE_DIR}
            PATH_SUFFIXES app
            DOC "gen_app_bin.py"
        )

        add_custom_command(
            OUTPUT ${RAW_DATA_OUTPUT_FILE}
            COMMAND ${GEN_APP_BIN}
                --elf-file
                    $<TARGET_FILE:rmm-app-${APP_TARGET_NAME}-elf>
                --app-name "${APP_APP_DISPLAY_NAME}"
                --app-id ${APP_APP_ID}
                --stack-page-count ${${APP_STACK_SIZE_VAR}}
                --heap-page-count ${${APP_HEAP_SIZE_VAR}}
                --out-bin ${RAW_DATA_OUTPUT_FILE}
            DEPENDS rmm-app-${APP_TARGET_NAME}-elf
                rmm-app-${APP_TARGET_NAME}-elf-lds
        )

        # Add a custom target that depends on the bin file
        add_custom_target(rmm-${APP_TARGET_NAME}-app
            DEPENDS ${RAW_DATA_OUTPUT_FILE} rmm_app_${APP_APP_NAME}.dump)
    else()
        add_custom_target(rmm-${APP_TARGET_NAME}-app
            DEPENDS rmm_app_${APP_APP_NAME}.dump)
    endif()
endfunction()
