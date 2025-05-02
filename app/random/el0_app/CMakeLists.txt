#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

# TODO: The C file generating logic is general for all the apps.
# need to move it to a common location somehow.

# The random app is not included in the CBMC analysis
if(RMM_CBMC_STATIC_ANALYSIS)
    add_library(rmm-app-random-elf INTERFACE)
    return()
endif()

add_subdirectory("mbedtls_random")

include(ArmTargetLinkerScript)

find_package(Python3 REQUIRED)
find_program(GEN_APP_BIN "gen_app_bin.py"
    PATHS ${CMAKE_SOURCE_DIR}
    PATH_SUFFIXES app
    DOC "gen_app_bin.py"
    )

# Compile the app as a separate executable (add_library would skip the linking step)
add_executable(rmm-app-random-elf)

set(RMM_RANDOM_APP_ID 103)

arm_config_option(
    NAME RMM_NUM_PAGES_PER_RANDOM_APP_STACK
    HELP "Number of pages to use for the Random app stack"
    TYPE STRING
    DEFAULT 1
    ADVANCED)

arm_config_option(
    NAME RMM_NUM_PAGES_PER_RANDOM_APP_HEAP
    HELP "Number of pages to use for the Random app heap"
    TYPE STRING
    DEFAULT 1
    ADVANCED)

target_include_directories(rmm-app-random-elf
    PRIVATE
        "src"
        "${CMAKE_CURRENT_SOURCE_DIR}/../rmm_stub/include"
        "${CMAKE_CURRENT_SOURCE_DIR}/../../common/include")

target_link_libraries(rmm-app-random-elf
    PRIVATE
        rmm-app-common-el0_app
        rmm-app-random-mbedtls
        rmm-lib-common
        rmm-lib-debug
        rmm-lib-xlat)

add_custom_command(
    COMMAND "${CMAKE_COMMAND}" -E copy_if_different "$<TARGET_FILE:rmm-app-random-elf>" "${CMAKE_CURRENT_BINARY_DIR}/rmm_app_random.elf"
    OUTPUT rmm_app_random.elf
    DEPENDS rmm-app-random-elf)

# Create the dump file using whatever tool comes with the toolchain.
if(CMAKE_OBJDUMP)
    add_custom_command(
        COMMAND "${CMAKE_OBJDUMP}" -dxS "${CMAKE_CURRENT_BINARY_DIR}/rmm_app_random.elf" > "${CMAKE_CURRENT_BINARY_DIR}/rmm_app_random.dump"
        OUTPUT rmm_app_random.dump
        DEPENDS rmm_app_random.elf)
endif()

target_sources(rmm-app-random-elf
    PRIVATE
        "src/random_app.c")

if (RMM_ARCH STREQUAL fake_host)
    target_sources(rmm-app-random-elf
        PRIVATE "src/fake_host/random_app_host.c")
endif()

target_link_options(rmm-app-random-elf
    PRIVATE "-Wl,-Map=$<TARGET_FILE:rmm-app-random-elf>.map")

# pass the heap size to the app
target_compile_definitions(rmm-app-random-elf
    PRIVATE "HEAP_PAGE_COUNT=U(${RMM_NUM_PAGES_PER_RANDOM_APP_HEAP})")

if(NOT RMM_ARCH STREQUAL fake_host)
    set(COMMON_APP_LINKER_SCRIPT "${CMAKE_CURRENT_SOURCE_DIR}/../../common/el0_app/linker.lds")

    arm_target_linker_script(rmm-app-random-elf "${COMMON_APP_LINKER_SCRIPT}")

    set_property(TARGET rmm-app-random-elf-lds APPEND
        PROPERTY COMPILE_DEFINITIONS "__LINKER__")

    set_property(TARGET rmm-app-random-elf-lds APPEND
        PROPERTY COMPILE_DEFINITIONS "GRANULE_SHIFT=U(${GRANULE_SHIFT})")

    # Get the name of the bin file that will contain the app data
    get_filename_component(RAW_DATA_OUTPUT_FILE ${CMAKE_CURRENT_BINARY_DIR}/random_app_data.bin ABSOLUTE)

    list(APPEND EL0_APP_BIN_LIST "${RAW_DATA_OUTPUT_FILE}")
    set(EL0_APP_BIN_LIST ${EL0_APP_BIN_LIST} PARENT_SCOPE)

    # Add a command that will run the bin file generation. Make it depend on the app elf file
    add_custom_command(
    OUTPUT ${RAW_DATA_OUTPUT_FILE}
    COMMAND ${GEN_APP_BIN}
        --elf-file $<TARGET_FILE:rmm-app-random-elf>
        --app-name "random_app"
        --app-id ${RMM_RANDOM_APP_ID}
        --stack-page-count ${RMM_NUM_PAGES_PER_RANDOM_APP_STACK}
        --heap-page-count ${RMM_NUM_PAGES_PER_RANDOM_APP_HEAP}
        --out-bin ${RAW_DATA_OUTPUT_FILE}
    DEPENDS rmm-app-random-elf rmm-app-random-elf-lds
    )

    # Add a custom target that depends on the bin file. This is necessary so that
    # the bundled image can depend on it.
    add_custom_target(rmm-random-app-bin DEPENDS ${RAW_DATA_OUTPUT_FILE} rmm_app_random.dump)
endif()
