#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

# The dev_assign app is not included in the CBMC analysis
if(RMM_CBMC_STATIC_ANALYSIS)
    return()
endif()

add_subdirectory("mbedtls_da")
add_subdirectory("spdm_requester")
add_subdirectory("spdm_emu")

include("${CMAKE_CURRENT_SOURCE_DIR}/../../common/el0_app/CommonApp.cmake")

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

add_el0_app(
    APP_NAME dev_assign
    APP_ID ${RMM_DEV_ASSIGN_APP_ID}
    APP_DISPLAY_NAME "device_assignment_app"
    STACK_SIZE_VAR DEV_ASSIGN_APP_STACK_SIZE
    HEAP_SIZE_VAR DEV_ASSIGN_APP_HEAP_SIZE
    SOURCES
        "src/dev_assign_cmds.c"
        "src/dev_assign_el0_app.c"
        "src/dev_assign_helper.c"
        "src/dev_assign_ide_cmds.c"
        "src/dev_tdisp_cmds.c"
        "src/rme_dvsec.c"
    LINK_LIBRARIES
        rmm-app-da-mbedtls
        rmm-lib-common
        rmm-lib-debug
        rmm-lib-smc
        rmm-lib-xlat
        rmm-pci-ide-km-requester-lib
        rmm-pci_tdisp_requester_lib
        rmm-spdm_requester
)

# Add device assignment-specific include directories
target_include_directories(rmm-app-dev-assign-elf
    PRIVATE
        "${RMM_SOURCE_DIR}/app/device_assignment/el0_app/spdm_requester"
        "${RMM_SOURCE_DIR}/app/device_assignment/el0_app/mbedtls_da"
)

# Add fake_host specific sources
if(RMM_ARCH STREQUAL fake_host)
    target_sources(rmm-app-dev-assign-elf
        PRIVATE "src/fake_host/dev_assign_app_host.c")
endif()

# Propagate EL0_APP_BIN_LIST to parent scope
set(EL0_APP_BIN_LIST ${EL0_APP_BIN_LIST} PARENT_SCOPE)
