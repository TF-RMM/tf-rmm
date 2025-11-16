#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

# The random app is not included in the CBMC analysis
if(RMM_CBMC_STATIC_ANALYSIS)
    add_library(rmm-app-random-elf INTERFACE)
    return()
endif()

add_subdirectory("mbedtls_random")

include("${CMAKE_CURRENT_SOURCE_DIR}/../../common/el0_app/CommonApp.cmake")

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

add_el0_app(
    APP_NAME random
    APP_ID ${RMM_RANDOM_APP_ID}
    APP_DISPLAY_NAME "random_app"
    STACK_SIZE_VAR RMM_NUM_PAGES_PER_RANDOM_APP_STACK
    HEAP_SIZE_VAR RMM_NUM_PAGES_PER_RANDOM_APP_HEAP
    SOURCES "src/random_app.c"
    LINK_LIBRARIES
        rmm-app-random-mbedtls
        rmm-lib-common
        rmm-lib-debug
        rmm-lib-xlat
)

# Add fake_host specific sources
if(RMM_ARCH STREQUAL fake_host)
    target_sources(rmm-app-random-elf
        PRIVATE "src/fake_host/random_app_host.c")
endif()

# Propagate EL0_APP_BIN_LIST to parent scope
set(EL0_APP_BIN_LIST ${EL0_APP_BIN_LIST} PARENT_SCOPE)
