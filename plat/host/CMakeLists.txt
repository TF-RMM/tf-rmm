#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

arm_config_option(
    NAME HOST_VARIANT
    HELP "Select the variant to use for the host platform"
    TYPE STRING
    STRINGS "host_build" "host_test" "host_cbmc"
    DEFAULT "host_build")

if(HOST_VARIANT STREQUAL host_test)
    # Disable CppUtest self tests
    set(TESTS "OFF" CACHE STRING "Compile and run CppUTest tests")

    # Disable CppUtest Extension Library
    set(EXTENSIONS "OFF" CACHE STRING "Use the CppUTest extension library")
endif()

add_subdirectory("../common" ${RMM_BINARY_DIR}/plat/common)

# Add the HOST_VARIANT directory before common, so that it has the option
# to override HOST_MEM_SIZE
add_subdirectory("${HOST_VARIANT}")
add_subdirectory("common")
