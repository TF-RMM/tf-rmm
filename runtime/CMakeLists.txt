#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

include(ArmTargetLinkerScript)

add_executable(rmm-runtime)

target_link_options(rmm-runtime
    PRIVATE "-Wl,-Map=$<TARGET_FILE:rmm-runtime>.map")

arm_config_option(
    NAME RSI_LOG_LEVEL
    HELP "Log level to apply for RSI calls (0 - 50)"
    TYPE STRING
    DEFAULT 40)

target_compile_definitions(rmm-runtime
    PRIVATE "RSI_LOG_LEVEL=${RSI_LOG_LEVEL}")

target_link_libraries(rmm-runtime
    PRIVATE rmm-lib
            rmm-platform)

target_include_directories(rmm-runtime
    PRIVATE "include")

if(NOT RMM_ARCH STREQUAL fake_host)
    target_sources(rmm-runtime
        PRIVATE "core/aarch64/entry.S"
                "core/aarch64/head.S"
                "core/aarch64/helpers.S"
                "core/aarch64/ns_access.S"
                "core/aarch64/run-asm.S"
                "core/aarch64/vectors.S")
else()
    target_sources(rmm-runtime
        PRIVATE "core/fake_host/runtime_core_stub.c")
endif()

target_sources(rmm-runtime
    PRIVATE "core/exit.c"
            "core/handler.c"
            "core/init.c"
            "core/inject_exp.c"
            "core/run.c"
            "core/sysregs.c"
            "core/vmid.c")

target_sources(rmm-runtime
    PRIVATE "rmi/feature.c"
            "rmi/granule.c"
            "rmi/realm.c"
            "rmi/rec.c"
            "rmi/rtt.c"
            "rmi/run.c"
            "rmi/system.c")

target_sources(rmm-runtime
    PRIVATE "rsi/config.c"
            "rsi/feature.c"
            "rsi/host_call.c"
            "rsi/logger.c"
            "rsi/memory.c"
            "rsi/psci.c"
            "rsi/realm_ipa_helper.c"
            "rsi/realm_attest.c"
            "rsi/system.c")

arm_config_option(
    NAME RMM_MAX_SIZE
    HELP "Maximum size for RMM image"
    TYPE STRING
    DEFAULT 0x0
    ADVANCED)

if(RMM_MAX_SIZE EQUAL 0x0)
    message(FATAL_ERROR "RMM_MAX_SIZE is not initialized")
endif()

if(NOT RMM_ARCH STREQUAL fake_host)
    arm_target_linker_script(rmm-runtime "linker.lds")

    set_target_properties(rmm-runtime-lds
        PROPERTIES COMPILE_DEFINITIONS "__LINKER__")

    set_property(TARGET rmm-runtime-lds APPEND
        PROPERTY COMPILE_DEFINITIONS "GRANULE_SHIFT=U(${GRANULE_SHIFT})")

    set_property(TARGET rmm-runtime-lds APPEND
        PROPERTY COMPILE_DEFINITIONS "MAX_CPUS=UL(${MAX_CPUS})")

    set_property(TARGET rmm-runtime-lds APPEND
        PROPERTY COMPILE_DEFINITIONS "RMM_MAX_SIZE=UL(${RMM_MAX_SIZE})")

    set_property(TARGET rmm-runtime-lds APPEND
        PROPERTY COMPILE_DEFINITIONS "RMM_NUM_PAGES_PER_STACK=UL(${RMM_NUM_PAGES_PER_STACK})")
endif()

include (tests/CMakeLists.txt)
