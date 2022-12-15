#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

if(RMM_STATIC_ANALYSIS)
    find_program(RMM_STATIC_ANALYSIS_CPPCHECK_PATH "cppcheck"
        DOC "Path to Cppcheck.")
endif()

if(EXISTS "${RMM_STATIC_ANALYSIS}")
    mark_as_advanced(FORCE RMM_STATIC_ANALYSIS_CPPCHECK_PATH)
else()
    mark_as_advanced(CLEAR RMM_STATIC_ANALYSIS_CPPCHECK_PATH)
endif()

arm_config_option(
    NAME RMM_STATIC_ANALYSIS_CPPCHECK
    HELP "Enable Cppcheck static analysis."
    DEFAULT TRUE
    DEPENDS (RMM_STATIC_ANALYSIS) AND
            (EXISTS "${RMM_STATIC_ANALYSIS_CPPCHECK_PATH}")
    ELSE FALSE)

arm_config_option(
    NAME RMM_STATIC_ANALYSIS_CPPCHECK_FLAGS
    HELP "Cppcheck command line options."
    TYPE STRING
    DEFAULT ""
    DEPENDS RMM_STATIC_ANALYSIS_CPPCHECK
    ADVANCED)

arm_config_option(
    NAME RMM_STATIC_ANALYSIS_CPPCHECK_CHECKER_CERT_C
    HELP "Enable Cppcheck's SEI CERT C checker."
    DEFAULT TRUE
    DEPENDS RMM_STATIC_ANALYSIS_CPPCHECK
    ELSE FALSE)

arm_config_option(
    NAME RMM_STATIC_ANALYSIS_CPPCHECK_CHECKER_MISRA
    HELP "Enable Cppcheck's MISRA C:2012 checker."
    DEFAULT TRUE
    DEPENDS RMM_STATIC_ANALYSIS_CPPCHECK
    ELSE FALSE)

arm_config_option(
    NAME RMM_STATIC_ANALYSIS_CPPCHECK_CHECKER_THREAD_SAFETY
    HELP "Enable Cppcheck's thread safety checker."
    DEFAULT TRUE
    DEPENDS RMM_STATIC_ANALYSIS_CPPCHECK
    ELSE FALSE)

if(RMM_STATIC_ANALYSIS_CPPCHECK)
    #
    # Set up checkers.
    #

    set(cppcheck-flags)

    list(APPEND cppcheck-flags "--enable=all")
    list(APPEND cppcheck-flags "--xml")
    list(APPEND cppcheck-flags "--xml-version=2")
    list(APPEND cppcheck-flags "--output-file=${CMAKE_CURRENT_BINARY_DIR}/cppcheck.xml")

    if(RMM_STATIC_ANALYSIS_CPPCHECK_CHECKER_CERT_C)
        list(APPEND cppcheck-flags "--addon=cert")
    endif()

    if(RMM_STATIC_ANALYSIS_CPPCHECK_CHECKER_MISRA)
	list(APPEND cppcheck-flags "--addon=${CMAKE_CURRENT_SOURCE_DIR}/misra.json")
    endif()

    if(RMM_STATIC_ANALYSIS_CPPCHECK_CHECKER_THREAD_SAFETY)
        list(APPEND cppcheck-flags "--addon=threadsafety")
    endif()

    #
    # Pass CHAR_BIT to Mbed TLS to supress error:
    # "mbed TLS requires a platform with 8-bit chars"
    #

    list(APPEND cppcheck-flags "-DCHAR_BIT=8")

    #
    # Exclude files or directories we don't want to receive warnings about.
    #

    list(APPEND cppcheck-flags "-i${CMAKE_SOURCE_DIR}/ext/")
    list(APPEND cppcheck-flags "-i${CMAKE_SOURCE_DIR}/lib/libc")

    #
    # If you want to suppress specific files without using an inline suppression,
    # do it in `suppressions.txt`.
    #

    list(APPEND cppcheck-flags
        "--inline-suppr" # Allow inline suppressions
        "--suppressions-list=${CMAKE_CURRENT_SOURCE_DIR}/suppressions.txt")

    #
    # Determine implicit C compiler definitions by pulling them from the
    # compiler and dumping them into a header file. This is for those situations
    # where we're relying on compiler implementation details, but Cppcheck
    # doesn't expose them.
    #

    file(TOUCH "${CMAKE_CURRENT_BINARY_DIR}/null.txt")

    separate_arguments(cflags NATIVE_COMMAND "${CMAKE_C_FLAGS}")

    execute_process(
        COMMAND ${CMAKE_C_COMPILER} ${cflags} -dM -E -
        INPUT_FILE "${CMAKE_CURRENT_BINARY_DIR}/null.txt"
        OUTPUT_FILE "${CMAKE_CURRENT_BINARY_DIR}/implicit-defines.h")

    list(APPEND cppcheck-flags
        "--include=${CMAKE_CURRENT_BINARY_DIR}/implicit-defines.h"
        "--suppress=*:${CMAKE_CURRENT_BINARY_DIR}/implicit-defines.h")

    #
    # Traditionally we would let Cppcheck use its own standard library headers,
    # but it appears to be lacking some critical symbols like `CHAR_BIT` from
    # `<limits.h>`. Luckily, CMake makes this relatively easy for us to do. We
    # don't analyze these headers, we just make them available for inclusion.
    #

    foreach(include IN LISTS CMAKE_C_IMPLICIT_INCLUDE_DIRECTORIES)
        list(APPEND cppcheck-flags "-I${include}")
        list(APPEND cppcheck-flags "--suppress=*:${include}/*")
    endforeach()

    #
    # Configure the platform file. This is done based on the current compiler,
    # if possible, so that we can communicate certain implementation details to
    # Cppcheck and avoid false positives.
    #

    set(platform-xml
        "${CMAKE_CURRENT_SOURCE_DIR}/compilers/${CMAKE_C_COMPILER_ID}.xml")

    if(EXISTS "${platform-xml}")
        list(APPEND cppcheck-flags "--platform=${platform-xml}")
    else()
        message(WARNING
            "No Cppcheck platform file is available for this compiler. Static "
            "analysis results may be inaccurate.")
    endif()

    separate_arguments(cppcheck-flags-user
        NATIVE_COMMAND "${RMM_STATIC_ANALYSIS_CPPCHECK_FLAGS}")


    set(COMPILE_COMMANDS_FILE "${CMAKE_BINARY_DIR}/compile_commands.json")

    add_custom_target(cppcheck
      COMMAND ${RMM_STATIC_ANALYSIS_CPPCHECK_PATH}
              --project=${COMPILE_COMMANDS_FILE} ${cppcheck-flags} ||
              (test ! -e ${COMPILE_COMMANDS_FILE} &&
              echo 'please generate with -DRMM_STATIC_ANALYSIS_CPPCHECK=ON')
    )
else()
    unset(CMAKE_C_CPPCHECK CACHE)
endif()
