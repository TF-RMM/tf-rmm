#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

#[=======================================================================[.rst:
ArmPreprocessSource
-------------------

.. default-domain:: cmake

.. command:: arm_preprocess_source

Preprocess a file with the C preprocessor.

.. code:: cmake

    arm_preprocess_source(<target> <source>)

Creates a target ``<target>`` which preprocesses an input file ``<source>``. The
target created by this macro can then be used as a dependency for a higher-level
target. The output file can be retrieved from the :prop_tgt:`LOCATION_<CONFIG>
<prop_tgt:LOCATION_<CONFIG>>` target property.

The following target properties are passed to the preprocessor:

- :prop_tgt:`COMPILE_OPTIONS <prop_tgt:COMPILE_OPTIONS>`
- :prop_tgt:`COMPILE_DEFINITIONS <prop_tgt:COMPILE_DEFINITIONS>`
- :prop_tgt:`INCLUDE_DIRECTORIES <prop_tgt:INCLUDE_DIRECTORIES>`

.. note::

    The created target automatically inherits :variable:`CMAKE_C_FLAGS
    <variable:CMAKE_<LANG>_FLAGS>` and :variable:`CMAKE_C_FLAGS_<CONFIG>
    <variable:CMAKE_<LANG>_FLAGS_<CONFIG>>`.

For example, if you wish to preprocess a file while providing the preprocessor
definition ``-DFOO=BAR``, you would use:

.. code:: cmake

    arm_preprocess_source(foo "bar.ld.S")

    set_target_properties(foo PROPERTIES
        COMPILE_DEFINITIONS "FOO=BAR")

    get_target_property(location foo LOCATION_${CMAKE_BUILD_TYPE})

    message(STATUS "My preprocessed file is here: ${location}")

For processing linker scripts specifically, see the
:command:`arm_target_linker_script` command instead.
#]=======================================================================]

include_guard()

macro(arm_preprocess_source target source)
    #
    # We start by trying to get the source file relative to the current source
    # directory, which means that we can mirror where it goes in the binary
    # directory. This just replicates what CMake does with source files it's
    # aware of.
    #

    get_filename_component(preprocessed_source "${source}.i" ABSOLUTE)
    file(RELATIVE_PATH preprocessed_source "${CMAKE_CURRENT_SOURCE_DIR}"
        "${preprocessed_source}")

    #
    # If we're using a multi-config generator, we need to place the output file
    # into the correct configuration directory.
    #

    get_property(multi_config GLOBAL
        PROPERTY "GENERATOR_IS_MULTI_CONFIG")

    if(multi_config)
        string(PREPEND preprocessed_source "$<CONFIG>/")
    endif()

    #
    # Make the source path absolute so that we don't need to care which
    # working directory the preprocessor uses.
    #

    string(PREPEND preprocessed_source "${CMAKE_CURRENT_BINARY_DIR}/")

    #
    # Create a single target for all configurations. It's differentiated based
    # on the generator expression in the dependency.
    #

    add_custom_target(${target}
        DEPENDS "${preprocessed_source}")

    #
    # Now that we've got that out of the way, we need to generate the
    # preprocessing command for each of the enabled configurations. Multi-config
    # generators will use `CMAKE_CONFIGURATION_TYPES`, whereas single-config
    # generators will use `CMAKE_BUILD_TYPE`. Only one is ever non-empty.
    #

    foreach(config IN LISTS CMAKE_CONFIGURATION_TYPES CMAKE_BUILD_TYPE)
        #
        # CMake provides the `CMAKE_C_CREATE_PREPROCESSED_SOURCE` variable,
        # which describes the command line required to preprocess a C source
        # file. This variable is in a format similar to this:
        #
        # <CMAKE_C_COMPILER> <DEFINES> <INCLUDES> <FLAGS> -E <SOURCE> >
        # <PREPROCESSED_SOURCE>
        #
        # We do some processing on this variable to convert these
        # bracket-surrounded names to variables we set. For example, `<DEFINES>`
        # is replaced with `${DEFINES}`. We then need to do some string
        # replacement magic to expand that string out to the value of the actual
        # variable.
        #
        # The values for some of these, namely include directories, definitions
        # and other compiler options, come from properties set on the target by
        # the caller. These are typically taken from the target that this
        # preprocessed source file belongs to.
        #

        set(command ${CMAKE_C_CREATE_PREPROCESSED_SOURCE})
        string(REPLACE " " ";" command ${command})

        get_filename_component(SOURCE "${source}" ABSOLUTE)
        string(REPLACE "$<CONFIG>" "${config}" PREPROCESSED_SOURCE
            "${preprocessed_source}")

        separate_arguments(FLAGS UNIX_COMMAND
            "${CMAKE_C_FLAGS} ${CMAKE_C_FLAGS_${config}} -P -x c")

        if(CMAKE_C_COMPILER_TARGET)
            if(CMAKE_C_COMPILER_ID MATCHES "Clang")
                list(APPEND FLAGS "-target" "${CMAKE_C_COMPILER_TARGET}")
            endif()
        endif()

        unset(DEFINES)
        unset(INCLUDES)

        list(APPEND FLAGS "$<TARGET_PROPERTY:${target},COMPILE_OPTIONS>")
        list(APPEND DEFINES "$<TARGET_PROPERTY:${target},COMPILE_DEFINITIONS>")
        list(APPEND INCLUDES "$<TARGET_PROPERTY:${target},INCLUDE_DIRECTORIES>")

        set(DEFINES "$<$<BOOL:${DEFINES}>:-D$<JOIN:${DEFINES},$<SEMICOLON>-D>>")
        set(INCLUDES "$<$<BOOL:${INCLUDES}>:-I$<JOIN:${INCLUDES},$<SEMICOLON>-I>>")

        string(REGEX REPLACE "<([[A-Z_]+)>" "\${\\1}" command "${command}")
        string(REGEX MATCH "\\\${[^}]*}" match "${command}")

        while(match)
            string(REGEX REPLACE "\\\${(.*)}" "\\1" variable "${match}")
            string(REPLACE "\${${variable}}" "${${variable}}" command "${command}")
            string(REGEX MATCH "\\\${[^}]*}" match "${command}")
        endwhile()

        add_custom_command(
            OUTPUT "${PREPROCESSED_SOURCE}"
            MAIN_DEPENDENCY ${source}
            COMMAND "${command}"
            VERBATIM COMMAND_EXPAND_LISTS)

        set_target_properties(${target} PROPERTIES
            LOCATION_${config} "${PREPROCESSED_SOURCE}")
    endforeach()
endmacro()
