#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

#[=======================================================================[.rst:
ArmTargetLinkerScript
---------------------

.. default-domain:: cmake

.. command:: arm_target_linker_script

Set the linker script for a target.

.. code:: cmake

    arm_target_linker_script(<target> <script>)

Sets the linker script of the target ``<target>`` to the script ``<script>``,
which is first preprocessed with the C preprocessor.

Properties for the linker script target may be set on `<target>-lds`.

Example usage:

.. code:: cmake

    add_executable(my-executable "main.c")

    arm_target_linker_script(my-executable "linker.lds")

    set_target_properties(my-executable-lds
        PROPERTIES COMPILE_DEFINITIONS "__LINKER__")

.. note::

    When preprocessing, the linker script given to this macro automatically
    inherits :variable:`CMAKE_C_FLAGS <variable:CMAKE_<LANG>_FLAGS>` and
    :variable:`CMAKE_C_FLAGS_<CONFIG> <variable:CMAKE_<LANG>_FLAGS_<CONFIG>>`.

    It also inherits the following properties from the target ``<target>``:

    - :prop_tgt:`COMPILE_OPTIONS <prop_tgt:COMPILE_OPTIONS>`
    - :prop_tgt:`COMPILE_DEFINITIONS <prop_tgt:COMPILE_DEFINITIONS>`
    - :prop_tgt:`INCLUDE_DIRECTORIES <prop_tgt:INCLUDE_DIRECTORIES>`
#]=======================================================================]

include_guard()

include(ArmPreprocessSource)

macro(arm_target_linker_script target script)
    set(subtarget "${target}-lds")

    #
    # Preprocess the linker script before doing anything else.
    #

    arm_preprocess_source(${subtarget} "${script}")

    set_target_properties(${subtarget}
        PROPERTIES
            COMPILE_OPTIONS
                "$<TARGET_PROPERTY:${target},COMPILE_OPTIONS>"
            COMPILE_DEFINITIONS
                "$<TARGET_PROPERTY:${target},COMPILE_DEFINITIONS>"
            INCLUDE_DIRECTORIES
                "$<TARGET_PROPERTY:${target},INCLUDE_DIRECTORIES>")

    #
    # Add the linker script to the dependencies of the target.
    #

    add_dependencies(${target} ${subtarget})

    set(location "$<TARGET_PROPERTY:${subtarget},LOCATION_$<CONFIG>>")

    set_target_properties(${target}
        PROPERTIES INTERFACE_LINK_DEPENDS "${location}")

    if(CMAKE_C_COMPILER_ID STREQUAL "ARMClang")
        target_link_options(${target}
            PUBLIC "LINKER:--scatter" "LINKER:${location}")
    else()
        target_link_options(${target}
            PUBLIC "LINKER:-T" "LINKER:${location}")
    endif()
endmacro()
