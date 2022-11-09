#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

#[=======================================================================[.rst:
ArmConfigOption
---------------

.. default-domain:: cmake

.. command:: arm_config_option

Create a configuration option with more flexibility than offered by
:module:`cmake_dependent_option() <module:CMakeDependentOption>`.

.. code:: cmake

    arm_config_option(NAME <name> HELP <help> [TYPE <type>] [DEFAULT <default>]
                      [[STRINGS <strings>...] [FREEFORM]] [ADVANCED]
                      [[DEPENDS <depends>] [ELSE <else>]] [FORCE <force>])

This helper function is intended to simplify some of the complex mechanics
involved in creating a robust, scalable configuration system for medium to
large projects. It incorporates basic dependency resolution, overridable default
values, and stronger typing in order to provide a smoother experience for both
build system developers and users.

Basics
^^^^^^

Every configuration option has one of the following types:

- ``BOOL`` for booleans (shows as a toggle option)
- ``STRING`` for strings (shows as a text box)
- ``PATH`` for directory paths (shows as a directory chooser)
- ``FILEPATH`` for file paths (shows as a file chooser)

These are the types supported by the :prop_cache:`TYPE <prop_cache:TYPE>` cache
entry property. It's important to choose the right type for the option in order
to provide a consistent user experience.

By default, any configuration option that does not specify a type (by providing
a value to the ``TYPE`` argument) is ``BOOL``, unless the ``STRINGS`` argument
has been provided. For example:

.. code:: cmake

    arm_config_option(NAME XYZ ... TYPE BOOL) # BOOL
    arm_config_option(NAME XYZ ... TYPE STRING) # STRING
    arm_config_option(NAME XYZ ... TYPE PATH) # PATH
    arm_config_option(NAME XYZ ... TYPE FILEPATH) # FILEPATH

    arm_config_option(NAME XYZ ...) # BOOL
    arm_config_option(NAME XYZ ... STRINGS ...) # STRING

Likewise, every configuration option has a (default) default value, dependent on
its type:

.. code:: cmake

    arm_config_option(NAME XYZ ... TYPE BOOL) # FALSE
    arm_config_option(NAME XYZ ... TYPE STRING) # ""
    arm_config_option(NAME XYZ ... TYPE PATH) # ""
    arm_config_option(NAME XYZ ... TYPE FILEPATH) # ""

    arm_config_option(NAME XYZ ...) # FALSE
    arm_config_option(NAME XYZ ... STRINGS X Y Z) # "X"

Note that the default value of configuration options with a ``STRINGS`` list
will use the first element of the list as the default.

The default value can be overridden by providing a value to the ``DEFAULT``
argument:

.. code:: cmake

    arm_config_option(NAME XYZ ... TYPE BOOL DEFAULT TRUE) # TRUE
    arm_config_option(NAME XYZ ... TYPE STRING DEFAULT "x") # "x"
    arm_config_option(NAME XYZ ... TYPE PATH DEFAULT "./x") # "./x"
    arm_config_option(NAME XYZ ... TYPE FILEPATH DEFAULT "./x.txt") # "./x.txt"

For options with a ``STRINGS`` list, the value provided to the ``DEFAULT``
argument must exist within the list unless the ``FREEFORM`` argument has been
provided. Freeform string list options permit values outside of the list:

.. code:: cmake

    arm_config_option(NAME XYZ ... STRINGS X Y Z) # "X"
    arm_config_option(NAME XYZ ... STRINGS X Y Z DEFAULT Z) # "Z"
    arm_config_option(NAME XYZ ... STRINGS X Y Z DEFAULT A FREEFORM) # "A"
    arm_config_option(NAME XYZ ... STRINGS X Y Z DEFAULT A) # ERROR

Configuration options can be marked as "advanced" by using the ``ADVANCED``
flag. In CMake's user interfaces, this hides the configuration option behind the
"advanced" toggle:

    arm_config_option(NAME XYZ ...) # Always visible
    arm_config_option(NAME XYZ ... ADVANCED) # Visible only when requested

Some basic usage examples follow:

.. code:: cmake

    arm_config_option(
        NAME MYPROJECT_ENABLE_FOO
        HELP "Enable the foo feature.")

    arm_config_option(
        NAME MYPROJECT_ENABLE_BAR
        HELP "Enable the bar feature."
        ADVANCED)

    arm_config_option(
        NAME MYPROJECT_BAZ_NAME
        HELP "Name of the baz."
        TYPE STRING
        DEFAULT "Baz")

    arm_config_option(
        NAME MYPROJECT_BAZ_TYPE
        HELP "Type of the baz."
        STRINGS "Surly" "Bewildered" "Aloof")

    if(MYPROJECT_ENABLE_FOO)
        message(STATUS "The foo feature is enabled!")
    endif()

    if(MYPROJECT_ENABLE_BAR)
        message(STATUS "The bar feature is enabled!")
    endif()

    message(STATUS "The name of the baz is: ${MYPROJECT_BAZ_NAME}!")
    message(STATUS "The type of the baz is: ${MYPROJECT_BAZ_TYPE}!")

Dependencies
^^^^^^^^^^^^

Dependencies between options can be modelled using the ``DEPENDS`` argument.
This argument takes an expression in :ref:`Condition Syntax`, which determines
whether the option will be shown.

For example, if you have a feature flag ``foo``, and you have a feature flag
``bar`` that only makes sense if ``foo`` is enabled, you might use:

.. code:: cmake

    arm_config_option(
        NAME MYPROJECT_ENABLE_FOO
        HELP "Enable the foo feature.")

    arm_config_option(
        NAME MYPROJECT_ENABLE_BAR
        HELP "Enable the bar feature."
        DEPENDS MYPROJECT_ENABLE_FOO)

Configuration options whose dependencies have not been met are hidden from the
GUI (that is, the cache variable is given the ``INTERNAL`` type), and the
default value is restored.

If you need a value *other* than the default to be set if the dependency is not
met, then use the ``ELSE`` argument:

.. code:: cmake

    arm_config_option(
        NAME STACK_SIZE
        HELP "Stack size (in bytes)."
        TYPE STRING
        DEFAULT 512)

    arm_config_option(
        NAME HEAP_SIZE
        HELP "Heap size (in bytes)."
        DEFAULT 65536)

    arm_config_option(
      NAME STACKHEAP_SIZE
      HELP "Stackheap size."
      DEFAULT 65536
      DEPENDS ((STACK_SIZE EQUAL 0) AND (HEAP_SIZE EQUAL 0))
      ELSE 0)

In some cases you may need to forcibly overwrite the value of a configuration
option under certain conditions. You can do this using the ``FORCE`` argument
which, like ``DEPENDS``, accepts :ref:`Condition Syntax`. This is typically only
useful for augmenting existing cache variables.

In the following example, ``FORCE`` is used to forcibly override the default
value of :variable:`CMAKE_BUILD_TYPE <variable:CMAKE_BUILD_TYPE>` (``""``) with
a new default defined by the build system configuration:

.. code:: cmake

    arm_config_option(
        NAME CMAKE_BUILD_TYPE
        HELP "Build type."
        STRINGS "Debug" "RelWithDebInfo" "MinSizeRel" "Release"
        DEFAULT "MinSizeRel"
        FORCE NOT CMAKE_BUILD_TYPE)

Detecting Changes
^^^^^^^^^^^^^^^^^

In some cases it's useful to know whether a configuration option has been
modified. Any configuration option created with this function has an associated
``${NAME}_CHANGED`` cache variable, which can be used to detect whether the
value of ``${NAME}`` has changed between the last configuration run and the
current one.

For example:

.. code:: cmake

    arm_config_option(
        NAME ENABLE_FEATURE
        HELP "Enable the feature.")

    if(ENABLE_FEATURE_CHANGED)
        message(STATUS "The feature's been toggled!")
    endif()

Fine-Grained Control
^^^^^^^^^^^^^^^^^^^^

Additional facilities for fine-grained control over defaults and forced values
are provided by the :command:`arm_config_option_override`.
#]=======================================================================]

include_guard()

function(arm_config_option)
    set(_options "FREEFORM;ADVANCED")
    set(_single_args "NAME;HELP;TYPE")
    set(_multi_args "DEFAULT;STRINGS;DEPENDS;ELSE;FORCE")

    cmake_parse_arguments(
        arg "${_options}" "${_single_args}" "${_multi_args}" ${ARGN})

    if("DEFAULT" IN_LIST arg_KEYWORDS_MISSING_VALUES)
        set(arg_DEFAULT "")
    endif()

    #
    # Attempt to derive the type from the other arguments given. Passing STRINGS
    # implies a type of STRING, otherwise the type is BOOL.
    #

    if(NOT DEFINED arg_TYPE)
        if(DEFINED arg_STRINGS)
            set(arg_TYPE "STRING")
        else()
            set(arg_TYPE "BOOL")
        endif()
    endif()

    #
    # Identify a reasonable default if one has not been provided. For BOOL this
    # is FALSE. If STRINGS has been provided then we take the first entry in the
    # list. For any other type we use an empty string.
    #

    if(NOT DEFINED arg_DEFAULT)
        if(arg_TYPE MATCHES "BOOL")
            set(arg_DEFAULT "FALSE")
        elseif(DEFINED arg_STRINGS)
            list(GET arg_STRINGS 0 arg_DEFAULT)
        else()
            set(arg_DEFAULT "")
        endif()
    endif()

    #
    # If no dependency condition is provided, it is implicitly TRUE.
    #

    if(NOT DEFINED arg_DEPENDS)
        set(arg_DEPENDS "TRUE")
    endif()

    if(${arg_DEPENDS})
        #
        # If an internal cache variable exists by this name but the dependency
        # condition holds, it's because it previously didn't. We need to
        # forcibly update the variable to make it visible again.
        #

        if(DEFINED "${arg_NAME}")
            get_property(type CACHE "${arg_NAME}" PROPERTY TYPE)

            if(type STREQUAL "INTERNAL")
                set(arg_FORCE TRUE)
            endif()
        endif()

        #
        # If a force variable exists, take on its value and hide the cache
        # variable. Otherwise, if a default variable exists, just take on its
        # value.
        #

        if(DEFINED "${arg_NAME}_FORCE")
            set(arg_TYPE "INTERNAL")
            set(arg_DEFAULT "${${arg_NAME}_FORCE}")
        elseif(DEFINED "${arg_NAME}_INIT")
            set(arg_DEFAULT "${${arg_NAME}_INIT}")
        endif()
    else()
        #
        # If the dependency condition doesn't hold, hide the cache variable from
        # the user.
        #

        set(arg_TYPE "INTERNAL")

        #
        # If an else value has been given, now is the time to adopt it.
        #

        if(DEFINED arg_ELSE)
            set(arg_DEFAULT "${arg_ELSE}")
        endif()
    endif()

    #
    # Try to detect whether the user has overridden an already
    # forcibly-overriden variable. We throw an error in this situation to avoid
    # a split-brain configuration, where the variable expands to two values
    # depending on which side of this function call you are on.
    #
    # This usually happens if the user has defined the value on the command
    # line, as these options are replaced every time reconfiguration
    # happens.
    #

    if((DEFINED "${arg_NAME}") AND
        (DEFINED "${arg_NAME}_FORCE") AND
        (NOT "${${arg_NAME}_FORCE}" STREQUAL "${${arg_NAME}}"))
        set(value "${${arg_NAME}}")
        unset("${arg_NAME}" CACHE)

        if(${arg_DEPENDS})
            message(FATAL_ERROR
                "Overridden configuration option detected!\n"

                "The configuration option `${arg_NAME}` cannot be given "
                "the value `${value}` because it has been forcibly set to "
                "`${arg_DEFAULT}`.")
        else()
            string(REPLACE ";" " " dependency "${arg_DEPENDS}")

            message(FATAL_ERROR
                "Impossible configuration detected!\n"

                "The configuration option `${arg_NAME}` cannot be given "
                "the value `${value}` because it has been forcibly set to "
                "`${arg_DEFAULT}` due to an unmet dependency:\n"

                "${dependency}")
        endif()
    endif()

    #
    # The official documentation says that `INTERNAL` implies `FORCE`, but this
    # does not seem to be the case in some situations, so let's be safe.
    #

    if(arg_TYPE STREQUAL "INTERNAL")
        set(arg_FORCE TRUE)
    endif()

    #
    # If we're being asked to forcibly update the cache variable, append FORCE
    # to the set() call.
    #

    if((DEFINED arg_FORCE) AND (${arg_FORCE}))
        set(force "FORCE")
    else()
        unset(force)

        #
        # Clear the forced-value variable so that we don't accidentally flag
        # this
        #

        unset("${arg_NAME}_FORCE" CACHE)
    endif()

    #
    # Update the change-tracking variable.
    #

    set(old "${${arg_NAME}_NEW}")
    set(new "${${arg_NAME}}")

    if(NOT old STREQUAL new)
        set(changed TRUE)
    else()
        set(changed FALSE)
    endif()

    set("${arg_NAME}_OLD" "${old}"
        CACHE INTERNAL "Previous value of ${arg_NAME}." FORCE)

    set("${arg_NAME}_NEW" "${new}"
        CACHE INTERNAL "Latest value of ${arg_NAME}." FORCE)

    set("${arg_NAME}_CHANGED" ${changed}
        CACHE INTERNAL "Has ${arg_NAME} just changed?" FORCE)

    #
    # Create the cache variable.
    #

    set("${arg_NAME}" "${arg_DEFAULT}"
        CACHE "${arg_TYPE}" "${arg_HELP}" ${force})

    if(arg_ADVANCED)
        mark_as_advanced("${arg_NAME}")
    endif()

    #
    # If we've been given a list of valid values, update the STRINGS property of
    # the cache variable with that list.
    #

    if(DEFINED arg_STRINGS)
        set_property(CACHE "${arg_NAME}" PROPERTY STRINGS ${arg_STRINGS})

        #
        # If we haven't been asked to offer a freeform text box, let the user
        # know if they've provided something out of bounds.
        #

        if((NOT arg_FREEFORM) AND (NOT "${${arg_NAME}}" IN_LIST arg_STRINGS))
            set(strings "")

            foreach(string IN LISTS arg_STRINGS)
                string(APPEND strings "\"${string}\" ")
            endforeach()

            message(FATAL_ERROR
                "Invalid value for `${arg_NAME}`!\n"

                "This configuration supports the following values: ${strings}")
        endif()
    endif()
endfunction()
