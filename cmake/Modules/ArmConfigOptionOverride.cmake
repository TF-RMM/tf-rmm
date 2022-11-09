#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

#[=======================================================================[.rst:
ArmConfigOptionOverride
-----------------------

.. default-domain:: cmake

.. command:: arm_config_option_override

Override the default or final value of a configuration option defined by
:command:`arm_config_option`.

.. note::

    Configuration options can only be overridden if their dependencies are met.
    This ensures the configuration space is always in a valid state.

Override Default Value
^^^^^^^^^^^^^^^^^^^^^^

.. code:: cmake

    arm_config_option_override(NAME <name> DEFAULT <default>)

Overrides the default value of the configuration option ``<name>`` with the
value ``<default>``.

For example:

.. code:: cmake

    arm_config_option_override(
        NAME MYPROJECT_USE_FOO
        DEFAULT TRUE)

    arm_config_option(
        NAME MYPROJECT_USE_FOO
        HELP "Use foo.")

In this situation, the configuration option ``USE_FOO`` is created with a
default value of ``FALSE``, but will use the overridden default value of
``TRUE``. This is most often useful in larger projects where certain default
values make more sense under certain conditions.

Forcibly Override Value
=======================

.. code:: cmake

    arm_config_option_override(NAME <name> FORCE <force>)

Forcibly overrides the value of the configuration option ``<name>`` with
``<force>``.

For example:

.. code:: cmake

    arm_config_option_override(
        NAME MYPROJECT_USE_FOO
        FORCE TRUE)

    arm_config_option(
        NAME MYPROJECT_USE_FOO
        HELP "Use foo.")

In this situation, ``USE_FOO`` will be forcibly set to ``TRUE``, and it will be
hidden from the GUI. Users may also no longer configure this value themselves.
Attempting to change the value of the configuration option will cause a
configuration failure, and the previous value will be restored.
#]=======================================================================]

include_guard()

function(arm_config_option_override)
    set(_options "")
    set(_single_args "NAME;DEFAULT;FORCE")
    set(_multi_args "")

    cmake_parse_arguments(arg "${_options}" "${_single_args}" "${_multi_args}"
                          ${ARGN})

    if(DEFINED arg_FORCE)
        set("${arg_NAME}_FORCE" "${arg_FORCE}" CACHE INTERNAL
            "Forced value for `${arg_NAME}`." FORCE)
    elseif(DEFINED arg_DEFAULT)
        set("${arg_NAME}_INIT" "${arg_DEFAULT}" CACHE INTERNAL
            "Default value for `${arg_NAME}`." FORCE)
    endif()
endfunction()
