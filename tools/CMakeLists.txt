#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

arm_config_option(
    NAME RMM_STATIC_ANALYSIS
    HELP "Enable static analysis checkers.")

add_subdirectory("cppcheck")
add_subdirectory("cbmc")
