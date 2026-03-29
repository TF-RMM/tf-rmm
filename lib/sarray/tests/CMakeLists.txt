#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

rmm_build_unittest(NAME sarray_tests
                   LIBRARIES rmm-platform
                   TARGET rmm-lib-sarray
                   SOURCES "tests/sarray_tests.cpp")
