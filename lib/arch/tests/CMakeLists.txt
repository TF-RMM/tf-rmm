#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

target_include_directories(rmm-lib-arch
	PRIVATE "tests")

# Add test functionality
rmm_build_unittest(NAME simd
		   LIBRARIES rmm-platform
		   TARGET rmm-lib-arch
		   SOURCES "tests/simd_tests.cpp"
			   "tests/simd_test_helpers.c"
		   ITERATIONS 10)
