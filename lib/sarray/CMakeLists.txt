#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

add_library(rmm-lib-sarray)

target_link_libraries(rmm-lib-sarray
  PRIVATE
    rmm-lib-common
)

target_include_directories(rmm-lib-sarray
  PUBLIC "include")

target_sources(rmm-lib-sarray
  PRIVATE
    "src/sarray.c")

include("tests/CMakeLists.txt")
