#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

add_library(rmm-lib-console)

target_link_libraries(rmm-lib-console
  PRIVATE
    rmm-lib-common
)

target_include_directories(rmm-lib-console
  PUBLIC "include")

target_sources(rmm-lib-console
  PRIVATE
    "src/console.c")
