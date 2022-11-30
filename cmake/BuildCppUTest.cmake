#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

#
# Remove Werror from CXXFLAGS else CppUTest compiler checks will fail.
# This will affect CMAKE_CXX_FLAG in the current scope and parent scope
# is unaffected.
#
string(REPLACE "-Werror" " " CMAKE_CXX_FLAGS ${CMAKE_CXX_FLAGS})

# Additional CXXFLAGS to get CppUTest to compile.
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wno-c++98-compat-pedantic ")

add_subdirectory("ext/cpputest")

