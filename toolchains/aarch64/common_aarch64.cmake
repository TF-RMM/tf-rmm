#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

include_guard()

include(${CMAKE_CURRENT_LIST_DIR}/../common.cmake)

set(CMAKE_SYSTEM_PROCESSOR aarch64)

foreach(language IN ITEMS ASM C)
	string(APPEND CMAKE_${language}_FLAGS_INIT "-ffreestanding ")
	string(APPEND CMAKE_${language}_FLAGS_INIT "-march=armv8.5-a ")
	string(APPEND CMAKE_${language}_FLAGS_INIT "-mbranch-protection=standard ")
	string(APPEND CMAKE_${language}_FLAGS_INIT "-mgeneral-regs-only ")
	string(APPEND CMAKE_${language}_FLAGS_INIT "-mstrict-align ")
	string(APPEND CMAKE_${language}_FLAGS_INIT "-fpie ")
	# Omit the frame pointer for Release build, this also disables
	# backtrace in the exception handler.
	string(APPEND CMAKE_${language}_FLAGS_RELEASE_INIT "-fomit-frame-pointer ")
	string(APPEND CMAKE_${language}_FLAGS_DEBUG_INIT "-fno-omit-frame-pointer ")
endforeach()

string(APPEND CMAKE_EXE_LINKER_FLAGS_INIT "-nostdlib ")
string(APPEND CMAKE_EXE_LINKER_FLAGS_INIT "-Wl,-pie ")
