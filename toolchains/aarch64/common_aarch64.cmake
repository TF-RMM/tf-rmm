#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

include_guard()
include(CheckCCompilerFlag)

include(${CMAKE_CURRENT_LIST_DIR}/../common.cmake)

set(CMAKE_SYSTEM_PROCESSOR aarch64)

foreach(language IN ITEMS ASM C)
	string(APPEND CMAKE_${language}_FLAGS_INIT "-ffreestanding ")
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

# Detect applicable "march=" option supported by compiler
function(detect_and_set_march)
	set (march_list 9.2 9.1 9 8.8 8.7 8.6 8.5)
	set (march_num 9_2 9_1 9 8_8 8_7 8_6 8_5)

	foreach(v n IN ZIP_LISTS march_list march_num)
		check_c_compiler_flag("-march=armv${v}-a" COMPILER_SUPPORTS_${n})
		if(COMPILER_SUPPORTS_${n})
			set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -march=armv${v}-a" PARENT_SCOPE)
			set(CMAKE_ASM_FLAGS "${CMAKE_ASM_FLAGS} -march=armv${v}-a" PARENT_SCOPE)
			return()
		endif()
	endforeach()
	message(FATAL_ERROR "Suitable -march not detected. Please upgrade aarch64 compiler." )
endfunction()
