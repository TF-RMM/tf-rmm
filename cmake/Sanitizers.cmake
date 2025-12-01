#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

#
# Macro to strip sanitizer flags from CMAKE_C_FLAGS. This is used when building
# third-party libraries (e.g. MbedTLS, libspdm) as it triggers false positives.
# Call this after saving CMAKE_C_FLAGS and before add_subdirectory(), then
# restore CMAKE_C_FLAGS afterwards.
#
macro(strip_sanitizer_flags)
# Strip ICSAN flags as this trigger faults in MbedTLS and libspdm.
    if (ICSAN)
        string(REPLACE "-fno-sanitize-recover=implicit-conversion" "" CMAKE_C_FLAGS ${CMAKE_C_FLAGS})
        string(REPLACE "-fsanitize-trap=implicit-conversion" "" CMAKE_C_FLAGS ${CMAKE_C_FLAGS})
        string(REPLACE "-fsanitize=implicit-conversion" "" CMAKE_C_FLAGS ${CMAKE_C_FLAGS})
    endif()
endmacro()
