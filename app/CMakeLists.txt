#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

# List of libraries that are included in the app stub library
set(RMM_EL2_STUB_LIBRARIES "")

add_subdirectory("common")

# List of apps to be packaged to final binary
# The contents of the list is populated by the CMakeLists in the subdirectories
set(EL0_APP_BIN_LIST "")

set(EL0_APP_BIN_LIST ${EL0_APP_BIN_LIST} PARENT_SCOPE)

add_library(rmm-el2-stub INTERFACE)
target_link_libraries(rmm-el2-stub
    INTERFACE ${RMM_EL2_STUB_LIBRARIES})
