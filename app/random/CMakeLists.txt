#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

add_subdirectory("el0_app")
add_subdirectory("rmm_stub")

set(EL0_APP_BIN_LIST ${EL0_APP_BIN_LIST} PARENT_SCOPE)
set(RMM_EL2_STUB_LIBRARIES ${RMM_EL2_STUB_LIBRARIES} PARENT_SCOPE)
