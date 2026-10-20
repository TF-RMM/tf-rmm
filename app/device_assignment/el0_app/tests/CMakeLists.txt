#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

# Keep the app's Mbed TLS configuration and service mocks in their own process.
# Compile the production sources so the tests use the registered callbacks.
get_target_property(DA_TEST_SOURCES rmm-app-dev-assign-elf SOURCES)
add_executable(dev_assign_response_tests
    ${DA_TEST_SOURCES}
    "tests/dev_assign_response_tests.cpp")

target_include_directories(dev_assign_response_tests PRIVATE
    "$<TARGET_PROPERTY:rmm-app-dev-assign-elf,INCLUDE_DIRECTORIES>")
target_compile_definitions(dev_assign_response_tests PRIVATE
    "$<TARGET_PROPERTY:rmm-app-dev-assign-elf,COMPILE_DEFINITIONS>")
target_link_libraries(dev_assign_response_tests PRIVATE
    "$<TARGET_PROPERTY:rmm-app-dev-assign-elf,LINK_LIBRARIES>"
    CppUTest)

add_test(NAME dev_assign_response_tests COMMAND dev_assign_response_tests)
set_tests_properties(dev_assign_response_tests PROPERTIES TIMEOUT 30)
add_dependencies(run-unittests dev_assign_response_tests)
