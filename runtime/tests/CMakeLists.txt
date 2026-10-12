#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

target_include_directories(rmm-runtime
    PRIVATE "tests")

# Add test functionality
rmm_build_unittest(NAME rmm_deactivate_tests
                   LIBRARIES rmm-platform
                   TARGET rmm-runtime
                   SOURCES "tests/rmm_deactivate_tests.cpp"
                   ADDITIONAL_TEST_GROUPS rmm_deactivate_boot_tests
                   ITERATIONS 1)

rmm_build_unittest(NAME status_tests
                   LIBRARIES rmm-platform
                   TARGET rmm-runtime
                   SOURCES "tests/status_tests.cpp"
                   ITERATIONS 1)

rmm_build_unittest(NAME pdev_comm_tests
                   LIBRARIES rmm-platform
                   TARGET rmm-runtime
                   SOURCES "tests/pdev_comm_tests.cpp"
                   ITERATIONS 1)

target_include_directories(rmm-runtime
    PRIVATE "${CMAKE_SOURCE_DIR}/plat/host/da/include"
            "${CMAKE_SOURCE_DIR}/ext/minicoro")

rmm_build_unittest(NAME host_da_e2e_tests
                   LIBRARIES rmm-platform
                   TARGET rmm-runtime
                   SOURCES "tests/host_da_e2e_tests.cpp"
                   RUN_ISOLATED_TESTS
                       pdev_yielded_abort_stop
                       pdev_failed_abort_stop
                       pdev_stop_copyout
                       vdev_pending_input)

set_tests_properties(
    host_da_e2e_tests::pdev_yielded_abort_stop
    host_da_e2e_tests::pdev_failed_abort_stop
    host_da_e2e_tests::pdev_stop_copyout
    host_da_e2e_tests::vdev_pending_input
    PROPERTIES RUN_SERIAL TRUE TIMEOUT 120)

rmm_build_unittest(NAME rsi_logger_tests
                   LIBRARIES rmm-platform
                   TARGET rmm-runtime
                   SOURCES "tests/rsi_logger_tests.cpp"
                   ITERATIONS 10)

rmm_build_unittest(NAME rsi_memory_tests
                   LIBRARIES rmm-platform
                   TARGET rmm-runtime
                   SOURCES "tests/rsi_memory_tests.cpp"
                   ITERATIONS 1)

rmm_build_unittest(NAME rec_sro_tests
                   LIBRARIES rmm-platform
                   TARGET rmm-runtime
                   SOURCES "tests/rec_sro_tests.cpp"
                   ITERATIONS 1)

rmm_build_unittest(NAME realm_sro_tests
                   LIBRARIES rmm-platform
                   TARGET rmm-runtime
                   SOURCES "tests/realm_sro_tests.cpp"
                   ITERATIONS 1)

rmm_build_unittest(NAME realm_bounds_tests
                   LIBRARIES rmm-platform
                   TARGET rmm-runtime
                   SOURCES "tests/realm_bounds_tests.cpp"
                   ITERATIONS 1)

rmm_build_unittest(NAME sro_donate_tests
                   LIBRARIES rmm-platform
                   TARGET rmm-runtime
                   SOURCES "tests/sro_donate_tests.cpp"
                   ITERATIONS 1)

rmm_build_unittest(NAME psmmu_sro_tests
                   LIBRARIES rmm-platform
                   TARGET rmm-runtime
                   SOURCES "tests/psmmu_sro_tests.cpp"
                   ITERATIONS 1)

rmm_build_unittest(NAME vdev_range_slot_tests
                   LIBRARIES rmm-platform
                   TARGET rmm-runtime
                   SOURCES "tests/vdev_range_slot_tests.cpp"
                   ITERATIONS 1)

rmm_build_unittest(NAME vdev_stream_range_tests
                   LIBRARIES rmm-platform
                   TARGET rmm-runtime
                   SOURCES "tests/vdev_stream_range_tests.cpp"
                   ITERATIONS 1)

rmm_build_unittest(NAME exit_esr_tests
                   LIBRARIES rmm-platform
                   TARGET rmm-runtime
                   SOURCES "tests/exit_esr_tests.cpp"
                   ITERATIONS 1)

rmm_build_unittest(NAME rtt_data_map_tests
                   LIBRARIES rmm-platform
                   TARGET rmm-runtime
                   SOURCES "tests/rtt_data_map_tests.cpp"
                   ITERATIONS 1)

rmm_build_unittest(NAME rtt_data_unmap_tests
                   LIBRARIES rmm-platform
                   TARGET rmm-runtime
                   SOURCES "tests/rtt_data_unmap_tests.cpp"
                   ITERATIONS 1)

rmm_build_unittest(NAME wfxt_exit_tests
                   LIBRARIES rmm-platform
                   TARGET rmm-runtime
                   SOURCES "tests/wfxt_exit_tests.cpp"
                   ITERATIONS 1)

rmm_build_unittest(NAME psci_features_tests
                   LIBRARIES rmm-platform
                   TARGET rmm-runtime
                   SOURCES "tests/psci_features_tests.cpp"
                   ITERATIONS 1)

rmm_build_unittest(NAME rtt_read_entry_dev_tests
                   LIBRARIES rmm-platform
                   TARGET rmm-runtime
                   SOURCES "tests/rtt_read_entry_dev_tests.cpp"
                   ITERATIONS 1)

rmm_build_unittest(NAME hash_algo_sha384_tests
                   LIBRARIES rmm-platform
                   TARGET rmm-runtime
                   SOURCES "tests/hash_algo_sha384_tests.cpp"
                   ITERATIONS 1)

rmm_build_unittest(NAME psci_affinity_info_tests
                   LIBRARIES rmm-platform
                   TARGET rmm-runtime
                   SOURCES "tests/psci_affinity_info_tests.cpp"
                   ITERATIONS 1)
