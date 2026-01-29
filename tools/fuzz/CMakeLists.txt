#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

if (HOST_VARIANT STREQUAL "host_fuzz")
    # Fuzz protocol header
    add_custom_command(OUTPUT "${CMAKE_SOURCE_DIR}/plat/host/host_fuzz/include/fuzzer_protocol.h"
            COMMAND python3 ${CMAKE_CURRENT_SOURCE_DIR}/python/create_fuzzer_protocol_header.py
            ${CMAKE_SOURCE_DIR}/plat/host/host_fuzz/include/fuzzer_protocol.h
            COMMENT "Generate protocol header"
    )

    add_custom_target(fuzzer-protocol ALL
            DEPENDS "${CMAKE_SOURCE_DIR}/plat/host/host_fuzz/include/fuzzer_protocol.h"
    )

    #     SMC corpus
    add_custom_command(OUTPUT "${CMAKE_BINARY_DIR}/smc_corpus"
            COMMAND python3 ${CMAKE_CURRENT_SOURCE_DIR}/python/generate_default_test.py ${CMAKE_BINARY_DIR}/smc_corpus/default.bin
            COMMENT "Generate default test as SMC corpus"

            COMMAND python3 ${CMAKE_CURRENT_SOURCE_DIR}/python/generate_minimal_test.py ${CMAKE_BINARY_DIR}/smc_corpus/min.bin
            COMMENT "Generate minimal test as SMC corpus"

            COMMAND python3 ${CMAKE_CURRENT_SOURCE_DIR}/python/generate_rtt_test.py ${CMAKE_BINARY_DIR}/smc_corpus/rtt.bin
            COMMENT "Generate minimal rtt as SMC corpus"

            COMMAND python3 ${CMAKE_CURRENT_SOURCE_DIR}/python/generate_rtt_fold_test.py ${CMAKE_BINARY_DIR}/smc_corpus/rtt-fold.bin
            COMMENT "Generate minimal rtt-fold as SMC corpus"

            COMMAND python3 ${CMAKE_CURRENT_SOURCE_DIR}/python/generate_ripas_test.py ${CMAKE_BINARY_DIR}/smc_corpus/ripas.bin
            COMMENT "Generate ripas test as SMC corpus"

            COMMAND python3 ${CMAKE_CURRENT_SOURCE_DIR}/python/generate_invalid_test.py ${CMAKE_BINARY_DIR}/smc_corpus/invalid.bin
            COMMENT "Generate invalid test as SMC corpus"

            COMMAND python3 ${CMAKE_CURRENT_SOURCE_DIR}/python/generate_pmu_test.py ${CMAKE_BINARY_DIR}/smc_corpus/pmu.bin
            COMMENT "Generate pmu test as SMC corpus"
    )

    add_custom_target(smc-corpus ALL
            DEPENDS "${CMAKE_BINARY_DIR}/smc_corpus"
    )

    add_dependencies(rmm-plat-host_fuzz smc-corpus)
    add_dependencies(rmm-plat-host_fuzz fuzzer-protocol)

    set(${FUZZ_BUILD_NAME} ENV{FUZZ_BUILD_NAME})

    set(CORPUS_DIR "${CMAKE_BINARY_DIR}/smc_corpus")
    set(FUZZ_ROOT "${CMAKE_BINARY_DIR}/../..")
    set(AFL_OUT_DIR "${FUZZ_ROOT}/aflout/${FUZZ_BUILD_NAME}")

    # Run AFL target
    add_custom_target(run-fuzzer
            COMMAND AFL_AUTORESUME=1
            afl-fuzz
            -i "${CORPUS_DIR}"
            -o "${AFL_OUT_DIR}"
            -S s-${FUZZ_BUILD_NAME}
#            -b 23 # use cpu 23
            -t 1000
            -a binary
            -P exploit
            -p mmopt
            -V 1000
            -- ${CMAKE_BINARY_DIR}/$<CONFIG>/rmm.elf @@
            COMMENT "Run fuzzer"
            DEPENDS rmm
    )

    # Quick run afl, plot and create coverage report
    add_custom_target(quick-bench
            COMMAND AFL_TRY_AFFINITY=23
            afl-fuzz
            -i "${CORPUS_DIR}"
            -o "${AFL_OUT_DIR}"
            -S s-${FUZZ_BUILD_NAME}
#            -b 23 # use cpu 23
            -t 1000
            -a binary
            -P exploit
            -p exploit
            -V 100
            -s 5330
            -- ${CMAKE_BINARY_DIR}/$<CONFIG>/rmm.elf @@ &&
            afl-plot  ${AFL_OUT_DIR}/s-${FUZZ_BUILD_NAME}/ ${FUZZ_ROOT}/bench/${FUZZ_BUILD_NAME} &&
            cmake --build ${CMAKE_BINARY_DIR} -- run-coverage &&
            echo "AFL Plot and Coverage Report:" &&
            echo "${FUZZ_ROOT}/bench/${FUZZ_BUILD_NAME}/index.html" &&
            echo "${CMAKE_BINARY_DIR}/builds/Debug/coverage/tf-rmm-coverage.html"
            COMMENT "Benchmark Fuzzer"
            DEPENDS rmm
    )

endif () # HOST_VARIANT STREQUAL "host_fuzz"
