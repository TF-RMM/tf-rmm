#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

if (HOST_VARIANT STREQUAL "host_fuzz")
    set(FUZZ_PROTOCOL_HEADER
        "${CMAKE_SOURCE_DIR}/plat/host/host_fuzz/include/fuzzer_protocol.h")
    set(FUZZ_PROTOCOL_GENERATOR
        "${CMAKE_CURRENT_SOURCE_DIR}/python/create_fuzzer_protocol_header.py")
    set(FUZZ_PROTOCOL_DEFINITION
        "${CMAKE_CURRENT_SOURCE_DIR}/python/fuzzer_protocol.py")
    set(FUZZ_CORPUS_SCRIPTS_DIR
        "${CMAKE_CURRENT_SOURCE_DIR}/python/corpus")
    set(FUZZ_CORPUS_DIR
        "${CMAKE_BINARY_DIR}/smc_corpus")

    # Fuzz protocol header
    add_custom_command(OUTPUT "${FUZZ_PROTOCOL_HEADER}"
            COMMAND python3 "${FUZZ_PROTOCOL_GENERATOR}" "${FUZZ_PROTOCOL_HEADER}"
            DEPENDS "${FUZZ_PROTOCOL_GENERATOR}" "${FUZZ_PROTOCOL_DEFINITION}"
            COMMENT "Generate protocol header"
            VERBATIM
    )

    add_custom_target(fuzzer-protocol ALL
            DEPENDS "${FUZZ_PROTOCOL_HEADER}"
    )

    # Corpora
    file(GLOB FUZZ_CORPUS_SCRIPTS CONFIGURE_DEPENDS
        "${FUZZ_CORPUS_SCRIPTS_DIR}/*.py")

    set(FUZZ_CORPUS_OUTPUTS)
    foreach(FUZZ_CORPUS_SCRIPT IN LISTS FUZZ_CORPUS_SCRIPTS)
        get_filename_component(FUZZ_CORPUS_NAME "${FUZZ_CORPUS_SCRIPT}" NAME_WE)
        set(FUZZ_CORPUS_OUTPUT "${FUZZ_CORPUS_DIR}/${FUZZ_CORPUS_NAME}.bin")

        add_custom_command(OUTPUT "${FUZZ_CORPUS_OUTPUT}"
                COMMAND "${CMAKE_COMMAND}" -E env "PYTHONPATH=${CMAKE_CURRENT_SOURCE_DIR}/python"
                        python3 "${FUZZ_CORPUS_SCRIPT}" "${FUZZ_CORPUS_OUTPUT}"
                DEPENDS "${FUZZ_CORPUS_SCRIPT}" "${FUZZ_PROTOCOL_DEFINITION}"
                COMMENT "Generate ${FUZZ_CORPUS_NAME} corpus"
                VERBATIM
        )

        list(APPEND FUZZ_CORPUS_OUTPUTS "${FUZZ_CORPUS_OUTPUT}")
    endforeach()

    add_custom_target(smc-corpus ALL
            DEPENDS ${FUZZ_CORPUS_OUTPUTS}
    )

    add_dependencies(rmm-plat-host_fuzz smc-corpus)
    add_dependencies(rmm-plat-host_fuzz fuzzer-protocol)

    set(${FUZZ_BUILD_NAME} ENV{FUZZ_BUILD_NAME})

    set(CORPUS_DIR "${FUZZ_CORPUS_DIR}")
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
