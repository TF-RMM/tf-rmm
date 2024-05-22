#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

include(FetchContent)
include("${SOURCE_DIR}/tools/cbmc/SummaryHelpers.cmake")
find_program(RMM_CBMC_PATH "cbmc"
    DOC "Path to cbmc.")
find_program(RMM_GOTO_CC_PATH "goto-cc"
    DOC "Path to goto-cc.")
find_program(RMM_CBMC_VIEWER_PATH "cbmc-viewer"
    DOC "Path to cbmc-viewer.")
find_program(RMM_GCC_PATH "gcc"
    DOC "Path to gcc.")

find_package(Python3 REQUIRED)
find_program(CHECK_CBMC_SUMMARY_EXECUTABLE "compare_summary.py"
  PATHS ${CMAKE_SOURCE_DIR}
  PATH_SUFFIXES tools/cbmc
  DOC "Path to compare_summary.py"
  )

#
# Configure and execute CBMC
#
if(NOT (EXISTS "${RMM_CBMC_PATH}"))
  message(FATAL_ERROR "cbmc executable not found. (${RMM_CBMC_PATH})")
endif()

string(TOLOWER "${RMM_CBMC_CONFIGURATION}" CBMC_RESULT_FILE_SUFFIX)

if(RMM_CBMC_VIEWER_OUTPUT)
  set(CBMC_OUT_FILE_ENDING "xml")
  set(CBMC_UI_OPTION "--xml-ui")
else()
  set(CBMC_OUT_FILE_ENDING "output")
  set(CBMC_UI_OPTION "")
endif()

if(${RMM_CBMC_CONFIGURATION} STREQUAL "GCC")
  set(COMPILED_FILE_PREFIX "gcc")
  set(RMM_CBMC_COMPILER_PATH "${RMM_GCC_PATH}")
  list(APPEND RMM_IMP_SRCS "${TESTBENCH_DIR}/../gcc/gcc_defs.c")
else()
  set(COMPILED_FILE_PREFIX "goto_cc")
  set(RMM_CBMC_COMPILER_PATH "${RMM_GOTO_CC_PATH}")
endif()

set(RMM_TESTBENCH_RESULT_DIR "${BINARY_DIR}/cbmc_${CBMC_RESULT_FILE_SUFFIX}_results")
set(SUMMARY_FILE "SUMMARY.${CBMC_RESULT_FILE_SUFFIX}")
set(RMM_CBMC_SUMMARY_FIELD_WIDTH 38)

# Configurations for the initial state.
set(GRANULE_SHIFT "9")
set(MAX_NUM_OF_GRANULE "4")
math(EXPR HOST_MEM_SIZE "(1 << ${GRANULE_SHIFT}) * ${MAX_NUM_OF_GRANULE}")
set(HOST_MEM_SIZE "${HOST_MEM_SIZE}UL")

set(MAX_RTT_UNWIND "6")
set(MAX_AUX_REC "2")
set(MAX_ROOT_RTT "3")
set(MAX_UNWIND_FLAGS "")

#
# Set up cbmc command line
#
set(cbmc_unwinds_list
  "--unwindset;find_lock_granules.3:${MAX_ROOT_RTT}"
  "--unwindset;find_lock_rd_granules.0:${MAX_RTT_UNWIND}"
  "--unwindset;find_lock_rd_granules.1:${MAX_RTT_UNWIND}"
  "--unwindset;free_rec_aux_granules.0:${MAX_AUX_REC}"
  "--unwindset;free_sl_rtts.0:${MAX_RTT_UNWIND}"
  "--unwindset;init_realm_descriptor_page.0:${MAX_ROOT_RTT}"
  "--unwindset;init_realm_descriptor_page.1:${MAX_ROOT_RTT}"
  "--unwindset;init_rec.0:${MAX_AUX_REC}"
  "--unwindset;init_rtt_root_page.0:${MAX_ROOT_RTT}"
  "--unwindset;init_walk_path.0:${MAX_RTT_UNWIND}"
  "--unwindset;lock_order_invariable.0:21"
  "--unwindset;lock_order_invariable.1:11"
  "--unwindset;lock_order_invariable.2:"
  "--unwindset;RealmIsLive.0:${MAX_ROOT_RTT}"
  "--unwindset;RealmIsLive.2:${MAX_ROOT_RTT}"
  "--unwindset;rtt_walk_lock_unlock.0:${MAX_RTT_UNWIND}"
  "--unwindset;RttWalk.0:${MAX_RTT_UNWIND}"
  "--unwindset;smc_realm_create.0:${MAX_RTT_UNWIND}"
  "--unwindset;smc_rec_create.0:${MAX_AUX_REC}"
  "--unwindset;total_root_rtt_refcount.0:${MAX_RTT_UNWIND}"
)

set(cbmc_defines_list
  "-DCBMC"
  "-DGRANULE_SHIFT=${GRANULE_SHIFT}"
  "-DXLAT_GRANULARITY_SIZE_SHIFT=${GRANULE_SHIFT}"
  "-DRMM_MAX_GRANULES=${MAX_NUM_OF_GRANULE}"
  "-DMAX_CPUS=1"
  "-DMAX_RTT_LEVEL=${MAX_RTT_UNWIND}"
  "-DHOST_MEM_SIZE=${HOST_MEM_SIZE}"
  "-DNAME=\"RMM\""
  "-DVERSION=\"CBMC\""
  "-DCOMMIT_INFO=\"CBMC\""
  "-DRMM_NUM_PAGES_PER_STACK=1"
)

# CBMC flags for memory safety analysis and undefined behaviour analysis.
set(cbmc_analysis_flags_list
  "--bounds-check"
  "--pointer-check"
  "--div-by-zero-check"
  "--signed-overflow-check"
  "--unsigned-overflow-check"
  "--pointer-overflow-check"
  "--conversion-check"
  "--undefined-shift-check"
  "--float-overflow-check"
  "--nan-check"
  "--enum-range-check"
  "--pointer-primitive-check"
  "--memory-leak-check")

set(cbmc_flags_list
  "--timestamp;wall"
  "--verbosity;9"
  # Optimisation flags:
  "--drop-unused-functions"
  "--reachability-slice"
  )

if("${RMM_CBMC_CONFIGURATION}" STREQUAL "COVERAGE")
  list(APPEND cbmc_flags_list
    "--cover;cover"
    "--no-assertions")
elseif("${RMM_CBMC_CONFIGURATION}" STREQUAL "ASSERT")
  list(APPEND cbmc_flags_list
    "--unwinding-assertions"
    "--trace"
    "--trace-show-function-calls")
elseif("${RMM_CBMC_CONFIGURATION}" STREQUAL "ANALYSIS")
  list(APPEND cbmc_flags_list
    "--unwinding-assertions"
    "${cbmc_analysis_flags_list}")
elseif("${RMM_CBMC_CONFIGURATION}" STREQUAL "GCC")
  list(APPEND cbmc_compiler_options
    "-Wall"
    "-Werror"
    "-Wno-unused-function"
    "-Wno-main" # Do not warning on the non-standard signature of main
    "-Wno-error=unused-variable" # Some of the testbenches contain unused variables
    "-include;${TESTBENCH_DIR}/../gcc/gcc_defs.h")
else()
  message(FATAL_ERROR "Invalid RMM_CBMC_CONFIGURATION '${RMM_CBMC_CONFIGURATION}'")
endif()

# Convert the space separated strings to a CMake list
string(REPLACE " " ";" TESTBENCH_FILES "${TESTBENCH_FILES}")

#
# Create semi-colon separated list from white-space seperated ones.
#
separate_arguments(RMM_IMP_SRCS)
separate_arguments(RMM_IMP_INCS)

#
# Execute CBMC on the testbench files
#
rmm_cbmc_write_summary_header(${RMM_CBMC_SUMMARY_FIELD_WIDTH}
  ${RMM_TESTBENCH_RESULT_DIR} ${SUMMARY_FILE} ${RMM_CBMC_CONFIGURATION})

function(rmm_cbmc_gen_file_names
  testbench_file_path
  filename_prefix
  out_file_ending
  cmd_file_var_name
  out_file_var_name
  err_file_var_name)
  get_filename_component(testbench_file_name "${testbench_file_path}" NAME)
  get_filename_component(parent "${testbench_file_path}" DIRECTORY)
  set("${cmd_file_var_name}" "${parent}/${filename_prefix}_${testbench_file_name}.cmd" PARENT_SCOPE)
  set("${out_file_var_name}" "${parent}/${filename_prefix}_${testbench_file_name}.${out_file_ending}" PARENT_SCOPE)
  set("${err_file_var_name}" "${parent}/${filename_prefix}_${testbench_file_name}.error" PARENT_SCOPE)
endfunction()

function(normalise_cmd cmd_str out_var_name)
  # replace the ; with space
  string (REPLACE ";" " " cmd_str "${cmd_str}")
  set("${out_var_name}" "${cmd_str}" PARENT_SCOPE)
endfunction()

foreach(testbench_file ${TESTBENCH_FILES})

  string(REPLACE ${TESTBENCH_DIR}/ "" testbench_filename ${testbench_file})
  string(REGEX REPLACE "\\.[^\\.]*$" "" entry_point "${testbench_filename}")

  set(RMM_GOTO_PROG_NAME "${RMM_TESTBENCH_RESULT_DIR}/rmm_${entry_point}.goto")

  # Set the names of output files
  string(REPLACE ${TESTBENCH_DIR} ${RMM_TESTBENCH_RESULT_DIR} OUT_FILE_NAME_PREFIX "${testbench_file}")
  rmm_cbmc_gen_file_names(${OUT_FILE_NAME_PREFIX} "cbmc" "${CBMC_OUT_FILE_ENDING}"
    cbmc_cmd_file cbmc_output_file cbmc_error_file)
  rmm_cbmc_gen_file_names(${OUT_FILE_NAME_PREFIX} "cbmc_prop" "xml"
    cbmc_prop_cmd_file cbmc_prop_output_file cbmc_prop_error_file)
  rmm_cbmc_gen_file_names(${OUT_FILE_NAME_PREFIX} "${COMPILED_FILE_PREFIX}" "output"
    compile_cmd_file compile_output_file compile_error_file)
  rmm_cbmc_gen_file_names(${OUT_FILE_NAME_PREFIX} "cbmc_viewer" "output"
    cbmc_viewer_cmd_file cbmc_viewer_output_file cbmc_viewer_error_file)
  set(CBMC_VIEWER_REPORT_DIR "${RMM_TESTBENCH_RESULT_DIR}/report_${entry_point}")

  if(${RMM_CBMC_CONFIGURATION} STREQUAL "GCC")
    set(CBMC_ENTRY_POINT "-D${entry_point}=main")
  else()
    set(CBMC_ENTRY_POINT "--function;${entry_point}")
  endif()

  set(compile_cmd
    ${RMM_CBMC_COMPILER_PATH}
    ${cbmc_compiler_options}
    ${cbmc_defines_list}
    ${CBMC_ENTRY_POINT}
    "-o;${RMM_GOTO_PROG_NAME}"
    ${RMM_IMP_INCS}
    ${RMM_IMP_SRCS}
    ${testbench_file}
  )

  set(cbmc_cmd
    ${RMM_CBMC_PATH}
    ${CBMC_UI_OPTION}
    ${cbmc_flags_list}
    ${cbmc_unwinds_list}
    ${RMM_GOTO_PROG_NAME})

  set(cbmc_prop_cmd
    ${RMM_CBMC_PATH}
    ${cbmc_flags_list}
    "--xml-ui"
    "--show-properties"
    ${RMM_GOTO_PROG_NAME})

  set(cbmc_viewer_cmd
    "${RMM_CBMC_VIEWER_PATH}"
    "--goto;${RMM_GOTO_PROG_NAME}"
    "--result;${cbmc_output_file}"
    "--property;${cbmc_prop_output_file}"
    "--srcdir;${CMAKE_SOURCE_DIR}"
    "--reportdir;${CBMC_VIEWER_REPORT_DIR}")

  # remove the absolute path making it relative (shorten the command line)
  string (REPLACE "${SOURCE_DIR}/" "" compile_cmd "${compile_cmd}")

  normalise_cmd("${compile_cmd}" COMPILE_CMD_STR)
  normalise_cmd("${cbmc_cmd}" CBMC_CMD_STR)

  file(WRITE ${compile_cmd_file} "${COMPILE_CMD_STR}")
  file(WRITE ${cbmc_cmd_file} "${CBMC_CMD_STR}")

  execute_process(COMMAND ${CMAKE_COMMAND} -E echo_append "CBMC: ${testbench_file}... ")
  execute_process(
      COMMAND ${compile_cmd}
      RESULT_VARIABLE res_var
      OUTPUT_FILE ${compile_output_file}
      ERROR_FILE ${compile_error_file})
  if (NOT ${res_var} EQUAL "0")
    message(FATAL_ERROR "Compiling testbench with ${RMM_CBMC_COMPILER_PATH} failed. For details see: ${compile_error_file}")
  endif()

  # Only run CBMC if not using compiler-only mode:
  if(NOT ${RMM_CBMC_CONFIGURATION} STREQUAL "GCC")
    execute_process(
        COMMAND ${cbmc_cmd}
        RESULT_VARIABLE res_var
        OUTPUT_FILE ${cbmc_output_file}
        ERROR_FILE ${cbmc_error_file})

    if(RMM_CBMC_VIEWER_OUTPUT)
      normalise_cmd("${cbmc_prop_cmd}" CBMC_PROP_CMD_STR)
      file(WRITE ${cbmc_prop_cmd_file} "${CBMC_PROP_CMD_STR}")
      execute_process(
        COMMAND ${cbmc_prop_cmd}
        RESULT_VARIABLE res_var
        OUTPUT_FILE ${cbmc_prop_output_file}
        ERROR_FILE ${cbmc_prop_error_file})

      normalise_cmd("${cbmc_viewer_cmd}" CBMC_VIEWER_CMD_STR)
      file(WRITE ${cbmc_viewer_cmd_file} "${CBMC_VIEWER_CMD_STR}")
      execute_process(
        COMMAND ${cbmc_viewer_cmd}
        RESULT_VARIABLE res_var
        OUTPUT_FILE ${cbmc_viewer_output_file}
        ERROR_FILE ${cbmc_viewer_error_file})
      if (NOT ${res_var} EQUAL "0")
        message(FATAL_ERROR "Failed to run cbmc-viewer. For details see: ${cbmc_viewer_error_file}")
      endif()
    endif()

    rmm_cbmc_append_summary("${testbench_filename}" "${cbmc_output_file}"
      "${CBMC_RESULT_FILE_SUFFIX}-${CBMC_OUT_FILE_ENDING}"
      ${RMM_CBMC_SUMMARY_FIELD_WIDTH} ${RMM_TESTBENCH_RESULT_DIR} ${SUMMARY_FILE})

  endif()

  execute_process(COMMAND ${CMAKE_COMMAND} -E echo "DONE")

endforeach()
message(STATUS "Result in ${RMM_TESTBENCH_RESULT_DIR}")

# Only run CBMC if not using compiler-only mode:
if(NOT ${RMM_CBMC_CONFIGURATION} STREQUAL "GCC")
  list(TRANSFORM TESTBENCH_FILES REPLACE "${TESTBENCH_DIR}/" "" OUTPUT_VARIABLE TESTBENCH_FILENAMES)
  execute_process(
    WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}
    COMMAND ${CHECK_CBMC_SUMMARY_EXECUTABLE}
      ${CMAKE_SOURCE_DIR}/tools/cbmc/testbenches_results/BASELINE.${CBMC_RESULT_FILE_SUFFIX}
      --testbench-files "${TESTBENCH_FILENAMES}"
      ${RMM_TESTBENCH_RESULT_DIR}/${SUMMARY_FILE}
    OUTPUT_VARIABLE CHECK_SUMMARY_OUTPUT
    ERROR_VARIABLE CHECK_SUMMARY_ERROR
    RESULT_VARIABLE CHECK_SUMMARY_RC
    OUTPUT_STRIP_TRAILING_WHITESPACE
    )

  if (NOT ${CHECK_SUMMARY_RC} EQUAL "0")
    message(WARNING
      "cbmc-${CBMC_RESULT_FILE_SUFFIX}: FAILED\n${CHECK_SUMMARY_ERROR}")
  else()
    message(STATUS "cbmc-${CBMC_RESULT_FILE_SUFFIX}: PASSED")
  endif()
endif()
