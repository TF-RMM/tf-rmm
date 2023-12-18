#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

#
# Helper functions for formatting the summary file
#

function(rmm_cbmc_align_to_middle field_width padding_character text)
  set (pad_pool "")
  foreach(i RANGE ${field_width})
    string(APPEND pad_pool ${padding_character})
  endforeach()
  string(LENGTH ${text} text_len)
  math(EXPR leading_space "(${field_width} - ${text_len}) / 2")
  math(EXPR trailing_space "${field_width} - ${text_len} - ${leading_space}")
  string (SUBSTRING ${pad_pool} 0 ${leading_space} leading_spaces)
  string (SUBSTRING ${pad_pool} 0 ${trailing_space} trailing_spaces)

  set(aligned_text "")
  string (APPEND aligned_text "${leading_spaces}" "${text}" "${trailing_spaces}")
  set(aligned_text "${aligned_text}" PARENT_SCOPE)
endfunction()

function(rmm_cbmc_append_separator summary_width result_dir file)
  rmm_cbmc_align_to_middle(${summary_width} "-" "-")
  set(separator_line "")
  string(APPEND separator_line "+" "${aligned_text}" "+" "${aligned_text}" "+\n")
  file(APPEND ${result_dir}/${file} ${separator_line})
endfunction()

function(rmm_cbmc_write_summary_header summary_width result_dir file summary_header)
  file(MAKE_DIRECTORY ${result_dir})
  file(WRITE ${result_dir}/${file} "")
  rmm_cbmc_append_separator(${summary_width} ${result_dir} ${file})
  rmm_cbmc_align_to_middle(${summary_width} " " "FILENAME")
  set(field1 "${aligned_text}")
  rmm_cbmc_align_to_middle(${summary_width} " " "${summary_header}")
  set(field2 "${aligned_text}")
  set(header "")
  string(APPEND header "|" "${field1}" "|" "${field2}" "|\n")
  file(APPEND ${result_dir}/${file} ${header})
  rmm_cbmc_append_separator(${summary_width} ${result_dir} ${file})
endfunction()

function (rmm_cbmc_generate_summary file mode summary_var_name)
  execute_process(COMMAND grep -cE "Solving with" ${output_file} OUTPUT_VARIABLE iteration_counts)
  if(${iteration_counts} EQUAL "0")
    set("${summary_var_name}" "" PARENT_SCOPE)
    return()
  endif()
  if(("${mode}" STREQUAL "assert-output") OR ("${mode}" STREQUAL "analysis-output"))
    execute_process(COMMAND grep -cE "\\[.*\\] .*: SUCCESS" ${output_file} OUTPUT_VARIABLE passed_asserts)
    execute_process(COMMAND grep -cE "\\[.*\\] .*: FAILURE" ${output_file} OUTPUT_VARIABLE failed_asserts)
    math(EXPR all_asserts "${passed_asserts} + ${failed_asserts}")
    set("${summary_var_name}" "** ${failed_asserts} of ${all_asserts} failed (${iteration_counts} iterations)" PARENT_SCOPE)
  elseif(("${mode}" STREQUAL "assert-xml") OR ("${mode}" STREQUAL "analysis-xml"))
    execute_process(COMMAND grep -cE "property=.*status=.SUCCESS" ${output_file} OUTPUT_VARIABLE passed_asserts)
    execute_process(COMMAND grep -cE "property=.*status=.FAILURE" ${output_file} OUTPUT_VARIABLE failed_asserts)
    math(EXPR all_asserts "${passed_asserts} + ${failed_asserts}")
    set("${summary_var_name}" "** ${failed_asserts} of ${all_asserts} failed (${iteration_counts} iterations)" PARENT_SCOPE)
  elseif(("${mode}" STREQUAL "coverage-xml") OR ("${mode}" STREQUAL "coverage-output"))
    execute_process(COMMAND grep -cE "\\[.*\\] file .* line .* function .*: SATISFIED" ${output_file} OUTPUT_VARIABLE passed_coverages)
    execute_process(COMMAND grep -cE "\\[.*\\] file .* line .* function .*: FAILED" ${output_file} OUTPUT_VARIABLE failed_coverages)
    math(EXPR all_coverages "${passed_coverages} + ${failed_coverages}")
    math(EXPR cover_percent_int_part "${passed_coverages} * 100 / ${all_coverages}")
    math(EXPR cover_percent_dec_part "(${passed_coverages} * 1000 / ${all_coverages}) % 10")
    set("${summary_var_name}" "** ${passed_coverages} of ${all_coverages} covered (${cover_percent_int_part}.${cover_percent_dec_part}%)" PARENT_SCOPE)
  else()
    message(FATAL_ERROR "Unknown mode ${mode}")
  endif()

endfunction()

function(rmm_cbmc_append_summary testbench_filename output_file mode summary_width result_dir file)
  rmm_cbmc_align_to_middle(${summary_width} " " ${testbench_filename})
  set(testbench_filename "${aligned_text}")

  rmm_cbmc_generate_summary("${output_file}" "${mode}" testbench_result)

  if("${testbench_result}" STREQUAL "")
    rmm_cbmc_align_to_middle(${summary_width} " " "N/A")
    set(testbench_result "${aligned_text}")
  endif()

  string(REPLACE "\n" "" testbench_result "${testbench_result}")
  string(REGEX REPLACE "[^\\*]*\\*\\*[\\s]*" "" testbench_result "${testbench_result}")

  rmm_cbmc_align_to_middle(${summary_width} " " ${testbench_result})
  set(testbench_result "${aligned_text}")

  string(APPEND summary_data "|${testbench_filename}|${testbench_result}|\n")
  file(APPEND ${result_dir}/${file} ${summary_data})
  rmm_cbmc_append_separator(${summary_width} ${result_dir} ${file})
endfunction()
