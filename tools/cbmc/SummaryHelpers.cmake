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

function(rmm_cbmc_append_summary testbench_filename output_file summary_width result_dir file summary_pattern)
  rmm_cbmc_align_to_middle(${summary_width} " " ${testbench_filename})
  set(testbench_filename "${aligned_text}")

  execute_process(COMMAND grep -E "${summary_pattern}" ${output_file} OUTPUT_VARIABLE testbench_result)

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
