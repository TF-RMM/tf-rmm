#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

#
# This script is called from main CMakeLists.txt to determine if code complies
# to coding standards as mentioned in docs/getting_started/coding-standard.rst
#
# Runs checkpatch.pl on entire codebase if variable CHECKCODEBASE_RUN is defined.
#
# Runs checkpatch.pl on new commits if variable CHECKCODEBASE_RUN is defined.
#
find_package(Git REQUIRED)
find_package(Perl REQUIRED)
find_program(CHECKPATCH_EXECUTABLE "checkpatch.pl"
  PATHS ${CMAKE_SOURCE_DIR}
  PATH_SUFFIXES tools/checkpatch
  DOC "Path to checkpatch.pl"
  )

find_program(COMMITMSGCHECK_EXECUTABLE "checkcommitmsg.py"
  PATHS ${CMAKE_SOURCE_DIR}
  PATH_SUFFIXES tools/checkpatch
  DOC "Path to checkcommitmsg.py"
)

list(APPEND CMAKE_MODULE_PATH "${CMAKE_SOURCE_DIR}/tools/common")
include(GitUtils)

#
# List of directories and files to exclude from checking for target checkcodebase
#
list(APPEND glob_excludes "^.git")
list(APPEND glob_excludes "^out")
list(APPEND glob_excludes "^build")
list(APPEND glob_excludes "^ext")
list(APPEND glob_excludes "^tools")
list(APPEND glob_excludes ".patch$")
list(APPEND glob_excludes ".md$")
list(APPEND glob_excludes "~$")
list(APPEND glob_excludes ".swp$")
list(APPEND glob_excludes "^cscope.")

set(total_errors "0")
set(total_warnings "0")

# Check if pre-reqs met
if(PERL_NOT_FOUND OR NOT EXISTS ${CHECKPATCH_EXECUTABLE})
  message(FATAL_ERROR "required dependencies not found")
endif()

#
# print_output_without_total: Remove the "total:" line from an output and print
# the new output.
#
function(print_output_without_total output)
  string(FIND "${output}" "\ntotal:" idx REVERSE)
  string(SUBSTRING "${output}" 0 ${idx} output_without_total)

  if(output_without_total)
    message("${output_without_total}")
  endif()
endfunction()

#
# checkpatch_get_stats: Parse and returns number of errors and warnings
#
function(checkpatch_get_stats stats_arg errors_ret warnings_ret)
  string(FIND "${stats_arg}" "total:" idx REVERSE)
  string(LENGTH "${stats_arg}" len)
  string(SUBSTRING "${stats_arg}" ${idx} ${len} last_line)

  string(REPLACE " " ";" last_line_list ${last_line})
  list(GET last_line_list 1 errors)
  list(GET last_line_list 3 warnings)

  set(${errors_ret} ${errors} PARENT_SCOPE)
  set(${warnings_ret} ${warnings} PARENT_SCOPE)
endfunction()

#
# print_stats_and_exit: Print summary of all errors and warnings.
# If there are errors call message(FATAL_ERROR)
#
function(print_stats_and_exit check_type total_errors total_warnings)
  message(STATUS "${check_type}: total errors: ${total_errors} "
    "warnings: ${total_warnings}")

  if(${total_errors} GREATER 0)
    message(FATAL_ERROR "${check_type}: FAILED")
  endif()

  message(STATUS "${check_type}: PASSED")
endfunction()

#
# Run checkpatch on entire codebase. This verifies all files in this repository
# except the files listed in "glob_excludes".
#
# Exits with FATAL_ERROR upon errors. Warnings are ignored (temporary)
#
if(CHECKCODEBASE_RUN)
  set(source_files "")

  if (GIT_FOUND AND IS_DIRECTORY .git)
    Git_Get_All_Files(source_files)
  else()
    file(GLOB_RECURSE source_files RELATIVE ${CMAKE_SOURCE_DIR} "*")
  endif()

  # Filter out 'glob_excludes'
  foreach(exclude IN LISTS glob_excludes)
    list(FILTER source_files EXCLUDE REGEX "${exclude}")
  endforeach()

  if(NOT source_files)
    message(STATUS "checkcodebase: No files to check")
    return()
  endif()

  foreach(source_file ${source_files})
    execute_process(
      COMMAND ${CMAKE_COMMAND} -E echo "Checking file ${source_file}"
      )

    execute_process(
      WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}
      COMMAND ${CHECKPATCH_EXECUTABLE} -f ${source_file}
      OUTPUT_VARIABLE checkpatch_output
      RESULT_VARIABLE checkpatch_rc
      ECHO_OUTPUT_VARIABLE
      OUTPUT_STRIP_TRAILING_WHITESPACE
      )

    # checkpatch.pl failed for this file. Collect no.of errors and warnings
    if(${checkpatch_rc})
      checkpatch_get_stats("${checkpatch_output}" errors warnings)
      MATH(EXPR total_errors "${total_errors}+${errors}")
      MATH(EXPR total_warnings "${total_warnings}+${warnings}")
    endif()
  endforeach()

  print_stats_and_exit("checkcodebase" ${total_errors}, ${total_warnings})
endif()

#
# Run checkpatch on pending commits.
#
# Exits with FATAL_ERROR upon errors.
#
if(CHECKPATCH_RUN)
  if(GIT_NOT_FOUND OR NOT IS_DIRECTORY .git)
    message(FATAL_ERROR "Required dependencies Git not found")
  endif()

  # Get list of commits to check
  Git_Get_Pending_Commits(pending_commits)

  foreach(commit IN LISTS pending_commits)
    message(STATUS "Checking commit: ${commit}")

    Git_Get_Files_In_Commit("${commit}" source_files)

    foreach(exclude IN LISTS glob_excludes)
      list(FILTER source_files EXCLUDE REGEX "${exclude}")
    endforeach()

    if(NOT source_files)
      message(STATUS "checkpatch: No files to check in this commit")
      continue()
    endif()

    execute_process(
      WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}
      COMMAND ${GIT_EXECUTABLE} diff --format=email "${commit}~..${commit}"
        -- ${source_files}
      COMMAND ${CHECKPATCH_EXECUTABLE} -
      OUTPUT_VARIABLE checkpatch_output
      RESULT_VARIABLE checkpatch_rc
      )

    #
    # Remove the "total:" line from the output as we will print the total errors
    # and warnings for the commit series later.
    #
    if(checkpatch_output)
      print_output_without_total("${checkpatch_output}")
    endif()

    # checkpatch.pl failed for this commit. Collect no.of errors and warnings
    if(${checkpatch_rc})
      checkpatch_get_stats("${checkpatch_output}" errors warnings)
      MATH(EXPR total_errors "${total_errors}+${errors}")
      MATH(EXPR total_warnings "${total_warnings}+${warnings}")
    endif()

    #
    # Check if commit was a merge. If so, we do not check the commit message.
    #
    set(merge_sha "")

    execute_process(
      WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}
      COMMAND ${GIT_EXECUTABLE} rev-list -1 --merges "${commit}~..${commit}"
      OUTPUT_VARIABLE merge_sha
      )

    if(${merge_sha})
      continue()
    endif()

    #
    # Get commit message text
    #
    execute_process(
      WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}
      COMMAND ${GIT_EXECUTABLE} log --format=%B -n 1 "${commit}"
      OUTPUT_VARIABLE commit_message
      )

    execute_process(
      WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}
      COMMAND ${COMMITMSGCHECK_EXECUTABLE}
        --project-root=${CMAKE_SOURCE_DIR}
        "${commit_message}"
      OUTPUT_VARIABLE checkcommitmsg_output
      RESULT_VARIABLE checkcommitmsg_rc
      )

    if(checkcommitmsg_output)
      print_output_without_total("${checkcommitmsg_output}")
    endif()

    checkpatch_get_stats("${checkcommitmsg_output}"
      commitmsg_errors commitmsg_warnings)
    MATH(EXPR total_errors "${total_errors} + ${commitmsg_errors}")
    MATH(EXPR total_warnings "${total_warnings} + ${commitmsg_warnings}")
  endforeach()

  print_stats_and_exit("checkpatch" ${total_errors}, ${total_warnings})
endif()
