#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

#
# This script is called from main CMakeLists.txt to determine if SPDX headers
# are in proper format
#
find_package(Git REQUIRED)
find_package(Python3 REQUIRED)
find_program(CHECKSPDX_EXECUTABLE "checkspdx.py"
  PATHS ${CMAKE_SOURCE_DIR}
  PATH_SUFFIXES tools/checkspdx
  DOC "Path to checkspdx.py"
  )

list(APPEND CMAKE_MODULE_PATH "${CMAKE_SOURCE_DIR}/tools/common")
include(GitUtils)

# List of directories and files to exclude from checking for target
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
list(APPEND glob_excludes ".png$")
list(APPEND glob_excludes "LICENSE")
list(APPEND glob_excludes "DCO")
list(APPEND glob_excludes "docs/global_substitutions.txt")

# checkspdx_get_stats: Parse and returns number of errors and warnings
function(checkspdx_get_stats stats_arg errors_ret)
  string(FIND "${stats_arg}" "total:" idx REVERSE)
  if(NOT ${idx} EQUAL -1)
    string(LENGTH "${stats_arg}" len)
    string(SUBSTRING "${stats_arg}" ${idx} ${len} last_line)

    string(REPLACE " " ";" last_line_list ${last_line})
    list(GET last_line_list 1 errors)
  else()
    set(errors 1)
  endif()

  set(${errors_ret} ${errors} PARENT_SCOPE)
endfunction()

#
# print_stats_and_exit: Print summary of all errors and warnings.
# If there are errors call message(FATAL_ERROR)
#
function(print_stats_and_exit check_type total_errors)
  message(STATUS "${check_type}: total errors: ${total_errors}")

  if(${total_errors} GREATER 0)
    message(FATAL_ERROR "${check_type}: FAILED")
  endif()

  message(STATUS "${check_type}: PASSED")
endfunction()

# Run checkspdx.py on the list of files.
function(run_checkspdx source_files errors_ret)
  set(errors 0)

  string(REPLACE ";" " " source_files "${source_files}")
  separate_arguments(source_files NATIVE_COMMAND "${source_files}")

  execute_process(
    WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}
    COMMAND ${CHECKSPDX_EXECUTABLE} -r docs/readme.rst ${source_files}
    OUTPUT_VARIABLE checkspdx_output
    RESULT_VARIABLE checkspdx_rc
    OUTPUT_STRIP_TRAILING_WHITESPACE
    )

  if(checkspdx_output)
    message(${checkspdx_output})
  endif()

  # checkspdx failed for this file. Collect no.of errors
  if(${checkspdx_rc} GREATER 0)
    checkspdx_get_stats("${checkspdx_output}" errors)
  endif()

  set(${errors_ret} ${errors} PARENT_SCOPE)
endfunction()

#
# Run checkspdx on entire codebase. This verifies all files in this repository
# except the files listed in "glob_excludes".
#
# Exits with FATAL_ERROR upon errors. Warnings are ignored (temporary)
#
if(CHECKSPDX_CODEBASE)
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
    message(STATUS "check-spdx-codebase: No files to check")
    return()
  endif()

  run_checkspdx("${source_files}" total_errors)
  print_stats_and_exit("checkspdx-codebase" ${total_errors})
endif()

#
# Check SPDX complaiance on pending commits.
#
# Exits with FATAL_ERROR upon errors.
#
if(CHECKSPDX_PATCH)
  if(GIT_NOT_FOUND OR NOT IS_DIRECTORY .git)
    message(FATAL_ERROR "Required dependencies Git not found")
  endif()

  # Get list of commits to check
  Git_Get_Pending_Commits(pending_commits)

  # Iterate throuth list of commit ids
  set(total_errors 0)
  foreach(commit IN LISTS pending_commits)
    message(STATUS "Checking commit: ${commit}")

    Git_Get_Files_In_Commit("${commit}" source_files)

    foreach(exclude IN LISTS glob_excludes)
      list(FILTER source_files EXCLUDE REGEX "${exclude}")
    endforeach()

    # run check if the list is not empty
    if(source_files)
      run_checkspdx("${source_files}" errors)
      MATH(EXPR total_errors "${total_errors}+${errors}")
    endif()
  endforeach()

  print_stats_and_exit("checkspdx-patch" ${total_errors})
endif()
