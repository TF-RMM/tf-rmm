#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

#
# This script is called from main CMakeLists.txt to run banned API checks
# on C, header and AArch64 assembly source files.
#
find_package(Git REQUIRED)
find_package(Python3 REQUIRED)
find_program(CHECKBANNEDAPI_EXECUTABLE "checkbannedapi.py"
  PATHS ${CMAKE_SOURCE_DIR}
  PATH_SUFFIXES tools/checkbannedapi
  DOC "Path to checkbannedapi.py"
  )

list(APPEND CMAKE_MODULE_PATH "${CMAKE_SOURCE_DIR}/cmake/Modules")
include(GitUtils)

# List of directories and files to exclude from checking for target
list(APPEND glob_excludes "^.git")
list(APPEND glob_excludes "^out")
list(APPEND glob_excludes "^build")
list(APPEND glob_excludes "^ext")
list(APPEND glob_excludes "^tools")

# checkbannedapi_get_stats: Parse and returns number of errors and warnings
function(checkbannedapi_get_stats stats_arg errors_ret)
  string(FIND "${stats_arg}" "errors:" idx REVERSE)
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

# filter all files except *.c/*.h/*.S files
function(filter_source_files all_files source_files_ret)
  foreach(exclude IN LISTS glob_excludes)
    list(FILTER all_files EXCLUDE REGEX "${exclude}")
  endforeach()

  foreach(source_file ${all_files})
    if(NOT source_file MATCHES ".c$" AND
        NOT source_file MATCHES ".S$" AND
        NOT source_file MATCHES ".h$")
      list(REMOVE_ITEM all_files ${source_file})
    endif()
  endforeach()

  set(${source_files_ret} ${all_files} PARENT_SCOPE)
endfunction()

# Run checkbannedapi.py on the list of files.
function(run_checkbannedapi source_files errors_ret)
  set(errors 0)

  string(APPEND additional_arguments "" " --banned_apis tools/checkbannedapi/banned-apis.txt")
  string(APPEND additional_arguments " --ignore_files tools/checkbannedapi/ignore-banned-api.txt")
  string(REPLACE ";" " " source_files "${source_files}")
  separate_arguments(source_files NATIVE_COMMAND "${source_files}")
  separate_arguments(additional_arguments NATIVE_COMMAND "${additional_arguments}")

  execute_process(
    WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}
    COMMAND ${CHECKBANNEDAPI_EXECUTABLE} ${source_files} ${additional_arguments}
    OUTPUT_VARIABLE checkbannedapi_output
    RESULT_VARIABLE checkbannedapi_rc
    OUTPUT_STRIP_TRAILING_WHITESPACE
    )

  if(checkbannedapi_output)
    message(${checkbannedapi_output})
  endif()

  # checkbannedapi failed for this file. Collect no.of errors
  if(${checkbannedapi_rc} GREATER 0)
    checkbannedapi_get_stats("${checkbannedapi_output}" errors)
  endif()

  set(${errors_ret} ${errors} PARENT_SCOPE)
endfunction()

#
# Run checkbannedapi on entire codebase. This verifies all files in this
# repository in "GLOB_INCLUDES".
#
# Exits with FATAL_ERROR upon errors. Warnings are ignored (temporary)
#
if(CHECKBANNEDAPI_CODEBASE)
  set(source_files "")

  if (GIT_FOUND AND IS_DIRECTORY .git)
    Git_Get_All_Files(all_files)
  else()
    file(GLOB_RECURSE all_files RELATIVE ${CMAKE_SOURCE_DIR} "*")
  endif()

  filter_source_files("${all_files}" source_files)

  if(NOT source_files)
    message(STATUS "checkbannedapi-codebase: No files to check")
    return()
  endif()

  run_checkbannedapi("${source_files}" total_errors)
  print_stats_and_exit("checkbannedapi-codebase" ${total_errors})
endif()

#
# Run checkbannedapi on pending commits.
#
# Exits with FATAL_ERROR upon errors.
#
if(CHECKBANNEDAPI_PATCH)
  if(GIT_NOT_FOUND OR NOT IS_DIRECTORY .git)
    message(FATAL_ERROR "Required dependencies Git not found")
  endif()

  # Get list of commits to check
  Git_Get_Pending_Commits(pending_commits)

  # Iterate throuth list of commit ids
  set(total_errors 0)
  foreach(commit IN LISTS pending_commits)
    message(STATUS "Checking commit: ${commit}")

    Git_Get_Files_In_Commit("${commit}" files_in_commit)

    set(source_files "")
    filter_source_files("${files_in_commit}" source_files)

    if(source_files)
      run_checkbannedapi("${source_files}" errors)
      MATH(EXPR total_errors "${total_errors}+${errors}")
    endif()
  endforeach()

  print_stats_and_exit("checkbannedapi-patch" ${total_errors})
endif()
