#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

#
# This script is called from main CMakeLists.txt to determine if header files
# included are in proper order
#
find_package(Git REQUIRED)
find_package(Python3 REQUIRED)
find_program(CHECKINCLUDES_EXECUTABLE "checkincludes.py"
  PATHS ${CMAKE_SOURCE_DIR}
  PATH_SUFFIXES tools/checkincludes
  DOC "Path to checkincludes.py"
  )

list(APPEND CMAKE_MODULE_PATH "${CMAKE_SOURCE_DIR}/tools/common")
include(GitUtils)

# List of directories and files to exclude from checking for target
list(APPEND glob_excludes "^.git")
list(APPEND glob_excludes "^out")
list(APPEND glob_excludes "^build")
list(APPEND glob_excludes "^ext")
list(APPEND glob_excludes "^tools")

# checkincludes_get_stats: Parse and returns number of errors and warnings
function(checkincludes_get_stats stats_arg errors_ret)
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

# Run checkincludes.py on the list of files.
function(run_checkincludes source_files errors_ret)
  set(errors 0)

  string(REPLACE ";" " " source_files "${source_files}")
  separate_arguments(source_files NATIVE_COMMAND "${source_files}")

  execute_process(
    WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}
    COMMAND ${CHECKINCLUDES_EXECUTABLE} ${source_files}
    OUTPUT_VARIABLE checkincludes_output
    RESULT_VARIABLE checkincludes_rc
    OUTPUT_STRIP_TRAILING_WHITESPACE
    )

  if(checkincludes_output)
    message(${checkincludes_output})
  endif()

  # checkincludes failed for this file. Collect no.of errors
  if(${checkincludes_rc} GREATER 0)
    checkincludes_get_stats("${checkincludes_output}" errors)
  endif()

  set(${errors_ret} ${errors} PARENT_SCOPE)
endfunction()

#
# Run checkincludes on entire codebase. This verifies all files in this
# repository in "GLOB_INCLUDES".
#
# Exits with FATAL_ERROR upon errors. Warnings are ignored (temporary)
#
if(CHECKINCLUDES_CODEBASE)
  set(source_files "")

  if (GIT_FOUND AND IS_DIRECTORY .git)
    Git_Get_All_Files(all_files)
  else()
    file(GLOB_RECURSE all_files RELATIVE ${CMAKE_SOURCE_DIR} "*")
  endif()

  filter_source_files("${all_files}" source_files)

  if(NOT source_files)
    message(STATUS "checkincludes-codebase: No files to check")
    return()
  endif()

  run_checkincludes("${source_files}" total_errors)
  print_stats_and_exit("checkincludes-codebase" ${total_errors})
endif()

#
# Check header files include order on pending commits.
#
# Exits with FATAL_ERROR upon errors.
#
if(CHECKINCLUDES_PATCH)
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
      run_checkincludes("${source_files}" errors)
      MATH(EXPR total_errors "${total_errors}+${errors}")
    endif()
  endforeach()

  print_stats_and_exit("checkincludes-patch" ${total_errors})
endif()
