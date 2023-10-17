#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

#
# This script is called from main CMakeLists.txt to run clang-tidy checks. The
# checks are run on either the codebase (if variable CLANG-TIDY_CODEBASE is
# defined) or just new commits (if variable CLANG-TIDY_PATCH is defined).
#
# Enabled checks can be configured in the .clang-tidy file.
#
find_package(Git REQUIRED)
find_package(Python REQUIRED)
find_package(Python3 REQUIRED)

find_program(CLANGTIDY_EXECUTABLE "run-clang-tidy"
  DOC "Path to run-clang-tidy executable."
  )

if(NOT CLANGTIDY_EXECUTABLE)
  message(FATAL_ERROR "Could not find run-clang-tidy executable.")
endif()

list(APPEND CMAKE_MODULE_PATH "${CMAKE_SOURCE_DIR}/tools/common")
include(GitUtils)

#
# List of directories and files to exclude from checking for target
#
list(APPEND glob_excludes "^.git")
list(APPEND glob_excludes "^out")
list(APPEND glob_excludes "^build")
list(APPEND glob_excludes "^ext")
list(APPEND glob_excludes "^tools")
list(APPEND glob_excludes "^configs")
list(APPEND glob_excludes "^cmake")
list(APPEND glob_excludes "^docs")

#
# clang-tidy_get_stats: Parse output and return number of errors and warnings
#
function(clangtidy_get_stats stats_arg warnings_ret errors_ret)
  set(output_lines)
  string(REPLACE "\n" ";" output_lines "${stats_arg}")

  set(warnings 0)
  set(errors 0)

  #
  # Ideally we would match against the substring ": warning: ", and similarly
  # for errors.
  #
  # Unfortunately, the run-clang-tidy included with Clang 14.0.0 enables
  # colours in the output by default, and there is no way to change this in
  # the configuration. The use of colours in the output means the exact
  # substring ": warning: " is never present, due to the presence of escape
  # characters.
  #
  # In addition, the presence of escape characters presents difficulties in
  # splitting the output into lines. This is why REGEX MATCHALL is used
  # instead of FIND.
  #
  foreach(output_line IN LISTS output_lines)
    set(warnings_list)

    string(REGEX MATCHALL "warning: " warnings_list "${output_line}")
    list(LENGTH warnings_list warnings_count)
    MATH(EXPR warnings "${warnings} + ${warnings_count}")

    set(errors_list)

    string(REGEX MATCHALL "error: " errors_list "${output_line}")
    list(LENGTH errors_list errors_count)
    MATH(EXPR errors "${errors} + ${errors_count}")
  endforeach()

  set(${warnings_ret} ${warnings} PARENT_SCOPE)
  set(${errors_ret} ${errors} PARENT_SCOPE)
endfunction()

#
# print_stats_and_exit: Print summary of all errors and warnings.
# If there are errors call message(FATAL_ERROR)
#
function(print_stats_and_exit check_type total_warnings total_errors)
  message(STATUS "${check_type}: total warnings: ${total_warnings}, total errors: ${total_errors}")

  if(${total_errors} GREATER 0)
    message(FATAL_ERROR "${check_type}: FAILED")
  endif()

  message(STATUS "${check_type}: PASSED")
endfunction()

#
# filter_source_files: Filter all files except *.c/*.h files
#
function(filter_source_files all_files source_files_ret)
  foreach(exclude IN LISTS glob_excludes)
    list(FILTER all_files EXCLUDE REGEX "${exclude}")
  endforeach()

  foreach(source_file ${all_files})
    if(NOT source_file MATCHES ".c$" AND
        NOT source_file MATCHES ".h$")
      list(REMOVE_ITEM all_files ${source_file})
    endif()
  endforeach()

  set(${source_files_ret} ${all_files} PARENT_SCOPE)
endfunction()

#
# run_clangtidy: Run clang-tidy on the list of files.
#
function(run_clangtidy source_files warnings_ret errors_ret)
  set(total_warnings 0)
  set(total_errors 0)

  string(REPLACE ";" " " source_files "${source_files}")
  separate_arguments(source_files NATIVE_COMMAND "${source_files}")

  foreach(source_file ${source_files})
    message("Checking file ${source_file}")

    #
    # Run clang-tidy on each file, one at a time. Note that although this loop
    # iterates through all files in the codebase, only files used for the
    # specified configuration will actually be checked.
    #
    # We pass the compile commands database (in the build folder), which
    # records the compile options used in the build, to clang-tidy.
    #
    # -quiet flag is required to prevent clang-tidy from printing the enabled
    # checks for every file!
    #
    # We discard the standard error output, which is simply a line stating "X
    # warnings generated". This number X includes warnings from system headers,
    # which are not displayed. Instead, we manually count the number of
    # warnings and errors generated from the relevant files.
    #
    execute_process(
      WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}
      COMMAND ${CLANGTIDY_EXECUTABLE}
        -p ${BUILD_DIR}
        -quiet
        ${source_file}
        OUTPUT_VARIABLE clang-tidy_output
        ERROR_QUIET
        )

    if(clang-tidy_output)
      message(${clang-tidy_output})
    endif()

    # Update total counts for warnings and errors
    clangtidy_get_stats("${clang-tidy_output}" warnings errors)
    MATH(EXPR total_warnings "${total_warnings} + ${warnings}")
    MATH(EXPR total_errors "${total_errors} + ${errors}")
  endforeach()

  set(${warnings_ret} ${total_warnings} PARENT_SCOPE)
  set(${errors_ret} ${total_errors} PARENT_SCOPE)
endfunction()

#
# Run clang-tidy on entire codebase. This verifies all files in this
# repository in "GLOB_INCLUDES".
#
# Exits with FATAL_ERROR upon errors.
#
if(CLANG-TIDY_CODEBASE)
  set(compile_commands
    "${BUILD_DIR}/compile_commands.json")

  if(NOT EXISTS "${compile_commands}")
    message(FATAL_ERROR
      "clang-tidy requires a compile command database. Use flag "
      "`-DCMAKE_EXPORT_COMPILE_COMMANDS=ON` during configuration.")
  endif()

  if(NOT "${RMM_TOOLCHAIN}" STREQUAL "llvm")
    message(FATAL_ERROR
      "clang-tidy can be used only if the project is built using the LLVM "
      "toolchain. Use flag `DRMM_TOOLCHAIN=llvm` during configuration.")
  endif()

  set(source_files "")

  if (GIT_FOUND AND IS_DIRECTORY .git)
    Git_Get_All_Files(all_files)
  else()
    file(GLOB_RECURSE all_files RELATIVE ${CMAKE_SOURCE_DIR} "*")
  endif()

  filter_source_files("${all_files}" source_files)

  if(NOT source_files)
    message(STATUS "clang-tidy-codebase: No files to check")
    return()
  endif()

  run_clangtidy("${source_files}" total_warnings total_errors)
  print_stats_and_exit("clang-tidy-codebase" ${total_warnings} ${total_errors})
endif()

#
# Run clang-tidy on pending commits.
#
# Exits with FATAL_ERROR upon errors.
#
if(CLANG-TIDY_PATCH)
  set(compile_commands
    "${BUILD_DIR}/compile_commands.json")

  if(NOT EXISTS "${compile_commands}")
    message(FATAL_ERROR
      "clang-tidy requires a compile command database. Use flag "
      "`-DCMAKE_EXPORT_COMPILE_COMMANDS=ON` during configuration.")
  endif()

  if(NOT "${RMM_TOOLCHAIN}" STREQUAL "llvm")
    message(FATAL_ERROR
      "clang-tidy can be used only if the project is built using the LLVM "
      "toolchain. Use flag `DRMM_TOOLCHAIN=llvm` during configuration.")
  endif()

  if(GIT_NOT_FOUND OR NOT IS_DIRECTORY .git)
    message(FATAL_ERROR "Required dependencies Git not found")
  endif()

  #
  # Get list of commits to check
  #
  Git_Get_Pending_Commits(pending_commits)

  #
  # Iterate through list of commit ids
  #
  set(total_warnings 0)
  set(total_errors 0)

  foreach(commit IN LISTS pending_commits)
    message(STATUS "Checking commit: ${commit}")

    Git_Get_Files_In_Commit("${commit}" files_in_commit)

    set(source_files "")
    filter_source_files("${files_in_commit}" source_files)

    if(source_files)
      run_clangtidy("${source_files}" warnings errors)
      MATH(EXPR total_warnings "${total_warnings} + ${warnings}")
      MATH(EXPR total_errors "${total_errors} + ${errors}")
    endif()
  endforeach()

  print_stats_and_exit("clang-tidy-patch" ${total_warnings} ${total_errors})
endif()
