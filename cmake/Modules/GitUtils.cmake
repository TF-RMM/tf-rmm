#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

#
# Returns:
# @FileList_Out:        All files in the Git repo in list format. Empty list
#                       on error
#
function(Git_Get_All_Files FileList_Out)
  if (GIT_NOT_FOUND OR NOT IS_DIRECTORY .git)
    set(${FileList_Out} "" PARENT_SCOPE)
    return()
  endif()

  execute_process(
    WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}
    COMMAND ${GIT_EXECUTABLE} ls-files
    OUTPUT_VARIABLE git_ls_files
    RESULT_VARIABLE git_rc
    OUTPUT_STRIP_TRAILING_WHITESPACE
    )

  # convert string to list
  if(NOT "${git_ls_files}" STREQUAL "")
    string(REPLACE "\n" ";" all_files ${git_ls_files})
  else()
    set(all_files "")
  endif()

  set(${FileList_Out} ${all_files} PARENT_SCOPE)
endfunction()

#
# Returns:
# @CommitIdList_Out:    All commit ids in current branch between HEAD and
#                       upstream tracking branch in List format. Empty list
#                       on error
#
function(Git_Get_Pending_Commits CommitIdList_Out)
  if (GIT_NOT_FOUND OR NOT IS_DIRECTORY .git)
    set(${CommitIdList_Out} "" PARENT_SCOPE)
    return()
  endif()

  # Get the upstream branch the current (local) branch is tracking
  execute_process(
    WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}
    COMMAND ${GIT_EXECUTABLE} rev-parse --abbrev-ref --symbolic-full-name @{u}
    OUTPUT_VARIABLE git_upstream_branch
    RESULT_VARIABLE git_rc
    OUTPUT_STRIP_TRAILING_WHITESPACE
    )

  if ("${git_upstream_branch}" STREQUAL "")
    message(STATUS "Warning: Upstream branch not set. Trying \"origin/main\"")
    set(git_upstream_branch "origin/main")
  endif()

  # Get the merge base
  execute_process(
    WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}
    COMMAND ${GIT_EXECUTABLE} merge-base HEAD ${git_upstream_branch}
    OUTPUT_VARIABLE git_merge_base
    RESULT_VARIABLE git_rc
    OUTPUT_STRIP_TRAILING_WHITESPACE
    )

  if("${git_merge_base}" STREQUAL "")
    set(${CommitIdList_Out} "" PARENT_SCOPE)
    return()
  endif()

  # Get list of commits between $merge_base and HEAD
  execute_process(
    WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}
    COMMAND ${GIT_EXECUTABLE} rev-list --no-merges "${git_merge_base}..HEAD"
    OUTPUT_VARIABLE git_rev_output
    RESULT_VARIABLE git_rc
    OUTPUT_STRIP_TRAILING_WHITESPACE
    )

  # convert to list
  if(NOT "${git_rev_output}" STREQUAL "")
    string(REPLACE "\n" ";" git_rev_list ${git_rev_output})
  else()
    set(git_rev_list "")
  endif()

  set(${CommitIdList_Out} ${git_rev_list} PARENT_SCOPE)
endfunction()

#
# Args In:
# @CommitId_In:         Commit's SHA
#
# Returns:
# @FileList_Out:        Files Added or Modified or Deleted by the @CommitId_In
#                       in list format. Empty list on error
#
function(Git_Get_Files_In_Commit CommitId_In FileList_Out)
  if (GIT_NOT_FOUND OR NOT IS_DIRECTORY .git OR "${CommitId_In}" STREQUAL "")
    set(${FileList_Out} "" PARENT_SCOPE)
    return()
  endif()

  execute_process(
    WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}
    # Get list of files that are Added or Renamed or Modified by this commit
    COMMAND ${GIT_EXECUTABLE} show --diff-filter=ARM --pretty=format: --name-only ${CommitId_In}
    OUTPUT_VARIABLE git_files
    RESULT_VARIABLE git_rc
    OUTPUT_STRIP_TRAILING_WHITESPACE
    )

  # convert string to list
  if(NOT "${git_files}" STREQUAL "")
    string(REPLACE "\n" ";" source_files ${git_files})
  else()
    set(source_files "")
  endif()

  set(${FileList_Out} ${source_files} PARENT_SCOPE)
endfunction()

#
# Apply patches in @Git_Repo
#
# Args In:
# @Git_Repo:            Git repository
# @Patch_Files_List:    List of .patch files to apply
#
function(Git_Apply_Patches Git_Repo Patch_Files_List)
  # use EXISTS as inside submodule .git file contains path to Git repository
  if(GIT_NOT_FOUND OR NOT EXISTS "${Git_Repo}/.git")
    message(FATAL_ERROR "${Git_Repo} not a git repository")
    return()
  endif()

  # todo: Remove 'checkout' and 'clean' commands.
  # These commands does a force reset and removes untracked files. If an user
  # has some work in progress changes in 'Git_Repo', then Git_Apply_Patches will
  # force delete the changes.
  execute_process(
    WORKING_DIRECTORY ${Git_Repo}
    # removes changes that are not staged
    COMMAND ${GIT_EXECUTABLE} checkout .
    )
  execute_process(
    WORKING_DIRECTORY ${Git_Repo}
    # removes changes that are not tracked
    COMMAND ${GIT_EXECUTABLE} clean -f
    )

  # todo: For applying patches use -am option, this retains commit history.
  foreach(PATCH_FILE IN LISTS Patch_Files_List)
    execute_process(
      WORKING_DIRECTORY ${Git_Repo}
      COMMAND ${GIT_EXECUTABLE} apply --verbose ${PATCH_FILE}
      RESULT_VARIABLE PATCH_STATUS
      COMMAND_ECHO STDOUT
      )

    if(NOT PATCH_STATUS EQUAL 0)
      message(FATAL_ERROR "Failed to apply patch ${PATCH_FILE} at ${Git_Repo}")
    endif()
  endforeach()
endfunction()
