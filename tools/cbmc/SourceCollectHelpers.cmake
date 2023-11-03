#
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#

#
# Helper functions for collecting all the source files and include paths that
# are used in the RMM build
#

function(is_valid_target_name target_name output_variable)
  string(FIND ${target_name} "NOTFOUND" notfound_pos)
  string(FIND ${target_name} "::@" link_addr_pos)
  string(FIND ${target_name} "$<$<" gen_expr_pos)
  if((NOT ${notfound_pos} EQUAL "-1") OR
     (NOT ${link_addr_pos} EQUAL "-1") OR
     (NOT ${gen_expr_pos} EQUAL "-1"))
    set(${output_variable} FALSE PARENT_SCOPE)
  else()
    set(${output_variable} TRUE PARENT_SCOPE)
  endif()
endfunction()

function(normalise_property_value target_name output_variable)
  foreach(value_prefix "INSTALL_INTERFACE" "BUILD_INTERFACE" "LINK_ONLY")
    string(REGEX REPLACE "^.*${value_prefix}:([^>]+)>$" "\\1" target_name ${target_name})
  endforeach()
  set(${output_variable} ${target_name} PARENT_SCOPE)
endfunction()

function(collect_targets_recursively collected_targets new_target output_variable)
  normalise_property_value("${new_target}" new_target)

  if ("${new_target}" IN_LIST collected_targets)
    set("${output_variable}" "${collected_targets}" PARENT_SCOPE)
    return()
  endif()

  set(extended_target_list "${collected_targets}")
  list(APPEND extended_target_list "${new_target}")

  foreach(link_property "INTERFACE_LINK_LIBRARIES" "LINK_LIBRARIES")
    # workaround for cmake older than 3.19:
    # INTERFACE_LIBRARY targets may only have whitelisted properties. This is typically
    # property names starting with 'INTERFACE_'
    get_target_property(target_type ${new_target} TYPE)
    if(${target_type} STREQUAL "INTERFACE_LIBRARY")
      string(FIND "${link_property}" "INTERFACE_" interface_pos)
      if (NOT interface_pos EQUAL 0)
        continue()
      endif()
    endif()

    get_target_property(target_interface "${new_target}" "${link_property}")
    if(NOT "${target_interface}" STREQUAL "target_interface-NOTFOUND")
      foreach(target_lib ${target_interface})
        is_valid_target_name(${target_lib} valid_target_name)
        if (valid_target_name)
          collect_targets_recursively("${extended_target_list}" "${target_lib}" extended_target_list)
        endif()
      endforeach()
    endif()
  endforeach()

  set("${output_variable}" "${extended_target_list}" PARENT_SCOPE)
endfunction()

function(add_include_from_target target_name)
  foreach(include_property "INTERFACE_INCLUDE_DIRECTORIES" "INCLUDE_DIRECTORIES")
    # workaround for cmake older than 3.19:
    # INTERFACE_LIBRARY targets may only have whitelisted properties. This is typically
    # property names starting with 'INTERFACE_'
    get_target_property(target_type ${target_name} TYPE)
    if(${target_type} STREQUAL "INTERFACE_LIBRARY")
      string(FIND "${include_property}" "INTERFACE_" interface_pos)
      if (NOT interface_pos EQUAL 0)
        continue()
      endif()
    endif()

    get_target_property(target_includes_dir ${target_name} ${include_property})
    if(NOT "${target_includes_dir}" STREQUAL "target_includes_dir-NOTFOUND")
      foreach(target_includes_dir ${target_includes_dir})
        normalise_property_value(${target_includes_dir} target_includes_dir)
        list(APPEND rmm_implementation_includes "-I${target_includes_dir}")
      endforeach()
      set (rmm_implementation_includes ${rmm_implementation_includes} PARENT_SCOPE)
    endif()
  endforeach()
endfunction()

function(add_source_and_include_from_target target_name)
  add_include_from_target(${target_name} ${level})
  set (rmm_implementation_includes ${rmm_implementation_includes} PARENT_SCOPE)

  # workaround for cmake older than 3.19:
  # INTERFACE_LIBRARY targets may only have whitelisted properties. This is typically
  # property names starting with 'INTERFACE_'. So SOURCES.* is not allowed.
  get_target_property(target_type ${target_name} TYPE)
  if(${target_type} STREQUAL "INTERFACE_LIBRARY")
    return()
  endif()

  get_target_property(target_srcs ${target_name} SOURCES)
  get_target_property(target_srcs_dir ${target_name} SOURCE_DIR)
  if((NOT "${target_srcs}" STREQUAL "target_srcs-NOTFOUND") AND
     (NOT "${target_srcs_dir}" STREQUAL "target_srcs_dir-NOTFOUND"))
    foreach(target_src ${target_srcs})
      list(APPEND rmm_implementation_srcs "${target_srcs_dir}/${target_src}")
    endforeach()
    set (rmm_implementation_srcs ${rmm_implementation_srcs} PARENT_SCOPE)
  endif()
endfunction()

function(add_source_and_include_recursively target_name)
  collect_targets_recursively("" "${target_name}" rmm_target_list)

  foreach(target_lib ${rmm_target_list})
    add_source_and_include_from_target("${target_lib}")
  endforeach()

  set (rmm_implementation_srcs ${rmm_implementation_srcs} PARENT_SCOPE)
  set (rmm_implementation_includes ${rmm_implementation_includes} PARENT_SCOPE)
endfunction()
