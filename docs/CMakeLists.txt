#-------------------------------------------------------------------------------
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#
#
#-------------------------------------------------------------------------------

add_custom_target(docs)

find_package(Python3)
find_package(Sphinx)
find_package(Git)

set(SPHINXCFG_OUTPUT_PATH ${CMAKE_CURRENT_BINARY_DIR}/user_guide)

if (SPHINX_FOUND AND GIT_FOUND)

    file(GLOB_RECURSE SPHINXCFG_DOC_FILES ${CMAKE_CURRENT_SOURCE_DIR} *.rst conf.py)

    add_custom_command(OUTPUT "${SPHINXCFG_OUTPUT_PATH}/html/index.html"
        OUTPUT "${SPHINXCFG_OUTPUT_PATH}/html/"
        COMMAND "${SPHINX_EXECUTABLE}" -W -b html "${CMAKE_CURRENT_SOURCE_DIR}" "${SPHINXCFG_OUTPUT_PATH}/html"
        WORKING_DIRECTORY "${CMAKE_SOURCE_DIR}/docs"
        DEPENDS ${SPHINXCFG_DOC_FILES}
    )
    add_custom_target(rmm_docs_userguide_html
        DEPENDS "${SPHINXCFG_OUTPUT_PATH}/html/index.html"
        DEPENDS "${SPHINXCFG_OUTPUT_PATH}/html/"
    )
    add_dependencies(docs rmm_docs_userguide_html)
endif()
