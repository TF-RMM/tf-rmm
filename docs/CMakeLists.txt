#-------------------------------------------------------------------------------
# SPDX-License-Identifier: BSD-3-Clause
# SPDX-FileCopyrightText: Copyright TF-RMM Contributors.
#
#
#-------------------------------------------------------------------------------

add_custom_target(docs)

find_package(Python3)
find_package(Sphinx)
find_package(PythonModules COMPONENTS sphinx-rtd-theme sphinxcontrib.plantuml)
find_package(PlantUML)

set(SPHINXCFG_OUTPUT_PATH ${CMAKE_CURRENT_BINARY_DIR}/user_guide)

configure_file(${CMAKE_CURRENT_SOURCE_DIR}/conf.py.in ${CMAKE_CURRENT_BINARY_DIR}/conf.py @ONLY)

if (SPHINX_FOUND AND PLANTUML_FOUND AND PY_SPHINX-RTD-THEME_FOUND AND PY_SPHINXCONTRIB.PLANTUML)

    file(GLOB_RECURSE SPHINXCFG_DOC_FILES ${CMAKE_CURRENT_SOURCE_DIR} *.rst)

    add_custom_command(OUTPUT "${SPHINXCFG_OUTPUT_PATH}/html/index.html"
        OUTPUT "${SPHINXCFG_OUTPUT_PATH}/html/"
        COMMAND "${SPHINX_EXECUTABLE}" -W -b html "${CMAKE_CURRENT_SOURCE_DIR}" "${SPHINXCFG_OUTPUT_PATH}/html" -c ${CMAKE_CURRENT_BINARY_DIR}
        WORKING_DIRECTORY "${CMAKE_SOURCE_DIR}"
        DEPENDS ${SPHINXCFG_DOC_FILES}
    )
    add_custom_target(rmm_docs_userguide_html
        DEPENDS "${SPHINXCFG_OUTPUT_PATH}/html/index.html"
        DEPENDS "${SPHINXCFG_OUTPUT_PATH}/html/"
    )
    add_dependencies(docs rmm_docs_userguide_html)
endif()
