###
# Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
#
# This file is part of Bitwuzla.
#
# Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
#
# See COPYING for more information on using this software.
##

find_package(Sphinx REQUIRED)
check_python_module(sphinxcontrib.bibtex sphinxcontrib-bibtex)

add_subdirectory(c)

configure_file(conf.py.in conf.py)

set(SPHINX_INPUT_DIR ${CMAKE_CURRENT_SOURCE_DIR})
set(SPHINX_OUTPUT_DIR ${CMAKE_CURRENT_BINARY_DIR}/sphinx)

add_custom_target(docs ALL
                  DEPENDS docs-doxygen
                  COMMAND
                    ${SPHINX_EXECUTABLE} -b html
                    # Tell Breathe where to find the Doxygen output
                    -Dbreathe_projects.Bitwuzla=${DOXYGEN_XML_DIR}
                    # Tell Sphinx where to find conf.py
                    -c ${CMAKE_CURRENT_BINARY_DIR}
                    ${SPHINX_INPUT_DIR}
                    ${SPHINX_OUTPUT_DIR}
                  # Remove unwanted header
                  COMMAND sed -i'orig' 's/<p class="breathe-sectiondef-title rubric" id="breathe-section-title-functions">Functions<\\/p>//' ${SPHINX_OUTPUT_DIR}/c/interface.html
                  COMMAND find ${SPHINX_OUTPUT_DIR} -name '*orig' -delete
                  WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}
                  COMMENT "Generating Sphinx API documentation")

if(PYTHON)
  add_dependencies(docs pybitwuzla)
endif()

set(SPHINX_GH_OUTPUT_DIR ${CMAKE_CURRENT_BINARY_DIR}/sphinx-gh)
add_custom_target(docs-gh ALL
                  DEPENDS docs
                  COMMAND ${CMAKE_COMMAND} -E remove_directory
                    ${SPHINX_GH_OUTPUT_DIR}
                  COMMAND ${CMAKE_COMMAND} -E copy_directory
                    ${SPHINX_OUTPUT_DIR} ${SPHINX_GH_OUTPUT_DIR}
                  COMMAND ${CMAKE_COMMAND} -E remove_directory
                    ${SPHINX_GH_OUTPUT_DIR}/_sources
                  COMMAND ${CMAKE_COMMAND} -E remove
                    ${SPHINX_GH_OUTPUT_DIR}/objects.inv
                  COMMAND ${CMAKE_COMMAND} -E rename
                    ${SPHINX_GH_OUTPUT_DIR}/_static
                    ${SPHINX_GH_OUTPUT_DIR}/static
                  COMMAND find ${SPHINX_GH_OUTPUT_DIR} -type f |
                    xargs sed -i'orig' 's/_static/static/'
                  COMMAND find ${SPHINX_GH_OUTPUT_DIR} -name '*orig' -delete
                  COMMENT "Generating GitHub Api docs")
