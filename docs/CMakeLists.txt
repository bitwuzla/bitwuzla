###
# Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
#
# This file is part of Bitwuzla.
#
# Copyright (C) 2007-2021 by the authors listed in the AUTHORS file.
#
# See COPYING for more information on using this software.
##

find_package(Sphinx REQUIRED)

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
                  WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
                  COMMENT "Generating Sphinx API documentation")

if(PYTHON)
  add_dependencies(docs pybitwuzla)
endif()
