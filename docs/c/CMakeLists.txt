###
# Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
#
# This file is part of Bitwuzla.
#
# Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
#
# See COPYING for more information on using this software.
##

find_package(Doxygen REQUIRED)
check_python_module(breathe)

set(DOXYFILE_IN ${CMAKE_CURRENT_SOURCE_DIR}/Doxyfile.in)
set(DOXYFILE_OUT ${CMAKE_CURRENT_BINARY_DIR}/Doxyfile)

set(DOXYGEN_INPUT_DIR ${PROJECT_SOURCE_DIR}/src/api/c)
set(DOXYGEN_OUTPUT_DIR ${CMAKE_CURRENT_BINARY_DIR}/doxygen)
set(DOXYGEN_INDEX_FILE ${DOXYGEN_OUTPUT_DIR}/xml/index.xml)

configure_file(Doxyfile.in Doxyfile @ONLY)

file(MAKE_DIRECTORY ${DOXYGEN_OUTPUT_DIR})

add_custom_command(OUTPUT ${DOXYGEN_INDEX_FILE}
                   DEPENDS ${PROJECT_SOURCE_DIR}/src/api/c/bitwuzla.h
                   COMMAND Doxygen::doxygen ${DOXYFILE_OUT}
                   WORKING_DIRECTORY ${DOXYGEN_BIN_DIR}
                   MAIN_DEPENDENCY ${DOXYFILE_OUT} ${DOXYFILE_IN}
                   COMMENT "Generating doxygen API docs")

add_custom_target(docs-doxygen ALL DEPENDS ${DOXYGEN_INDEX_FILE})

# tell parent scope where to find the output xml                                
set(DOXYGEN_XML_DIR "${DOXYGEN_OUTPUT_DIR}/xml" PARENT_SCOPE)
