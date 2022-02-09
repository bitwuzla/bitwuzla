###
# Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
#
# This file is part of Bitwuzla.
#
# Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
#
# See COPYING for more information on using this software.
##

find_package(PythonExtensions REQUIRED)
find_package(Cython REQUIRED)

include_directories(${PYTHON_INCLUDE_DIRS})
include_directories(${CMAKE_CURRENT_LIST_DIR})               # bitwuzla_api.pxd
include_directories(${CMAKE_CURRENT_LIST_DIR}/../c/)         # bitwuzla.h
include_directories(${CMAKE_CURRENT_BINARY_DIR})

set(generated_file "${CMAKE_CURRENT_BINARY_DIR}/pybitwuzla_enums.pxd")

# Generate pybitwuzla_enums.pxd from bitwuzla.h
add_custom_command(
  COMMAND
    "${PYTHON_EXECUTABLE}"
    "${CMAKE_CURRENT_LIST_DIR}/mkenums.py"
    "${CMAKE_CURRENT_LIST_DIR}/../c/bitwuzla.h"
    "${generated_file}"
  OUTPUT
    "${generated_file}"
  DEPENDS
    "${CMAKE_CURRENT_LIST_DIR}/mkenums.py"
    "${CMAKE_CURRENT_LIST_DIR}/../c/bitwuzla.h"
  COMMENT
    "Generate pybitwuzla_enums.pxd"
)

add_custom_target(
    pybitwuzla_enums
    DEPENDS
      "${generated_file}"
      "${CMAKE_CURRENT_LIST_DIR}/mkenums.py"
      "${CMAKE_CURRENT_LIST_DIR}/../c/bitwuzla.h"
)
add_cython_target(pybitwuzla CXX)  # implicitely uses pybitwuzla.pyx

add_library(pybitwuzla
            MODULE
            ${pybitwuzla} pybitwuzla_utils.c pybitwuzla_abort.cpp)
add_dependencies(pybitwuzla pybitwuzla_enums)

target_link_libraries(pybitwuzla bitwuzla ${PYTHON_LIBRARIES})

if(IS_WINDOWS_BUILD)
  target_link_libraries(pybitwuzla -static gcc stdc++ winpthread -dynamic)
endif()

# Suppress warnings for code generted by Cython.
set_target_properties(
  pybitwuzla PROPERTIES COMPILE_FLAGS "-Wno-redundant-decls")

python_extension_module(pybitwuzla)
install(TARGETS pybitwuzla DESTINATION lib)
