###
# Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
#
# This file is part of Bitwuzla.
#
# Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
#
# See COPYING for more information on using this software.
##

find_package(PythonInterp 3 REQUIRED)

# Check if pytest module is installed.
execute_process(
  COMMAND
    ${PYTHON_EXECUTABLE} -c "import pytest"
  RESULT_VARIABLE
    MODULE_NOT_FOUND
  ERROR_QUIET
)

macro(add_python_test_case name filename)
  add_test(
    NAME python/${name}
    COMMAND
      ${PYTHON_EXECUTABLE} -m pytest ${CMAKE_CURRENT_SOURCE_DIR}/${filename}
  )
set_tests_properties(python/${name}
  PROPERTIES
    ENVIRONMENT
      "PYTHONPATH=${CMAKE_BINARY_DIR}/lib")
endmacro()

if(MODULE_NOT_FOUND)
  message(WARNING "Could not find pytest module. Disabling Python tests.")
else()
  add_python_test_case(api test_api.py)
endif()
