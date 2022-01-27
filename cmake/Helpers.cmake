###
# Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
#
# This file is part of Bitwuzla.
#
# Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
#
# See COPYING for more information on using this software.
##

include(CheckCCompilerFlag)
include(CheckCXXCompilerFlag)

macro(add_c_flag flag)
  set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} ${flag}")
  message(STATUS "Configuring with C flag '${flag}'")
endmacro()

macro(add_cxx_flag flag)
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${flag}")
  message(STATUS "Configuring with CXX flag '${flag}'")
endmacro()

macro(add_c_cxx_flag flag)
  add_c_flag(${flag})
  add_cxx_flag(${flag})
endmacro()

macro(add_check_c_flag flag)
  string(REGEX REPLACE "[-=]" "_" flagname ${flag})
  check_c_compiler_flag("${flag}" HAVE_FLAG${flagname})
  if(HAVE_FLAG${flagname})
    add_c_flag(${flag})
  endif()
endmacro()

macro(add_check_cxx_flag flag)
  string(REGEX REPLACE "[-=]" "_" flagname ${flag})
  check_cxx_compiler_flag("${flag}" HAVE_FLAG${flagname})
  if(HAVE_FLAG${flagname})
    add_cxx_flag(${flag})
  endif()
endmacro()

macro(add_check_c_cxx_flag flag)
  add_check_c_flag(${flag})
  add_check_cxx_flag(${flag})
endmacro()

macro(add_required_cxx_flag flag)
  string(REGEX REPLACE "[-=]" "_" flagnamename ${flag})
  check_cxx_compiler_flag("${flag}" HAVE_FLAG${flagname})
  if (NOT HAVE_FLAG${flagname})
    message(FATAL_ERROR "Required compiler flag ${flag} not supported")
  endif()
  add_cxx_flag(${flag})
endmacro()

macro(add_required_c_flag flag)
  string(REGEX REPLACE "[-=]" "_" flagname ${flag})
  check_c_compiler_flag("${flag}" HAVE_FLAG${flagname})
  if (NOT HAVE_FLAG${flagname})
    message(FATAL_ERROR "Required compiler flag ${flag} not supported")
  endif()
  add_c_flag(${flag})
endmacro()

macro(add_required_c_cxx_flag flag)
  add_required_c_flag(${flag})
  add_required_cxx_flag(${flag})
endmacro()

# 3-valued option IGNORE/OFF/ON
macro(option3vl var description)
  set(${var} IGNORE CACHE STRING "${description}")
  # Provide drop down menu options in cmake-gui
  set_property(CACHE ${var} PROPERTY STRINGS IGNORE ON OFF)
endmacro()

# Set option only if it still has initial value IGNORE (do not overwrite user
# configurations)
macro(set_option var value)
  if(${var} STREQUAL "IGNORE")
    set(${var} ${value})
  endif()
endmacro()

# Check if given Python module is installed and raises a FATAL_ERROR error
# if the module cannot be found.
function(check_python_module module)
  find_package(PythonInterp 3 REQUIRED)
  execute_process(
    COMMAND
    ${PYTHON_EXECUTABLE} -c "import ${module}"
    RESULT_VARIABLE
      RET_MODULE_TEST
    ERROR_QUIET
  )
  set(module_name ${ARGN})
  if(NOT module_name)
    set(module_name ${module})
  endif()

  if(RET_MODULE_TEST)
    message(FATAL_ERROR
        "Could not find module ${module_name} for Python "
        "version ${PYTHON_VERSION_MAJOR}.${PYTHON_VERSION_MINOR}. "
        "Make sure to install ${module_name} for this Python version "
        "via \n`${PYTHON_EXECUTABLE} -m pip install ${module_name}'.\n"
        "Note: You need to have pip installed for this Python version.")
  endif()
endfunction()

#-----------------------------------------------------------------------------#
