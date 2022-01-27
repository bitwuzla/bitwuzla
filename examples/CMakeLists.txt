###
# Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
#
# This file is part of Bitwuzla.
#
# Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
#
# See COPYING for more information on using this software.
##

cmake_minimum_required(VERSION 3.4)

project(bitwuzla-examples)

enable_testing()

# Find Bitwuzla package. If Bitwuzla is not installed into the default system
# location use `cmake .. -DCMAKE_PREFIX_PATH=path/to/lib/cmake` to specify the
# location of BitwuzlaConfig.cmake.
find_package(Bitwuzla)

set(EXAMPLES_BIN_DIR ${CMAKE_BINARY_DIR}/bin)

# Add example target and create test to run example with ctest.
#
# > name: The name of the example
# > src_files: The list of source files passed as string "src1 src2 ..."
#              (alternative: "src1;src2;...").  If empty, <name>.cpp is assumed.
# > output_dir: Determines the examples subdirectory and is empty (passed as
#               empty string) for the examples root directory (this)
# > file_ext:  The extension of the example source file.
# > ARGN: Any additional arguments passed to the macro are interpreted as
#         as arguments to the test executable.
#
# The build target is created without the path prefix (not supported),
# e.g., for '<output_dir>/myexample.cpp'
#   we create build target 'myexample'
#   and build it with 'make myexample'.
# As a consequence, all build target names must be globally unique.
macro(bzla_add_example name src_files output_dir file_ext)
  if("${src_files}" STREQUAL "")
    set(src_files_list ${name}.${file_ext})
  else()
    string(REPLACE " " ";" src_files_list "${src_files}")
  endif()

  add_executable(${name} ${src_files_list})
  target_link_libraries(${name} Bitwuzla::bitwuzla)

  # The test target is prefixed with the path,
  # e.g., for '<output_dir>/myexample.cpp'
  #   we create test target '<output_dir>/myexample'
  #   and run it with 'ctest -R "<output_dir>/myexample"'.
  set(example_bin_dir ${EXAMPLES_BIN_DIR}/${output_dir})
  if("${output_dir}" STREQUAL "")
    set(example_test ${name})
  else()
    set(example_test ${output_dir}/${name})
  endif()
  set_target_properties(${name}
    PROPERTIES RUNTIME_OUTPUT_DIRECTORY ${example_bin_dir})
  add_test(${example_test} ${example_bin_dir}/${name} ${ARGN})
endmacro()

add_subdirectory(c)
