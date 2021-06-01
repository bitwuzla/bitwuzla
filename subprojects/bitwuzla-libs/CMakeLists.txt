cmake_minimum_required(VERSION 3.9)

#-----------------------------------------------------------------------------#

project(bzla-ls)
set(VERSION "0.0")
string(TIMESTAMP TIME)

#-----------------------------------------------------------------------------#

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_MODULE_PATH ${PROJECT_SOURCE_DIR}/cmake)
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)
list(APPEND CMAKE_PREFIX_PATH "${PROJECT_SOURCE_DIR}/deps/install")

#-----------------------------------------------------------------------------#

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

#-----------------------------------------------------------------------------#

set(CMAKE_ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib)
set(CMAKE_LIBRARY_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib)
set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin)
message(STATUS "LIB directory is '${CMAKE_BINARY_DIR}/lib'")
message(STATUS "BIN directory is '${CMAKE_BINARY_DIR}/bin'")

#-----------------------------------------------------------------------------#

option3vl(ASAN       "Compile with ASAN support")
option3vl(UBSAN      "Compile with UBSan support")
option3vl(ASSERTIONS "Enable assertions")
option3vl(TESTING    "Enable unit tests")
option3vl(GCOV       "Compile with coverage support")
option3vl(GPROF      "Compile with profiling support")

#-----------------------------------------------------------------------------#

if(ASAN)
  # -fsanitize=address requires CMAKE_REQUIRED_FLAGS to be explicitely set,
  # otherwise the -fsanitize=address check will fail while linking.
  set(CMAKE_REQUIRED_FLAGS -fsanitize=address)
  add_required_c_cxx_flag("-fsanitize=address")
  unset(CMAKE_REQUIRED_FLAGS)
  add_check_c_cxx_flag("-fno-omit-frame-pointer")
  add_required_c_cxx_flag("-fsanitize-recover=address")
  set(BUILD_SHARED_LIBS ON)
endif()

if(UBSAN)
  add_required_c_cxx_flag("-fsanitize=undefined")
  set(BUILD_SHARED_LIBS ON)
endif()

#-----------------------------------------------------------------------------#

# Note: Do not set these flags the cmake way as we need them for generating
#       bzlalsconfig.h and they are else not yet added to CMAKE_C(XX)_FLAGS at
#       file generation time (configure_file).
# TODO bzlalsconfig.h is not generated yet
add_required_c_flag("-std=gnu99")
add_required_cxx_flag("-std=gnu++11")

add_check_c_cxx_flag("-W")
add_check_c_cxx_flag("-Wall")
add_check_c_cxx_flag("-Wextra")
add_check_c_cxx_flag("-Wredundant-decls")

foreach(flag ${FLAGS})
  add_required_c_cxx_flag("${flag}")
endforeach()

#-----------------------------------------------------------------------------#

set(build_types Debug Production)
if(NOT CMAKE_BUILD_TYPE)
    message(STATUS "No build type set, options are: ${build_types}")
    set(CMAKE_BUILD_TYPE Production CACHE STRING "Options are: ${build_types}" FORCE)
    # Provide drop down menu options in cmake-gui
    set_property(CACHE CMAKE_BUILD_TYPE PROPERTY STRINGS ${build_types})
endif()
message(STATUS "Building ${CMAKE_BUILD_TYPE} build")

if(CMAKE_BUILD_TYPE STREQUAL "Debug")
  add_required_c_cxx_flag("-g")
  add_check_c_cxx_flag("-g3")
  add_check_c_cxx_flag("-ggdb")
  set_option(ASSERTIONS ON)
  set_option(TESTING ON)
elseif(CMAKE_BUILD_TYPE STREQUAL "Production")
  add_check_c_cxx_flag("-O3")
  if(NOT ASSERTIONS)
    add_definitions("-DNDEBUG")
  endif()
endif()

#-----------------------------------------------------------------------------#
# Regression tests

if(TESTING)
  enable_testing()
endif()

#-----------------------------------------------------------------------------#

if(NOT BUILD_SHARED_LIBS)
  set(CMAKE_FIND_LIBRARY_SUFFIXES .a)
endif()

#-----------------------------------------------------------------------------#

if(GCOV)
  include(CodeCoverage)
  APPEND_COVERAGE_COMPILER_FLAGS()
  setup_target_for_coverage_lcov(
    NAME coverage
    EXECUTABLE ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/test
    DEPENDENCIES cbitwuzla-bin)
endif()

if(GPROF)
  add_required_c_cxx_flag("-pg")
endif()

#include(CheckSignals)
#if(HAVE_SIGNALS)
#  add_definitions("-DBZLALS_HAVE_SIGNALS")
#endif()

#-----------------------------------------------------------------------------#

find_package(GMP REQUIRED)
if(GMP_FOUND)
  add_definitions("-DBZLA_USE_GMP")
else()
  message(FATAL_ERROR "GMP not found")
endif()

#-----------------------------------------------------------------------------#
# Extract info from Git for bzlalsconfig.h
# TODO is not generated yet

#find_package(Git)
#
#set(GIT_DIRTY "")
#set(GIT_SHA1 "")
#set(GIT_BRANCH "")
#
#if(GIT_FOUND)
#  # Get current git branch, result is != 0 if this is not a git repository
#  execute_process(
#    COMMAND ${GIT_EXECUTABLE} -C ${PROJECT_SOURCE_DIR} rev-parse --abbrev-ref HEAD
#    RESULT_VARIABLE GIT_RESULT
#    OUTPUT_VARIABLE GIT_BRANCH
#    OUTPUT_STRIP_TRAILING_WHITESPACE
#    ERROR_QUIET
#  )
#  if("${GIT_RESULT}" STREQUAL "0")
#    set(GIT_BRANCH "${GIT_BRANCH}-")
#    # Extract sha1 of HEAD
#    execute_process(
#      COMMAND ${GIT_EXECUTABLE} -C ${PROJECT_SOURCE_DIR} rev-parse HEAD
#      OUTPUT_VARIABLE GIT_SHA1
#      OUTPUT_STRIP_TRAILING_WHITESPACE
#    )
#    # Result is != 0 if worktree is dirty
#    execute_process(
#      COMMAND ${GIT_EXECUTABLE} -C ${PROJECT_SOURCE_DIR} diff --quiet
#      RESULT_VARIABLE GIT_RESULT
#    )
#    if(NOT "${GIT_RESULT}" STREQUAL "0")
#      set(GIT_DIRTY "-dirty")
#    endif()
#  endif()
#endif()
#
#file(READ COPYING LICENSE NEWLINE_CONSUME)
#string(REGEX REPLACE "\n" "\\\\n" LICENSE "${LICENSE}")
#string(REGEX REPLACE "\"" "\\\\\"" LICENSE "${LICENSE}")
#
## TODO: definitions added via add_definititions
#configure_file(
#  ${CMAKE_CURRENT_SOURCE_DIR}/src/bzlalsconfig.h.in
#  ${CMAKE_CURRENT_BINARY_DIR}/src/bzlalsconfig.h)

#-----------------------------------------------------------------------------#
# Source directories

include_directories(src ${CMAKE_CURRENT_BINARY_DIR}/src)
add_subdirectory(src)
if (TESTING)
  add_subdirectory(test)
endif()

#-----------------------------------------------------------------------------#
# Install config and configversion for bzla-ls to add support for
# find_package(bzlals).

# TODO
#include(CMakePackageConfigHelpers)
#write_basic_package_version_file(
#  ${CMAKE_CURRENT_BINARY_DIR}/CBitwuzlaConfigVersion.cmake
#  VERSION ${VERSION}
#  COMPATIBILITY SameMajorVersion
#)
#
## Install the config, configversion and custom find modules
#install(FILES
#  ${CMAKE_CURRENT_LIST_DIR}/cmake/CBitwuzlaConfig.cmake
#  ${CMAKE_CURRENT_BINARY_DIR}/CBitwuzlaConfigVersion.cmake
#  DESTINATION lib/cmake/CBitwuzla
#)

#-----------------------------------------------------------------------------#
# Print bzla-ls configuration

if(NOT WIN32)
  string(ASCII 27 Esc)
  set(Green "${Esc}[32m")
  set(Blue "${Esc}[1;34m")
  set(ResetColor "${Esc}[m")
endif()

macro(config_info msg value)
  message(STATUS  "${Blue}${msg}: ${Green}${value}${ResetColor}")
endmacro()

macro(config_info_bool msg value)
  if(${value})
    config_info("${msg}" "yes")
  else()
    config_info("${msg}" "no")
  endif()
endmacro()

config_info("Build type" "${CMAKE_BUILD_TYPE}")
config_info_bool("Shared build" "${BUILD_SHARED_LIBS}")

config_info_bool("ASAN support" ASAN)
config_info_bool("UBSAN support" UBSAN)
config_info_bool("Assertions enabled" ASSERTIONS)
config_info_bool("Testing enabled" TESTING)
config_info_bool("gcov support" GCOV)
config_info_bool("gprof support" GPROF)
