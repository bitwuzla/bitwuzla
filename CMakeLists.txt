cmake_minimum_required(VERSION 3.3)

#-----------------------------------------------------------------------------#

project(bitwuzla)
set(VERSION "0.1-202011")
string(TIMESTAMP TIME)

#-----------------------------------------------------------------------------#

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
option3vl(CHECK      "Enable assertions even for optimized compilation")
option3vl(GCOV       "Compile with coverage support")
option3vl(GPROF      "Compile with profiling support")
option3vl(LOG        "Compile with logging support (default for Debug builds)")
#option3vl(PYTHON     "Build Python API")
option3vl(TIME_STATS "Compile with time statistics")

option3vl(USE_CADICAL    "Use and link with CaDiCaL")
option3vl(USE_CMS        "Use and link with CryptoMiniSat")
option3vl(USE_LINGELING  "Use and link with Lingeling (default)")
option3vl(USE_MINISAT    "Use and link with MiniSat")
option3vl(USE_PICOSAT    "Use and link with PicoSAT")
option3vl(USE_KISSAT     "Use and link with Kissat")
option3vl(USE_SYMFPU     "Use and link with SymFPU")

option(ONLY_CADICAL   "Only use CaDiCaL" OFF)
option(ONLY_CMS       "Only use CryptoMiniSat" OFF)
option(ONLY_LINGELING "Only use Lingeling" OFF)
option(ONLY_MINISAT   "Only use MiniSat" OFF)
option(ONLY_PICOSAT   "Only use PicoSAT" OFF)
option(ONLY_KISSAT    "Only use Kissat" OFF)
#option(USE_PYTHON2    "Prefer Python 2.7" )
#option(USE_PYTHON3    "Prefer Python 3" )
option(USE_GMP        "Use GMP for bit-vector implementation" OFF)

#-----------------------------------------------------------------------------#

# Automatically build shared libraries if Python bindings are enabled.
# Disabled until migrated to new API
#if(PYTHON)
#  if(USE_PYTHON2)
#    find_package(PythonInterp 2.7 REQUIRED)
#  elseif(USE_PYTHON3)
#    find_package(PythonInterp 3 REQUIRED)
#  else()
#    find_package(PythonInterp REQUIRED)
#  endif()
#  # Explicitly check for a compatible version of Python libs.
#  find_package(PythonLibs
#    ${PYTHON_VERSION_MAJOR}.${PYTHON_VERSION_MINOR}.${PYTHON_VERSION_PATCH}
#    REQUIRED)
#
#  # Produce a python module that only links against system libraries. SAT
#  # solvers and libbitwuzla should be included in the module itself.
#  if(NOT BUILD_SHARED_LIBS)
#    add_check_c_cxx_flag("-fPIC")
#    # Disable MiniSat since the static library is not compiled with -fPIC by
#    # default.
#    message(STATUS "Disabling MiniSat for static Python builds. "
#                   "Use --shared if you need MiniSat.")
#    set_option(USE_MINISAT OFF)
#  endif()
#endif()

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

if(NOT BUILD_SHARED_LIBS)
  set(CMAKE_FIND_LIBRARY_SUFFIXES .a)
endif()

#-----------------------------------------------------------------------------#
# Default values for 3-valued options

set_option(USE_CADICAL ON)
set_option(USE_CMS ON)
set_option(USE_LINGELING ON)
set_option(USE_MINISAT ON)
set_option(USE_PICOSAT ON)
set_option(USE_KISSAT ON)
set_option(USE_SYMFPU OFF)

#-----------------------------------------------------------------------------#

# Note: Do not set these flags the cmake way as we need them for generating
#       bzlaconfig.h and they are else not yet added to CMAKE_C(XX)_FLAGS at
#       file generation time (configure_file).
add_required_c_flag("-std=gnu99")
add_required_cxx_flag("-std=gnu++11")

add_check_c_cxx_flag("-W")
add_check_c_cxx_flag("-Wall")
add_check_c_cxx_flag("-Wextra")
add_check_c_cxx_flag("-Wredundant-decls")

foreach(flag ${FLAGS})
  add_required_c_cxx_flag("${flag}")
endforeach()

if(IS_WINDOWS_BUILD)
  add_definitions("-DBZLA_WINDOWS_BUILD")
endif()

#-----------------------------------------------------------------------------#

set(build_types Debug Release)
if(NOT CMAKE_BUILD_TYPE)
    message(STATUS "No build type set, options are: ${build_types}")
    set(CMAKE_BUILD_TYPE Release CACHE STRING "Options are: ${build_types}" FORCE)
    # Provide drop down menu options in cmake-gui
    set_property(CACHE CMAKE_BUILD_TYPE PROPERTY STRINGS ${build_types})
endif()
message(STATUS "Building ${CMAKE_BUILD_TYPE} build")

if(CMAKE_BUILD_TYPE STREQUAL "Debug")
  add_required_c_cxx_flag("-g")
  add_check_c_cxx_flag("-g3")
  add_check_c_cxx_flag("-ggdb")
  set_option(LOG ON)
  set_option(TIME_STATS ON)
elseif(CMAKE_BUILD_TYPE STREQUAL "Release")
  add_check_c_cxx_flag("-O3")
  if(NOT CHECK)
    add_definitions("-DNDEBUG")
  endif()
  set_option(LOG OFF)
  set_option(TIME_STATS OFF)
endif()

#-----------------------------------------------------------------------------#

if(GCOV)
  include(CodeCoverage)
  APPEND_COVERAGE_COMPILER_FLAGS()
  setup_target_for_coverage_lcov(
    NAME coverage
    EXECUTABLE ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/test
    DEPENDENCIES bitwuzla-bin)
endif()

if(GPROF)
  add_required_c_cxx_flag("-pg")
endif()

if(NOT LOG)
  add_definitions("-DNBZLALOG")
endif()

include(CheckSignals)
if(HAVE_SIGNALS)
  add_definitions("-DBZLA_HAVE_SIGNALS")
endif()

include(CheckTimeUtils)
if(NOT HAVE_TIME_UTILS)
  set(TIME_STATS OFF)
endif()

if(TIME_STATS)
  add_definitions("-DBZLA_TIME_STATISTICS")
endif()

include(CheckNoExportDynamic)

#-----------------------------------------------------------------------------#

if(ONLY_CADICAL)
  set(USE_CMS OFF)
  set(USE_LINGELING OFF)
  set(USE_MINISAT OFF)
  set(USE_PICOSAT OFF)
  set(USE_KISSAT OFF)
  set(USE_CADICAL ON)
elseif(ONLY_CMS)
  set(USE_CADICAL OFF)
  set(USE_LINGELING OFF)
  set(USE_MINISAT OFF)
  set(USE_PICOSAT OFF)
  set(USE_KISSAT OFF)
  set(USE_CMS ON)
elseif(ONLY_LINGELING)
  set(USE_CADICAL OFF)
  set(USE_CMS OFF)
  set(USE_MINISAT OFF)
  set(USE_PICOSAT OFF)
  set(USE_KISSAT OFF)
  set(USE_LINGELING ON)
elseif(ONLY_MINISAT)
  set(USE_CADICAL OFF)
  set(USE_CMS OFF)
  set(USE_LINGELING OFF)
  set(USE_PICOSAT OFF)
  set(USE_KISSAT OFF)
  set(USE_MINISAT ON)
elseif(ONLY_PICOSAT)
  set(USE_CADICAL OFF)
  set(USE_CMS OFF)
  set(USE_LINGELING OFF)
  set(USE_MINISAT OFF)
  set(USE_KISSAT OFF)
  set(USE_PICOSAT ON)
endif()

#-----------------------------------------------------------------------------#

find_package(Btor2Tools REQUIRED)

if(NOT IS_WINDOWS_BUILD)
  set(THREADS_PREFER_PTHREAD_FLAG ON)
  find_package(Threads)
  if(Threads_FOUND)
    set(LIBRARIES ${LIBRARIES} ${CMAKE_THREAD_LIBS_INIT})
    add_definitions("-DBZLA_HAVE_PTHREADS")
  endif()
endif()

if(USE_GMP)
  find_package(GMP)
  if(GMP_FOUND)
    add_definitions("-DBZLA_USE_GMP")
  else()
    message(FATAL_ERROR "GMP not found")
  endif()
endif()

if(USE_SYMFPU)
  find_package(SymFPU)
endif()
if(SymFPU_FOUND)
  if(NOT SymFPU_INCLUDE_DIR)
    message(FATAL_ERROR "SymFPU headers not found")
  else()
    add_definitions("-DBZLA_USE_SYMFPU")
  endif()
elseif(GIVEN_SymFPU_ROOT_DIR)
  message(FATAL_ERROR "SymFPU not found")
endif()

if(USE_LINGELING)
  find_package(Lingeling)
endif()
if(USE_CADICAL)
  find_package(CaDiCaL)
endif()
if(USE_CMS)
  find_package(CryptoMiniSat)
endif()
if(USE_PICOSAT)
  find_package(PicoSAT)
endif()
if(USE_KISSAT)
  find_package(Kissat)
endif()
if(USE_MINISAT)
  find_package(MiniSat)
endif()

if(NOT USE_LINGELING
   AND NOT USE_CADICAL
   AND NOT USE_CMS
   AND NOT USE_PICOSAT
   AND NOT USE_KISSAT
   AND NOT USE_MINISAT)
  message(FATAL_ERROR "No SAT solver configured")
elseif(NOT Lingeling_FOUND
       AND NOT CaDiCaL_FOUND
       AND NOT CryptoMiniSat_FOUND
       AND NOT PicoSAT_FOUND
       AND NOT MiniSat_FOUND)
  message(FATAL_ERROR "No SAT solver found")
endif()

if(Lingeling_FOUND)
  if(NOT Lingeling_INCLUDE_DIR)
    message(FATAL_ERROR "Lingeling headers not found")
  else()
    add_definitions("-DBZLA_USE_LINGELING")
  endif()
endif()

if(CaDiCaL_FOUND)
  if(NOT CaDiCaL_INCLUDE_DIR)
    message(FATAL_ERROR "CaDiCaL headers not found")
  else()
    add_definitions("-DBZLA_USE_CADICAL")
  endif()
endif()

if(CryptoMiniSat_FOUND)
  if(NOT CryptoMiniSat_INCLUDE_DIR)
    message(FATAL_ERROR "CryptoMiniSat headers not found")
  else()
    add_definitions("-DBZLA_USE_CMS")
  endif()
endif()

if(PicoSAT_FOUND)
  if(NOT PicoSAT_INCLUDE_DIR)
    message(FATAL_ERROR "PicoSAT headers not found")
  else()
    add_definitions("-DBZLA_USE_PICOSAT")
  endif()
endif()

if(Kissat_FOUND)
  if(NOT Kissat_INCLUDE_DIR)
    message(FATAL_ERROR "Kissat headers not found")
  else()
    add_definitions("-DBZLA_USE_KISSAT")
  endif()
endif()

if(MiniSat_FOUND)
  if(NOT MiniSat_INCLUDE_DIR)
    message(FATAL_ERROR "MiniSAT headers not found")
  else()
    add_definitions("-DBZLA_USE_MINISAT")
  endif()
endif()

#-----------------------------------------------------------------------------#
# Extract info from Git for bzlaconfig.h

find_package(Git)

set(GIT_DIRTY "")
set(GIT_SHA1 "")
set(GIT_BRANCH "")

if(GIT_FOUND)
  # Get current git branch, result is != 0 if this is not a git repository
  execute_process(
    COMMAND ${GIT_EXECUTABLE} -C ${PROJECT_SOURCE_DIR} rev-parse --abbrev-ref HEAD
    RESULT_VARIABLE GIT_RESULT
    OUTPUT_VARIABLE GIT_BRANCH
    OUTPUT_STRIP_TRAILING_WHITESPACE
    ERROR_QUIET
  )
  if("${GIT_RESULT}" STREQUAL "0")
    set(GIT_BRANCH "${GIT_BRANCH}-")
    # Extract sha1 of HEAD
    execute_process(
      COMMAND ${GIT_EXECUTABLE} -C ${PROJECT_SOURCE_DIR} rev-parse HEAD
      OUTPUT_VARIABLE GIT_SHA1
      OUTPUT_STRIP_TRAILING_WHITESPACE
    )
    # Result is != 0 if worktree is dirty
    execute_process(
      COMMAND ${GIT_EXECUTABLE} -C ${PROJECT_SOURCE_DIR} diff --quiet
      RESULT_VARIABLE GIT_RESULT
    )
    if(NOT "${GIT_RESULT}" STREQUAL "0")
      set(GIT_DIRTY "-dirty")
    endif()
  endif()
endif()

file(READ COPYING LICENSE NEWLINE_CONSUME)
string(REGEX REPLACE "\n" "\\\\n" LICENSE "${LICENSE}")
string(REGEX REPLACE "\"" "\\\\\"" LICENSE "${LICENSE}")

# TODO: definitions added via add_definititions
configure_file(
  ${CMAKE_CURRENT_SOURCE_DIR}/src/bzlaconfig.h.in
  ${CMAKE_CURRENT_BINARY_DIR}/src/bzlaconfig.h)

#-----------------------------------------------------------------------------#
# Regression tests

# Get and configure google test
include(cmake/googletest.cmake)
fetch_googletest(
    ${PROJECT_SOURCE_DIR}/cmake
    ${PROJECT_BINARY_DIR}/googletest
    )

enable_testing()

#-----------------------------------------------------------------------------#
# Source directories

include_directories(src ${CMAKE_CURRENT_BINARY_DIR}/src)
add_subdirectory(src)
add_subdirectory(test)
# Disabled until migrated to new API
#if(PYTHON)
#  add_subdirectory(src/api/python)
#endif()
# Disabled until migrated to new API
# add_subdirectory(examples/api/c)

#-----------------------------------------------------------------------------#

set(ARCHIVE_NAME "bitwuzla-${VERSION}")
add_custom_target(dist
    COMMAND git archive --prefix=${ARCHIVE_NAME}/ HEAD
        | xz > ${CMAKE_BINARY_DIR}/${ARCHIVE_NAME}.tar.xz
    WORKING_DIRECTORY ${CMAKE_SOURCE_DIR})

#-----------------------------------------------------------------------------#
# Install config and configversion for Bitwuzla to add support for
# find_package(Bitwuzla).

include(CMakePackageConfigHelpers)
write_basic_package_version_file(
  ${CMAKE_CURRENT_BINARY_DIR}/BitwuzlaConfigVersion.cmake
  VERSION ${VERSION}
  COMPATIBILITY SameMajorVersion
)

# Install the config, configversion and custom find modules
install(FILES
  ${CMAKE_CURRENT_LIST_DIR}/cmake/BitwuzlaConfig.cmake
  ${CMAKE_CURRENT_BINARY_DIR}/BitwuzlaConfigVersion.cmake
  DESTINATION lib/cmake/Bitwuzla
)

#-----------------------------------------------------------------------------#
# Print Bitwuzla configuration

if(NOT WIN32)
  string(ASCII 27 Esc)
  set(Green "${Esc}[32m")
  set(Blue "${Esc}[34m")
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
config_info_bool("Assertions enabled" CHECK)
config_info_bool("gcov support" GCOV)
config_info_bool("gprof support" GPROF)
config_info_bool("Logging support" LOG)
#config_info_bool("Python bindings" PYTHON)
config_info_bool("Time statistics" TIME_STATS)
config_info_bool("CaDiCaL" CaDiCaL_FOUND)
config_info_bool("CryptoMiniSat" CryptoMiniSat_FOUND)
config_info_bool("Lingeling" Lingeling_FOUND)
config_info_bool("MiniSat" MiniSat_FOUND)
config_info_bool("PicoSAT" PicoSAT_FOUND)
config_info_bool("Kissat" Kissat_FOUND)
config_info_bool("GMP" USE_GMP)
config_info_bool("SymFPU" SymFPU_FOUND)
