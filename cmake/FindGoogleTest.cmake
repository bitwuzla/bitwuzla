# Find GTest
#
# GTest_FOUND - Found GTest
# GTest::GTest - GTest library

find_package(GTest 1.10.0)

if(NOT GTest_FOUND)
  include(ExternalProject)

  set(GTest_VERSION "1.10.0")

  ExternalProject_Add(
    GTest-EP
    PREFIX "${CMAKE_BINARY_DIR}/deps"
    URL https://github.com/google/googletest/archive/refs/tags/release-${GTest_VERSION}.tar.gz
    URL_HASH SHA1=9c89be7df9c5e8cb0bc20b3c4b39bf7e82686770
    DOWNLOAD_NAME gtest.tar.gz
    CMAKE_ARGS
      -DCMAKE_INSTALL_PREFIX=<INSTALL_DIR>
    BUILD_COMMAND ${CMAKE_COMMAND} --build .
    BUILD_BYPRODUCTS
        <INSTALL_DIR>/lib/libgtest.a
        <INSTALL_DIR>/lib/libgtest_main.a
    LOG_DOWNLOAD ON
    LOG_UPDATE ON
    LOG_CONFIGURE ON
    LOG_BUILD ON
    LOG_INSTALL ON
    LOG_OUTPUT_ON_FAILURE TRUE
  )

  set(GTest_INCLUDE_DIR "${CMAKE_BINARY_DIR}/deps/include/")
  set(GTest_MAIN_LIBRARY "${CMAKE_BINARY_DIR}/deps/lib/libgtest_main.a")
  set(GTest_LIBRARY "${CMAKE_BINARY_DIR}/deps/lib/libgtest.a")
  file(MAKE_DIRECTORY "${GTest_INCLUDE_DIR}")

  add_library(GTest::gtest_main STATIC IMPORTED GLOBAL)
  set_target_properties(GTest::gtest_main
    PROPERTIES
      IMPORTED_LOCATION "${GTest_MAIN_LIBRARY}"
      INTERFACE_INCLUDE_DIRECTORIES "${GTest_INCLUDE_DIR}"
      INTERFACE_LINK_LIBRARIES "${GTest_LIBRARY}"
  )
  set(GTest_FOUND TRUE)
  add_dependencies(GTest::gtest_main GTest-EP)
  message(STATUS "Building GTest ${GTest_VERSION}: ${GTest_MAIN_LIBRARY}")

  mark_as_advanced(GTest_FOUND)
  mark_as_advanced(GTest_INCLUDE_DIR)
  mark_as_advanced(GTest_LIBRARIES)
endif()
