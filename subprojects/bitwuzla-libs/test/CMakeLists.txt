find_package(GoogleTest REQUIRED)

set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin/tests)

macro(add_unit_test test_name)
  add_executable(${test_name} ${test_name}.cpp)
  gtest_add_tests(TARGET ${test_name})
  target_link_libraries(${test_name} bzlabv)
  target_link_libraries(${test_name} GTest::GTest)
  target_link_libraries(${test_name} GTest::Main)
  add_test(NAME ${test_name} COMMAND ${test_name})
endmacro()

set(test_names
  test_bv
)

foreach(test ${test_names})
  add_unit_test(${test})
endforeach()

include_directories(${CMAKE_CURRENT_SOURCE_DIR})
add_subdirectory(bitblast)
add_subdirectory(ls)
