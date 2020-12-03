set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin/tests)

set(test_names
  #bitvector
)

foreach(test ${test_names})
  add_executable (test${test} test_${test}.cpp)
  gtest_add_tests(TARGET ${test})
  target_link_libraries(test${test} bzlals)
  target_link_libraries(${test} GTest::GTest)
  target_link_libraries(${test} GTest::Main)
  set_target_properties(test${test} PROPERTIES OUTPUT_NAME test${test})
  add_test(${test} ${CMAKE_BINARY_DIR}/bin/tests/test${test})
endforeach()
