find_package(GoogleTest REQUIRED)

set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin/tests)

set(test_names
  bv
  bvdomain
  bvdomaingen
  bvnodecons
  bvnodeinv
  bvnodeiscons
  bvnodeisess
  bvnodeisinv
  bvnodeselpath
  ls
  aigmgr
)

foreach(test ${test_names})
  set(testbin testbzlals${test})
  add_executable (${testbin} test_${test}.cpp)
  gtest_add_tests(TARGET ${testbin})
  target_link_libraries(${testbin} bzlals)
  target_link_libraries(${testbin} GTest::GTest)
  target_link_libraries(${testbin} GTest::Main)
  set_target_properties(${testbin} PROPERTIES OUTPUT_NAME ${testbin})
  add_test(${test} ${CMAKE_BINARY_DIR}/bin/tests/${testbin})
endforeach()
