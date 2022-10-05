macro(add_bb_unit_test test_name)
  add_executable(${test_name} ${test_name}.cpp)
  gtest_add_tests(TARGET ${test_name})
  target_link_libraries(${test_name} bzlabb)
  target_link_libraries(${test_name} GTest::GTest)
  target_link_libraries(${test_name} GTest::Main)
  add_test(NAME ${test_name} COMMAND ${test_name})
endmacro()

set(test_bb_names
  test_aig_bitblaster
  test_aig_manager
  test_aig_cnf
)

foreach(test ${test_bb_names})
  add_bb_unit_test(${test})
endforeach()
