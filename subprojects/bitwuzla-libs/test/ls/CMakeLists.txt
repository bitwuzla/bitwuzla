macro(add_ls_unit_test test_name)
  add_executable(${test_name} ${test_name}.cpp)
  gtest_add_tests(TARGET ${test_name})
  target_link_libraries(${test_name} bzlals)
  target_link_libraries(${test_name} GTest::GTest)
  target_link_libraries(${test_name} GTest::Main)
  add_test(NAME ${test_name} COMMAND ${test_name})
endmacro()

set(test_ls_names
  test_bvdomain
  test_bvdomaingen
  test_bvnode
  test_bvnodecons
  test_bvnodeinv
  test_bvnodeiscons
  test_bvnodeisess
  test_bvnodeisinv
  test_bvnodeselpath
  test_ls
)

foreach(test ${test_ls_names})
  add_ls_unit_test(${test})
endforeach()
