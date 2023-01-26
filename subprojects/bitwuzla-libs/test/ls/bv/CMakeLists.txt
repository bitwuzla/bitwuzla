macro(add_ls_bv_unit_test test_name is_white)
  if((NOT ${is_white}) OR ENABLE_WHITEBOX_TESTS)
    add_executable(${test_name} ${test_name}.cpp)
    gtest_add_tests(TARGET ${test_name})
    target_link_libraries(${test_name} bzlals)
    target_link_libraries(${test_name} GTest::GTest)
    target_link_libraries(${test_name} GTest::Main)
    if(${is_white})
      target_compile_options(${test_name} PRIVATE -fno-access-control)
    endif()
    add_test(NAME ${test_name} COMMAND ${test_name})
  endif()
endmacro()

set(test_ls_bv_names
  test_bvdomain
  test_bvdomaingen
  test_bvnode
  test_bvnodecons
  test_bvnodeinv
  test_bvnodeiscons
  test_bvnodeisess
  test_bvnodeisinv
  test_bvnodeselpath
)

set(test_ls_bv_names_white
  test_lsbv
  test_lsbv_normalize
)

foreach(test ${test_ls_bv_names})
  add_ls_bv_unit_test(${test} FALSE)
endforeach()
foreach(test ${test_ls_bv_names_white})
  add_ls_bv_unit_test(${test} TRUE)
endforeach()
