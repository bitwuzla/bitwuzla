set(test_ls_names
  test_bvnodecons
  test_bvnodeinv
  test_bvnodeiscons
  test_bvnodeisess
  test_bvnodeisinv
  test_bvnodeselpath
  test_ls
)

foreach(test ${test_ls_names})
  add_unit_test(${test})
endforeach()
