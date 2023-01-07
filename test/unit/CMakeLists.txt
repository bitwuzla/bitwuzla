find_package(GoogleTest REQUIRED)

set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin/tests)

set(test_names
  #arithmetic
  #bv
  #bvprop
  #comp
  #lambda
  #misc
  #modelgen
  #modelgensmt2
  #prop
  #propold
  #propoldcomplete
  #propoldcons
  #propoldinv
  #shift
)

macro(_add_unit_test test_name is_white)
  if((NOT ${is_white}) OR ENABLE_WHITEBOX_TESTS)
    add_executable(${test_name} ${test_name}.cpp)
    gtest_add_tests(TARGET ${test_name})
    target_link_libraries(${test_name} bitwuzla m)
    target_link_libraries(${test_name} GTest::gtest_main)
    target_include_directories(${test_name} PRIVATE ${PROJECT_SOURCE_DIR})
    if(${is_white})
      target_compile_options(${test_name} PRIVATE -fno-access-control)
    endif()
    file(RELATIVE_PATH dir ${PROJECT_SOURCE_DIR}/test ${CMAKE_CURRENT_LIST_DIR})
    set(test_bin_dir ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/${dir})
    set_target_properties(${test_name}
      PROPERTIES RUNTIME_OUTPUT_DIRECTORY ${test_bin_dir})
    add_test(NAME ${test_name} COMMAND ${test_name})
  endif()
endmacro()

macro(add_unit_test test_name)
  _add_unit_test(${test_name} FALSE)
endmacro()

macro(add_whitebox_unit_test test_name)
  _add_unit_test(${test_name} TRUE)
endmacro()

foreach(test ${test_names})
  add_unit_test(test_${test})
endforeach()

add_subdirectory(api)
add_subdirectory(backtrack)
add_subdirectory(node)
add_subdirectory(option)
add_subdirectory(preprocess)
add_subdirectory(printer)
add_subdirectory(rewrite)
add_subdirectory(solver)
add_subdirectory(type)
