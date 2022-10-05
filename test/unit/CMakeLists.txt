find_package(GoogleTest REQUIRED)

set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin/tests)

set(test_names
  #aig
  #aigvec
  #arithmetic
  #bv
  #bvdomain
  #bvdomaingen
  #bvprop
  #comp
  #constbits
  #essutils
  #exp
  #hash
  #inc
  #inthash
  #inthashmap
  #invutils
  #lambda
  #logic
  #mem
  #misc
  #modelgen
  #modelgensmt2
  #nodemap
  #overflow
  #prop
  #propold
  #propoldcomplete
  #propoldcons
  #propoldinv
  #rotate
  #queue
  satmgr
  #shift
  #smtaxioms
  #sort
  #stack
  #unionfind
  #util
)

if(SymFPU_FOUND)
  list(APPEND test_names api fp)
endif()

macro(_add_unit_test test_name is_white)
  if((NOT ${is_white}) OR ENABLE_WHITEBOX_TESTS)
    add_executable(${test_name} ${test_name}.cpp)
    gtest_add_tests(TARGET ${test_name})
    target_link_libraries(${test_name} bitwuzla m)
    target_link_libraries(${test_name} GTest::gtest_main)
    if(${is_white})
      target_compile_options(${test_name} PRIVATE -fno-access-control)
    endif()
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

include_directories(${CMAKE_CURRENT_SOURCE_DIR})
add_subdirectory(backtrack)
add_subdirectory(node)
add_subdirectory(option)
add_subdirectory(printer)
add_subdirectory(rewrite)
add_subdirectory(solver)
add_subdirectory(type)
