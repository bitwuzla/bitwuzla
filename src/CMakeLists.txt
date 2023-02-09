###
# Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
#
# This file is part of Bitwuzla.
#
# Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
#
# See COPYING for more information on using this software.
##

set(libbitwuzla_src_files
  backtrack/assertion_stack.cpp
  backtrack/backtrackable.cpp
  bzlaparse.c
  api/checks.cpp
  api/c/bitwuzla.cpp
  api/cpp/bitwuzla.cpp
  env.cpp
  node/kind_info.cpp
  node/node.cpp
  node/node_data.cpp
  node/node_kind.cpp
  node/node_manager.cpp
  node/node_utils.cpp
  printer/printer.cpp
  type/type.cpp
  type/type_data.cpp
  type/type_manager.cpp
  util/statistics.cpp
  util/logger.cpp
  option/option.cpp
  parser/bzlabtor.cpp
  parser/bzlasmt2.cpp
  preprocess/pass/contradicting_ands.cpp
  preprocess/pass/elim_extract.cpp
  preprocess/pass/elim_lambda.cpp
  preprocess/pass/elim_uninterpreted.cpp
  preprocess/pass/embedded_constraints.cpp
  preprocess/pass/flatten_and.cpp
  preprocess/pass/normalize.cpp
  preprocess/pass/rewrite.cpp
  preprocess/pass/rewrite.cpp
  preprocess/pass/skeleton_preproc.cpp
  preprocess/pass/variable_substitution.cpp
  preprocess/preprocessing_pass.cpp
  preprocess/preprocessor.cpp
  rewrite/rewrite_utils.cpp
  rewrite/rewriter.cpp
  rewrite/rewrites_array.cpp
  rewrite/rewrites_bool.cpp
  rewrite/rewrites_core.cpp
  rewrite/rewrites_bv.cpp
  rewrite/rewrites_bv_norm.cpp
  rewrite/rewrites_fp.cpp
  sat/cadical.cpp
  sat/cryptominisat.cpp
  sat/kissat.cpp
  solver/bv/bv_solver.cpp
  solver/bv/bv_bitblast_solver.cpp
  solver/bv/bv_prop_solver.cpp
  solver/fp/floating_point.cpp
  solver/fp/fp_solver.cpp
  solver/fp/rounding_mode.cpp
  solver/fp/symfpu_wrapper.cpp
  solver/fp/word_blaster.cpp
  solver/fun/fun_solver.cpp
  solver/array/array_solver.cpp
  solver/quant/quant_solver.cpp
  solver/result.cpp
  solver/solver.cpp
  solver/solver_engine.cpp
  solver/solver_state.cpp
  solving_context.cpp
)

#set(bitwuzla_src_files
#  bitwuzlamain.c
#  bzlamain.c
#)

#-----------------------------------------------------------------------------#
# Bitwuzla library

add_library(bitwuzla ${libbitwuzla_src_files})
target_link_libraries(bitwuzla PRIVATE ${LIBRARIES})
target_include_directories(bitwuzla
  PUBLIC
    $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}>
    $<INSTALL_INTERFACE:include>)

target_include_directories(bitwuzla PRIVATE subprojects/bitwuzla-libs/src)
target_link_libraries(bitwuzla PRIVATE bzlabb bzlabv bzlals bzlarng)

if(GMP_FOUND)
  target_include_directories(bitwuzla PRIVATE ${GMP_INCLUDE_DIR})
  target_link_libraries(bitwuzla PRIVATE ${GMP_LIBRARIES})
endif()

if(Lingeling_FOUND)
  target_include_directories(bitwuzla PRIVATE ${Lingeling_INCLUDE_DIR})
  target_link_libraries(bitwuzla PRIVATE ${Lingeling_LIBRARIES})
endif()

if(CaDiCaL_FOUND)
  target_include_directories(bitwuzla PRIVATE ${CaDiCaL_INCLUDE_DIR})
  target_link_libraries(bitwuzla PRIVATE ${CaDiCaL_LIBRARIES})
endif()

if(CryptoMiniSat_FOUND)
  target_include_directories(bitwuzla PRIVATE ${CryptoMiniSat_INCLUDE_DIR})
  target_link_libraries(bitwuzla PRIVATE ${CryptoMiniSat_LIBRARIES})
endif()

if(Kissat_FOUND)
  target_include_directories(bitwuzla PRIVATE ${Kissat_INCLUDE_DIR})
  target_link_libraries(bitwuzla PRIVATE ${Kissat_LIBRARIES})
endif()

if(Gimsatul_FOUND)
  target_include_directories(bitwuzla PRIVATE ${Gimsatul_INCLUDE_DIR})
  target_link_libraries(bitwuzla PRIVATE ${Gimsatul_LIBRARIES})
endif()

if(SymFPU_FOUND)
  target_include_directories(bitwuzla SYSTEM PRIVATE ${SymFPU_INCLUDE_DIR})
endif()

install(TARGETS bitwuzla
  EXPORT bitwuzla-export
  LIBRARY DESTINATION lib
  ARCHIVE DESTINATION lib
)

install(EXPORT bitwuzla-export
  FILE BitwuzlaTargets.cmake
  NAMESPACE Bitwuzla::
  DESTINATION lib/cmake/Bitwuzla)

# Install header files
install(FILES api/c/bitwuzla.h DESTINATION include/bitwuzla/api/c)
install(FILES api/cpp/bitwuzla.h DESTINATION include/bitwuzla/api/cpp)

add_subdirectory(main)
