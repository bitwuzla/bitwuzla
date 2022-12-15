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
  aigprop.c
  backtrack/assertion_stack.cpp
  backtrack/backtrackable.cpp
  bzlaaig.c
  bzlaaigvec.c
  bzlaass.c
  bzlabeta.c
  bzlabv.cpp
  bzlabvdomain.c
  bzlabvprop.c
  bzlaconsutils.c
  bzlacore.c
  bzladbg.c
  bzladcr.c
  bzlaessutils.c
  bzlaexp.c
  bzlainvutils.c
  bzlalsutils.c
  bzlamodel.c
  bzlamsg.c
  bzlanode.c
  bzlaopt.c
  bzlaparse.c
  bzlaprintmodel.c
  bzlaproputils.c
  bzlarewrite.c
  bzlarm.c
  bzlarwcache.c
  bzlasat.c
  bzlaslsutils.c
  bzlaslvaigprop.c
  bzlaslvfun.c
  bzlaslvprop.cpp
  bzlaslvpropold.c
  bzlaslvquant.cpp
  bzlaslvsls.c
  bzlasort.c
  bzlasubst.c
  bzlafp.cpp
  bzlasynthterm.cpp
  api/checks.cpp
  api/c/bitwuzla.cpp
  api/cpp/bitwuzla.cpp
  dumper/bzladumpaig.c
  dumper/bzladumpbtor.c
  dumper/bzladumpsmt.c
  env.cpp
  node/kind_info.cpp
  node/node.cpp
  node/node_data.cpp
  node/node_kind.cpp
  node/node_manager.cpp
  node/node_translation.cpp
  node/node_utils.cpp
  printer/printer.cpp
  type/type.cpp
  type/type_data.cpp
  type/type_manager.cpp
  util/statistics.cpp
  option/option.cpp
  parser/bzlabtor.c
  #parser/bzlabtor2.c
  parser/bzlasmt2.cpp
  preprocess/bzlaack.c
  preprocess/bzlader.c
  preprocess/bzlaelimapplies.c
  preprocess/bzlaelimites.c
  preprocess/bzlaelimslices.c
  preprocess/bzlaembed.c
  preprocess/bzlaextract.c
  preprocess/bzlamerge.c
  preprocess/bzlaminiscope.c
  preprocess/bzlanormadd.c
  preprocess/bzlanormquant.c
  preprocess/bzlapputils.c
  preprocess/bzlapreprocess.c
  preprocess/bzlaskel.c
  preprocess/bzlaskolemize.c
  preprocess/bzlaunconstrained.c
  preprocess/bzlavarsubst.c
  preprocess/pass/elim_lambda.cpp
  preprocess/pass/rewrite.cpp
  preprocess/pass/variable_substitution.cpp
  preprocess/pass/flatten_and.cpp
  preprocess/preprocessing_pass.cpp
  preprocess/preprocessor.cpp
  rewrite/rewrite_utils.cpp
  rewrite/rewriter.cpp
  rewrite/rewrites_bool.cpp
  rewrite/rewrites_core.cpp
  rewrite/rewrites_bv.cpp
  rewrite/rewrites_fp.cpp
  sat/bzlacadical.cpp
  sat/bzlacms.cpp
  sat/bzlalgl.c
  sat/bzlagimsatul.c
  sat/bzlakissat.cpp
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
  solver/fp/word_blaster_old.cpp
  solver/fp/word_blaster.cpp
  solver/fun/fun_solver.cpp
  solver/array/array_solver.cpp
  solver/result.cpp
  solver/solver.cpp
  solver/solver_engine.cpp
  solver/solver_state.cpp
  solving_context.cpp
  utils/bzlahashint.c
  utils/bzlahashptr.c
  utils/bzlamem.c
  utils/bzlanodeiter.c
  utils/bzlanodemap.c
  utils/bzlaoptparse.c
  utils/bzlapartgen.c
  utils/bzlarng.cpp
  utils/bzlaunionfind.c
  utils/bzlautil.c
  utils/bzlaabort.c
)

#set(bitwuzla_src_files
#  bitwuzlamain.c
#  bzlamain.c
#)

#-----------------------------------------------------------------------------#
# Bitwuzla library

add_library(bitwuzla ${libbitwuzla_src_files})
target_link_libraries(bitwuzla ${LIBRARIES})
target_include_directories(bitwuzla
  PUBLIC
    $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}>
    $<INSTALL_INTERFACE:include>)

target_include_directories(bitwuzla PRIVATE ${Btor2Tools_INCLUDE_DIR})
target_link_libraries(bitwuzla ${Btor2Tools_LIBRARIES})

target_include_directories(bitwuzla PRIVATE subprojects/bitwuzla-libs/src)
target_link_libraries(bitwuzla bzlabb bzlabv bzlals bzlarng)

if(GMP_FOUND)
  target_include_directories(bitwuzla PRIVATE ${GMP_INCLUDE_DIR})
  target_link_libraries(bitwuzla ${GMP_LIBRARIES})
endif()

if(Lingeling_FOUND)
  target_include_directories(bitwuzla PRIVATE ${Lingeling_INCLUDE_DIR})
  target_link_libraries(bitwuzla ${Lingeling_LIBRARIES})
endif()

if(CaDiCaL_FOUND)
  target_include_directories(bitwuzla PRIVATE ${CaDiCaL_INCLUDE_DIR})
  target_link_libraries(bitwuzla ${CaDiCaL_LIBRARIES})
endif()

if(CryptoMiniSat_FOUND)
  target_include_directories(bitwuzla PRIVATE ${CryptoMiniSat_INCLUDE_DIR})
  target_link_libraries(bitwuzla ${CryptoMiniSat_LIBRARIES})
endif()

if(Kissat_FOUND)
  target_include_directories(bitwuzla PRIVATE ${Kissat_INCLUDE_DIR})
  target_link_libraries(bitwuzla ${Kissat_LIBRARIES})
endif()

if(Gimsatul_FOUND)
  target_include_directories(bitwuzla PRIVATE ${Gimsatul_INCLUDE_DIR})
  target_link_libraries(bitwuzla ${Gimsatul_LIBRARIES})
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
install(FILES api/c/bitwuzla.h DESTINATION include/bitwuzla)

add_subdirectory(main)
