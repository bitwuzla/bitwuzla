set(libboolector_src_files
  aigprop.c
  boolector.c
  bzlaabort.c
  bzlaaig.c
  bzlaaigvec.c
  bzlaass.c
  bzlabeta.c
  bzlabv.c
  bzlabvprop.c
  bzlachkclone.c
  bzlachkmodel.c
  bzlachkfailed.c
  bzlaclone.c
  bzlacore.c
  bzladbg.c
  bzladcr.c
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
  bzlarwcache.c
  bzlasat.c
  bzlaslsutils.c
  bzlaslvaigprop.c
  bzlaslvfun.c
  bzlaslvprop.c
  bzlaslvquant.c
  bzlaslvsls.c
  bzlasort.c
  bzlasubst.c
  bzlasynth.c
  bzlatrapi.c
  dumper/bzladumpaig.c
  dumper/bzladumpbtor.c
  dumper/bzladumpsmt.c
  parser/bzlabtor.c
  parser/bzlabtor2.c
  parser/bzlasmt.c
  parser/bzlasmt2.c
  preprocess/bzlapputils.c
  preprocess/bzlaack.c
  preprocess/bzlader.c
  preprocess/bzlaelimapplies.c
  preprocess/bzlaelimslices.c
  preprocess/bzlaembed.c
  preprocess/bzlaextract.c
  preprocess/bzlamerge.c
  preprocess/bzlaminiscope.c
  preprocess/bzlanormadd.c
  preprocess/bzlanormquant.c
  preprocess/bzlapreprocess.c
  preprocess/bzlaskel.c
  preprocess/bzlaskolemize.c
  preprocess/bzlaunconstrained.c
  preprocess/bzlavarsubst.c
  sat/bzlacadical.c
  sat/bzlacms.cpp
  sat/bzlalgl.c
  sat/bzlaminisat.cpp
  sat/bzlapicosat.c
  sat/bzlakissat.c
  utils/bzlaaigmap.c
  utils/bzlahashint.c
  utils/bzlahashptr.c
  utils/bzlamem.c
  utils/bzlanodeiter.c
  utils/bzlanodemap.c
  utils/bzlaoptparse.c
  utils/bzlapartgen.c
  utils/bzlarng.c
  utils/bzlaunionfind.c
  utils/bzlautil.c
)

set(boolector_src_files
  boolectormain.c
  bzlamain.c
)

#-----------------------------------------------------------------------------#
# boolector library

add_library(boolector ${libboolector_src_files})
target_link_libraries(boolector ${LIBRARIES})
target_include_directories(boolector
  PUBLIC
    $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}>
    $<INSTALL_INTERFACE:include>)

target_include_directories(boolector PRIVATE ${Btor2Tools_INCLUDE_DIR})
target_link_libraries(boolector ${Btor2Tools_LIBRARIES})

if(GMP_FOUND)
  target_include_directories(boolector PRIVATE ${GMP_INCLUDE_DIR})
  target_link_libraries(boolector ${GMP_LIBRARIES})
endif()

if(Lingeling_FOUND)
  target_include_directories(boolector PRIVATE ${Lingeling_INCLUDE_DIR})
  target_link_libraries(boolector ${Lingeling_LIBRARIES})
endif()

if(CaDiCaL_FOUND)
  target_include_directories(boolector PRIVATE ${CaDiCaL_INCLUDE_DIR})
  target_link_libraries(boolector ${CaDiCaL_LIBRARIES})
endif()

if(CryptoMiniSat_FOUND)
  target_include_directories(boolector PRIVATE ${CryptoMiniSat_INCLUDE_DIR})
  target_link_libraries(boolector ${CryptoMiniSat_LIBRARIES})
endif()

if(PicoSAT_FOUND)
  target_include_directories(boolector PRIVATE ${PicoSAT_INCLUDE_DIR})
  target_link_libraries(boolector ${PicoSAT_LIBRARIES})
endif()

if(MiniSat_FOUND)
  target_include_directories(boolector PRIVATE ${MiniSat_INCLUDE_DIR})
  target_link_libraries(boolector ${MiniSat_LIBRARIES})
endif()

install(TARGETS boolector
  EXPORT boolector-export
  LIBRARY DESTINATION lib
  ARCHIVE DESTINATION lib
)

install(EXPORT boolector-export
  FILE BoolectorTargets.cmake
  NAMESPACE Boolector::
  DESTINATION lib/cmake/Boolector)

# Install header files
install(FILES boolector.h bzlatypes.h DESTINATION include/boolector)

#-----------------------------------------------------------------------------#
# boolector

add_executable (boolector-bin ${boolector_src_files})
target_link_libraries(boolector-bin boolector)
set_target_properties(boolector-bin
  PROPERTIES
    OUTPUT_NAME boolector
    RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin)
install(TARGETS boolector-bin DESTINATION bin)

#-----------------------------------------------------------------------------#
# Static binaries

if(NOT BUILD_SHARED_LIBS AND NOT APPLE)
  set(BZLA_STATIC_FLAGS "-static")
  set(STATIC_TARGETS boolector-bin)

  if(HAVE_NO_EXPORT_DYNAMIC)
    set(BZLA_STATIC_FLAGS "${BZLA_STATIC_FLAGS} -Wl,--no-export-dynamic")
  endif()
  set_target_properties(${STATIC_TARGETS}
    PROPERTIES
      LINK_FLAGS ${BZLA_STATIC_FLAGS}
      LINK_SEARCH_START_STATIC ON LINK_SEARCH_END_STATIC ON)
endif()
