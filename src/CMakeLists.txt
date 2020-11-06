set(libcbitwuzla_src_files
  aigprop.c
  bzlaaig.c
  bzlaaigvec.c
  bzlaass.c
  bzlabeta.c
  bzlabv.c
  bzlabvdomain.c
  bzlabvprop.c
  bzlachkclone.c
  bzlachkmodel.c
  bzlachkfailed.c
  bzlaclone.c
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
  bzlaslvprop.c
  bzlaslvquant.c
  bzlaslvsls.c
  bzlasort.c
  bzlasubst.c
  bzlafp.cpp
  bzlasynth.c
  bzlatrapi.c
  api/c/bitwuzla.c
  dumper/bzladumpaig.c
  dumper/bzladumpbtor.c
  dumper/bzladumpsmt.c
  parser/bzlabtor.c
  parser/bzlabtor2.c
  parser/bzlasmt2.c
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
  sat/bzlacadical.c
  sat/bzlacms.cpp
  sat/bzlalgl.c
  sat/bzlaminisat.cpp
  sat/bzlapicosat.c
  sat/bzlakissat.c
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
  utils/bzlaabort.c
)

set(cbitwuzla_src_files
  bitwuzlamain.c
  bzlamain.c
)

#-----------------------------------------------------------------------------#
# CBitwuzla library

add_library(cbitwuzla ${libcbitwuzla_src_files})
target_link_libraries(cbitwuzla ${LIBRARIES})
target_include_directories(cbitwuzla
  PUBLIC
    $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}>
    $<INSTALL_INTERFACE:include>)

target_include_directories(cbitwuzla PRIVATE ${Btor2Tools_INCLUDE_DIR})
target_link_libraries(cbitwuzla ${Btor2Tools_LIBRARIES})

if(GMP_FOUND)
  target_include_directories(cbitwuzla PRIVATE ${GMP_INCLUDE_DIR})
  target_link_libraries(cbitwuzla ${GMP_LIBRARIES})
endif()

if(Lingeling_FOUND)
  target_include_directories(cbitwuzla PRIVATE ${Lingeling_INCLUDE_DIR})
  target_link_libraries(cbitwuzla ${Lingeling_LIBRARIES})
endif()

if(CaDiCaL_FOUND)
  target_include_directories(cbitwuzla PRIVATE ${CaDiCaL_INCLUDE_DIR})
  target_link_libraries(cbitwuzla ${CaDiCaL_LIBRARIES})
endif()

if(CryptoMiniSat_FOUND)
  target_include_directories(cbitwuzla PRIVATE ${CryptoMiniSat_INCLUDE_DIR})
  target_link_libraries(cbitwuzla ${CryptoMiniSat_LIBRARIES})
endif()

if(PicoSAT_FOUND)
  target_include_directories(cbitwuzla PRIVATE ${PicoSAT_INCLUDE_DIR})
  target_link_libraries(cbitwuzla ${PicoSAT_LIBRARIES})
endif()

if(Kissat_FOUND)
  target_include_directories(cbitwuzla PRIVATE ${Kissat_INCLUDE_DIR})
  target_link_libraries(cbitwuzla ${Kissat_LIBRARIES})
endif()

if(MiniSat_FOUND)
  target_include_directories(cbitwuzla PRIVATE ${MiniSat_INCLUDE_DIR})
  target_link_libraries(cbitwuzla ${MiniSat_LIBRARIES})
endif()

install(TARGETS cbitwuzla
  EXPORT cbitwuzla-export
  LIBRARY DESTINATION lib
  ARCHIVE DESTINATION lib
)

install(EXPORT cbitwuzla-export
  FILE CBitwuzlaTargets.cmake
  NAMESPACE CBitwuzla::
  DESTINATION lib/cmake/CBitwuzla)

# Install header files
install(FILES api/c/bitwuzla.h DESTINATION include/cbitwuzla)

#-----------------------------------------------------------------------------#
# CBitwuzla binary

add_executable (cbitwuzla-bin ${cbitwuzla_src_files})
target_link_libraries(cbitwuzla-bin cbitwuzla)
set_target_properties(cbitwuzla-bin
  PROPERTIES
    OUTPUT_NAME cbitwuzla
    RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin)
install(TARGETS cbitwuzla-bin DESTINATION bin)

#-----------------------------------------------------------------------------#
# Static binaries

if(NOT BUILD_SHARED_LIBS AND NOT APPLE)
  set(BZLA_STATIC_FLAGS "-static")
  set(STATIC_TARGETS cbitwuzla-bin)

  if(HAVE_NO_EXPORT_DYNAMIC)
    set(BZLA_STATIC_FLAGS "${BZLA_STATIC_FLAGS} -Wl,--no-export-dynamic")
  endif()
  set_target_properties(${STATIC_TARGETS}
    PROPERTIES
      LINK_FLAGS ${BZLA_STATIC_FLAGS}
      LINK_SEARCH_START_STATIC ON LINK_SEARCH_END_STATIC ON)
endif()
