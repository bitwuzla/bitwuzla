set(libbzlabv_src_files
  bv/bitvector.cpp
)

set(libbzlabb_src_files
  bitblast/aig/aig_manager.cpp
  bitblast/aig/aig_cnf.cpp
  bitblast/aig/aig_printer.cpp
  bitblast/aig_bitblaster.cpp
)

set(libbzlals_src_files
  ls/ls.cpp
  ls/ls_bv.cpp
  ls/bv/bitvector_domain.cpp
  ls/bv/bitvector_node.cpp
  ls/node/node.cpp
  util/wheel_factorizer.cpp
)

set(libbzlarng_src_files
  rng/rng.cpp
)

#-----------------------------------------------------------------------------#
# bzlarng library

add_library(bzlarng ${libbzlarng_src_files})
target_include_directories(bzlarng PUBLIC ${GMP_INCLUDE_DIR})
target_link_libraries(bzlarng ${GMP_LIBRARIES})

target_include_directories(bzlarng
  PUBLIC
    $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}>
    $<INSTALL_INTERFACE:include>)

#-----------------------------------------------------------------------------#
# bzlabv library

add_library(bzlabv ${libbzlabv_src_files})
target_include_directories(bzlabv PUBLIC ${GMP_INCLUDE_DIR})
target_link_libraries(bzlabv ${GMP_LIBRARIES} bzlarng)

target_include_directories(bzlabv
  PUBLIC
    $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}>
    $<INSTALL_INTERFACE:include>)

#-----------------------------------------------------------------------------#
# bzlabb library

add_library(bzlabb ${libbzlabb_src_files})
target_link_libraries(bzlabb bzlabv)

target_include_directories(bzlabb
  PUBLIC
    $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}>
    $<INSTALL_INTERFACE:include>)

#-----------------------------------------------------------------------------#
# bzlals library

add_library(bzlals ${libbzlals_src_files})
target_link_libraries(bzlals bzlabv bzlarng)

target_include_directories(bzlals
  PUBLIC
    $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}>
    $<INSTALL_INTERFACE:include>)

#-----------------------------------------------------------------------------#
# Install

install(TARGETS bzlabv
  EXPORT bitwuzla-export
  LIBRARY DESTINATION lib
  ARCHIVE DESTINATION lib
)

install(TARGETS bzlabb
  EXPORT bitwuzla-export
  LIBRARY DESTINATION lib
  ARCHIVE DESTINATION lib
)

install(TARGETS bzlals
  EXPORT bitwuzla-export
  LIBRARY DESTINATION lib
  ARCHIVE DESTINATION lib
)

install(TARGETS bzlarng
  EXPORT bitwuzla-export
  LIBRARY DESTINATION lib
  ARCHIVE DESTINATION lib
)

install(EXPORT bitwuzla-export
  FILE BzlaBVTargets.cmake
  NAMESPACE BzlaBV::
  DESTINATION lib/cmake/Bitwuzla)

install(EXPORT bitwuzla-export
  FILE BzlaBBTargets.cmake
  NAMESPACE BzlaBB::
  DESTINATION lib/cmake/Bitwuzla)

install(EXPORT bitwuzla-export
  FILE BzlaLSTargets.cmake
  NAMESPACE BzlaLS::
  DESTINATION lib/cmake/Bitwuzla)

install(EXPORT bitwuzla-export
  FILE BzlaRNGTargets.cmake
  NAMESPACE BzlaRNG::
  DESTINATION lib/cmake/Bitwuzla)

install(FILES ls/ls.h ls/ls_bv.h DESTINATION include/bitwuzla/ls)
install(FILES bv/bitvector.h DESTINATION include/bitwuzla/bv)
