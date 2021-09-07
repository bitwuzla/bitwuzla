set(libbzlabv_src_files
  bitvector.cpp
  rng.cpp
)

set(libbzlals_src_files
  bzlals.cpp
  bitvector_domain.cpp
  bitvector_node.cpp
  rng.cpp
  wheel_factorizer.cpp
)

#-----------------------------------------------------------------------------#
# bzlabv library

add_library(bzlabv ${libbzlabv_src_files})
target_include_directories(bzlabv PRIVATE ${GMP_INCLUDE_DIR})
target_link_libraries(bzlabv ${GMP_LIBRARIES})

#-----------------------------------------------------------------------------#
# bzlals library

add_library(bzlals ${libbzlals_src_files})
target_link_libraries(bzlals bzlabv)

target_include_directories(bzlals
  PUBLIC
    $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}>
    $<INSTALL_INTERFACE:include>)

#-----------------------------------------------------------------------------#
# Install

install(TARGETS bzlals
  EXPORT bzlals-export
  LIBRARY DESTINATION lib
  ARCHIVE DESTINATION lib
)

install(TARGETS bzlabv
  EXPORT bzlabv-export
  LIBRARY DESTINATION lib
  ARCHIVE DESTINATION lib
)

install(EXPORT bzlals-export
  FILE BzlaLSTargets.cmake
  NAMESPACE BzlaLS::
  DESTINATION lib/cmake/BzlaLS)

install(EXPORT bzlabv-export
  FILE BzlaBVTargets.cmake
  NAMESPACE BzlaBV::
  DESTINATION lib/cmake/BzlaBV)

install(FILES bzlals.h bitvector.h DESTINATION include)
