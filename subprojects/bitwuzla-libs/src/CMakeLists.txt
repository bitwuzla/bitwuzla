set(libbzlals_src_files
  bzlals.cpp
  bitvector.cpp
  bitvector_domain.cpp
  bitvector_node.cpp
  rng.cpp
  wheel_factorizer.cpp
)

#-----------------------------------------------------------------------------#
# bzla-ls library

add_library(bzlals ${libbzlals_src_files})
target_link_libraries(bzlals ${LIBRARIES})
target_include_directories(bzlals
  PUBLIC
    $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}>
    $<INSTALL_INTERFACE:include>)

target_include_directories(bzlals PRIVATE ${GMP_INCLUDE_DIR})
target_link_libraries(bzlals ${GMP_LIBRARIES})

# TODO install
