set(main_src_files
  main.cpp
)

## Bitwuzla binary
add_executable (bitwuzla-bin ${main_src_files})
target_link_libraries(bitwuzla-bin bitwuzla)
set_target_properties(bitwuzla-bin
  PROPERTIES
    OUTPUT_NAME bitwuzla
    RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin)
install(TARGETS bitwuzla-bin DESTINATION bin)

## Static binary
if(NOT BUILD_SHARED_LIBS AND NOT APPLE)
  set(BZLA_STATIC_FLAGS "-static")
  set(STATIC_TARGETS bitwuzla-bin)

  if(HAVE_NO_EXPORT_DYNAMIC)
    set(BZLA_STATIC_FLAGS "${BZLA_STATIC_FLAGS} -Wl,--no-export-dynamic")
  endif()
  set_target_properties(${STATIC_TARGETS}
    PROPERTIES
      LINK_FLAGS ${BZLA_STATIC_FLAGS}
      LINK_SEARCH_START_STATIC ON LINK_SEARCH_END_STATIC ON)
endif()
