###
# Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
#
# This file is part of Bitwuzla.
#
# Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
#
# See COPYING for more information on using this software.
##
cmake_minimum_required(VERSION 3.11)
project(Gimsatul)

set(libgimsatul_src_files
  allocate.c
  analyze.c
  assign.c
  average.c
  backtrack.c
  barrier.c
  build.c
  bump.c
  catch.c
  clause.c
  clone.c
  compact.c
  decide.c
  deduplicate.c
  definition.c
  detach.c
  eliminate.c
  export.c
  fail.c
  file.c
  heap.c
  import.c
  logging.c
  message.c
  minimize.c
  mode.c
  options.c
  parse.c
  probe.c
  profile.c
  propagate.c
  queue.c
  reduce.c
  rephase.c
  report.c
  restart.c
  ring.c
  ruler.c
  search.c
  set.c
  simplify.c
  solve.c
  statistics.c
  substitute.c
  subsume.c
  system.c
  trace.c
  types.c
  unclone.c
  utilities.c
  vivify.c
  walk.c
  warm.c
  watches.c
  witness.c
)

set(libgimsatul_headers
  allocate.h
  analyze.h
  assign.h
  average.h
  backtrack.h
  barrier.h
  build.h
  bump.h
  catch.h
  clause.h
  clone.h
  compact.h
  ${CMAKE_CURRENT_BINARY_DIR}/config.h
  cover.h
  decide.h
  deduplicate.h
  definition.h
  detach.h
  eliminate.h
  export.h
  fail.h
  file.h
  heap.h
  import.h
  logging.h
  macros.h
  message.h
  minimize.h
  mode.h
  options.h
  parse.h
  probe.h
  profile.h
  propagate.h
  queue.h
  random.h
  reduce.h
  rephase.h
  report.h
  restart.h
  ring.h
  ruler.h
  search.h
  set.h
  simplify.h
  solve.h
  stack.h
  statistics.h
  substitute.h
  subsume.h
  system.h
  tagging.h
  trace.h
  types.h
  unclone.h
  usage.h
  utilities.h
  variable.h
  vivify.h
  walk.h
  warm.h
  watches.h
  witness.h
)

set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -Wall -O3 -DNDEBUG -DQUIET")

configure_file(config.h.in config.h)

add_library(gimsatul ${libgimsatul_src_files})
target_link_libraries(gimsatul m)
target_link_libraries(gimsatul pthread)
target_include_directories(gimsatul PRIVATE ${CMAKE_PROJECT_DIR})
target_include_directories(gimsatul PRIVATE ${CMAKE_CURRENT_BINARY_DIR})

install(TARGETS gimsatul
  EXPORT gimsatul-export
  LIBRARY DESTINATION lib
  ARCHIVE DESTINATION lib)

install(FILES ${libgimsatul_headers} DESTINATION include/gimsatul)
