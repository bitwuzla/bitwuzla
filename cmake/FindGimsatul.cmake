###
# Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
#
# This file is part of Bitwuzla.
#
# Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
#
# See COPYING for more information on using this software.
##
# Find Gimsatul
# Gimsatul_FOUND - found Gimsatul lib
# Gimsatul_INCLUDE_DIR - the Gimsatul include directory
# Gimsatul_LIBRARIES - Libraries needed to use Gimsatul

find_path(Gimsatul_INCLUDE_DIR NAMES gimsatul/ruler.h)
find_library(Gimsatul_LIBRARIES NAMES gimsatul)

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(Gimsatul
  DEFAULT_MSG Gimsatul_INCLUDE_DIR Gimsatul_LIBRARIES)

mark_as_advanced(Gimsatul_INCLUDE_DIR Gimsatul_LIBRARIES)
if(Gimsatul_LIBRARIES)
  message(STATUS "Found Gimsatul library: ${Gimsatul_LIBRARIES}")
endif()
