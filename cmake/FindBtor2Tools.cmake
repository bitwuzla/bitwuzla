# Find Btor2Tools
# Btor2Tools_FOUND - found Btor2Tools lib
# Btor2Tools_INCLUDE_DIR - the Btor2Tools include directory
# Btor2Tools_LIBRARIES - Libraries needed to use Btor2Tools

find_path(Btor2Tools_INCLUDE_DIR NAMES btor2parser/btor2parser.h)
find_library(Btor2Tools_LIBRARIES NAMES btor2parser)

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(Btor2Tools
  DEFAULT_MSG Btor2Tools_INCLUDE_DIR Btor2Tools_LIBRARIES)

mark_as_advanced(Btor2Tools_INCLUDE_DIR Btor2Tools_LIBRARIES)
if(Btor2Tools_LIBRARIES)
  message(STATUS "Found Btor2Tools library: ${Btor2Tools_LIBRARIES}")
endif()
