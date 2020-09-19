# Check if the linker flag no-export-dynamic is supported
include(CheckCSourceCompiles)

set(CMAKE_REQUIRED_FLAGS "-Wl,--no-export-dynamic")
check_c_compiler_flag("" HAVE_NO_EXPORT_DYNAMIC)
unset(CMAKE_REQUIRED_FLAGS)
