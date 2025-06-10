project('mimalloc-static',
  'c', 'cpp',
  version: '2.2.4',
  license: 'mit',
  default_options: [
    'c_std=c11',
    'cpp_std=c++17',
    'buildtype=release',
    'default_library=static',
    'b_ndebug=true',
    'warning_level=0',
  ]
)


# Compile as C++ program
fs = import('fs')
sources = fs.copyfile('src/static.c', 'static.cpp')
# Override default malloc
cpp_args = ['-DMI_MALLOC_OVERRIDE']

mimalloc_static_lib = static_library('mimalloc-static',
                                     include_directories: ['include', 'src'],
                                     sources: sources,
                                     cpp_args: cpp_args)

mimalloc_static_dep = declare_dependency(link_with: mimalloc_static_lib)
