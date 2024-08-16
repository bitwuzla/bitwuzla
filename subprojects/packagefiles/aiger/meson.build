project('aiger',
  'c',
  version: '1.9.19',
  license: 'mit',
  default_options: [
    'c_std=gnu99',
    'buildtype=release',
    'default_library=static',
    'b_ndebug=if-release',
    'warning_level=0',
    'optimization=3',
  ]
)

aiger_lib = library('aiger', sources: ['aiger.c'])
aiger_dep = declare_dependency(
                  include_directories: include_directories('.'),
                  link_with: aiger_lib)
