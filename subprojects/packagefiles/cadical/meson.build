project('cadical',
  ['cpp', 'c'],
  version: '3.0.0',
  license: 'mit',
  default_options: [
    'cpp_std=c++11',
    'buildtype=release',
    'default_library=static',
    'b_ndebug=if-release',
    'warning_level=0'
  ]
)

header_targets = []
subdir('include/cadical')
subdir('src')
