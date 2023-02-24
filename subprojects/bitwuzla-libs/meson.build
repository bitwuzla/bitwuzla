project('bitwuzla-libs',
  'cpp',
  meson_version: '>= 0.64',
  license: 'mit',
  default_options: [
    'cpp_std=c++17',
    'buildtype=release',
    'default_library=static',
    'b_ndebug=if-release'
  ]
)

# Build parameters
build_static = get_option('default_library') == 'static' and get_option('b_sanitize') == 'none'

# Configure unit testing
if get_option('unit_testing').auto()
  if get_option('buildtype') == 'release'
    enable_unit_testing = false
  elif get_option('buildtype') == 'debug'
    enable_unit_testing = true
  endif
else
  enable_unit_testing = get_option('unit_testing').enabled()
endif

subdir('src')
if enable_unit_testing
  subdir('test')
endif
