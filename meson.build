project('bitwuzla',
  ['c', 'cpp'],
  meson_version: '>= 0.64',
  version: '0.3.2',
  license: 'mit',
  default_options: [
    'c_std=c17',
    'cpp_std=c++17',
    'buildtype=release',
    'b_ndebug=if-release',
    'default_library=static',
    'strip=true',
    'warning_level=3'
  ]
)
bitwuzla_lib_soversion = 0

install_rpath = join_paths(get_option('prefix'), get_option('libdir'))

# Build parameters
enable_python = get_option('python')

# Whether external and system libraries should be statically linked
build_static = get_option('default_library') == 'static' \
               and get_option('b_sanitize') == 'none' \
               and not enable_python

# Configure testing
if get_option('testing').auto()
  if get_option('buildtype') == 'release'
    enable_testing = false
  elif get_option('buildtype') == 'debug'
    enable_testing = true
  endif
else
  enable_testing = get_option('testing').enabled()
endif

if get_option('unit_testing').auto()
  enable_unit_testing = enable_testing
else
  enable_unit_testing = get_option('unit_testing').enabled()
endif

subdir('src')

if enable_python
  subdir('src/api/python')
endif

if enable_testing
  if enable_unit_testing
    subdir('test/unit')
  endif
  subdir('test/regress')
  if enable_python
    subdir('test/python')
  endif
endif

if get_option('docs')
  subdir('docs')
endif

# Install public headers
install_subdir('include/bitwuzla', install_dir: 'include')
