project('bitwuzla',
  ['c', 'cpp'],
  meson_version: '>= 0.64',
  version: '0.9.1-dev',
  license: 'mit',
  default_options: [
    'c_std=c17',
    'cpp_std=c++20',
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

is_sat_solver_configured = get_option('cadical') or \
                           get_option('cryptominisat') or \
                           get_option('gimsatul') or \
                           get_option('kissat')
# Configure testing
if not is_sat_solver_configured
  enable_testing = false
else
  if get_option('testing').auto()
    if get_option('buildtype') == 'release'
      enable_testing = false
    elif get_option('buildtype') in ['debug', 'debugoptimized']
      enable_testing = true
    endif
  else
    enable_testing = get_option('testing').enabled()
  endif
endif

if get_option('unit_testing').auto()
  enable_unit_testing = enable_testing
else
  enable_unit_testing = get_option('unit_testing').enabled()
endif

# Apple's linker warns about libraries that are passed more than once. This is
# harmless and happens if a dependency's pkg-config file lists a library that
# is also passed by another dependency, e.g., MPFR adds a bare '-lgmp' while GMP
# is already linked via its full path.
if host_machine.system() == 'darwin'
  add_project_link_arguments(
    meson.get_compiler('cpp').get_supported_link_arguments(
      '-Wl,-no_warn_duplicate_libraries'),
    language: ['c', 'cpp'])
endif

# Objects compiled for link-time optimization only contain the compiler's
# intermediate representation, which only the same compiler can link. Static
# libraries, which also bundle the objects of subprojects, additionally need
# machine code to be linkable by other compilers. Clang supports such fat
# objects for ELF only.
lto_fat_static = false
if get_option('b_lto') and get_option('default_library') != 'shared'
  lto_fat_static = true
  foreach lang : ['c', 'cpp']
    compiler = meson.get_compiler(lang)
    if compiler.has_multi_arguments('-flto', '-ffat-lto-objects')
      add_global_arguments('-ffat-lto-objects', language: lang)
    else
      lto_fat_static = false
    endif
  endforeach
endif

subdir('src')

# The intermediate representation is only needed for linking within the build.
# Remove it from installed static libraries, which keep their machine code
# only, as Linux distributions do for packaged static libraries.
if lto_fat_static
  static_libs = []
  foreach lib : [bitwuzla_lib] + support_libs
    if get_option('default_library') == 'both'
      lib = lib.get_static_lib()
    endif
    static_libs += lib
  endforeach
  meson.add_install_script(find_program('python3', 'python'),
                           files('src/strip_lto.py'),
                           find_program('objcopy').full_path(),
                           get_option('libdir'),
                           static_libs,
                           install_tag: 'devel')
endif

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

# Optional development utilities, not built by default
if is_sat_solver_configured
  subdir('contrib/lemma_scorer')
endif

# Install public headers
install_subdir('include/bitwuzla', install_dir: 'include')
