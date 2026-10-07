project('cryptominisat5',
  ['c', 'cpp'],
  version: '5.11.21',
  license: 'mit',
  default_options: [
    'cpp_std=c++17',
    'buildtype=release',
    'default_library=static',
    'b_ndebug=if-release',
    'warning_level=0',
  ]
)

# CryptoMiniSat uses sprintf(), which is marked deprecated in the macOS SDK.
add_project_arguments(
  meson.get_compiler('cpp').get_supported_arguments(
    '-Wno-deprecated-declarations'),
  language: 'cpp')

# The bundled PicoSAT compares a pointer against a char constant in an
# assertion.
add_project_arguments(
  meson.get_compiler('c').get_supported_arguments('-Wno-pointer-compare'),
  language: 'c')

header_targets=[]

subdir('cryptominisat5')
subdir('src')
