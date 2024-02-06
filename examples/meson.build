project('bitwuzla-examples',
  ['c', 'cpp'],
  meson_version: '>= 0.64',
  default_options: [
    'c_std=c17',
    'cpp_std=c++17',
  ]
)

# Build parameters
python_path = get_option('python_path')

subdir('c')
subdir('cpp')

if python_path != ''
  subdir('python')
endif
