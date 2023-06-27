# ---
# Build Python bindings
# ---

add_languages('cython', native: false, required: true)

python = import('python').find_installation()
mkenums_script = files('mkenums.py')

# Generate enums include
enums_h = files('../../../include/bitwuzla/enums.h')
enums_pxd = custom_target('enums.pxd',
  output: 'enums.pxd',
  depend_files: [mkenums_script, enums_h],
  command: [python, mkenums_script, enums_h, '@OUTPUT@']
)

# Generate options include
option_h = files('../../../include/bitwuzla/option.h')
options_pxd = custom_target('options.pxd',
  output: 'options.pxd',
  depend_files: [mkenums_script, option_h],
  command: [python, mkenums_script, option_h, '@OUTPUT@']
)

# Build Python module
python_dep = python.dependency()
bitwuzla_py_ext = python.extension_module(
  'bitwuzla',
  ['bitwuzla.pyx', enums_pxd, options_pxd, 'terminator.cpp'],
  dependencies: [python_dep, bitwuzla_dep],
  # Note: include_directories not passed to cython compiler
  cython_args: ['-I', meson.current_build_dir()],
  override_options: ['cython_language=cpp'],
  install: true,
  install_tag: 'python-bindings'
)

# Add alias for python module target
alias_target('python-bindings', bitwuzla_py_ext)
