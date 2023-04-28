conf_data = configuration_data()

include_path = join_paths(meson.project_source_root(), 'include', 'bitwuzla')
header_files = [
  join_paths(include_path, 'cpp', 'bitwuzla.h'),
  join_paths(include_path, 'cpp', 'parser.h'),
  join_paths(include_path, 'enums.h'),
  join_paths(include_path, 'option.h'),
]

conf_data.set('PROJECT_NAME', 'Bitwuzla_cpp')
conf_data.set('PREDEFINED', '')
conf_data.set('DOXYGEN_INPUT', ' '.join(header_files))
conf_data.set('DOXYGEN_OUTPUT_DIR', meson.current_build_dir())
doxyfile = configure_file(input: '../Doxyfile.in',
                          output: 'Doxyfile',
                          configuration: conf_data)

depend_files = [
  doxyfile,
  'api.rst',
  'interface.rst',
  'library_info.rst',
  'options.rst',
  'sort_creation.rst',
  'term_creation.rst',
  'term_substitution.rst',
  'classes/bitwuzla.rst',
  'classes/exception.rst',
  'classes/options.rst',
  'classes/optioninfo.rst',
  'classes/parser.rst',
  'classes/sort.rst',
  'classes/term.rst',
  'classes/terminator.rst',
  'enums/kind.rst',
  'enums/option.rst',
  'enums/result.rst',
  'enums/roundingmode.rst',
]
depend_files += header_files
docs_doxygen_cpp = custom_target('docs-doxygen-cpp',
  build_by_default: true,
  output: 'xml',
  command: [doxygen, doxyfile],
  depend_files: depend_files
)
