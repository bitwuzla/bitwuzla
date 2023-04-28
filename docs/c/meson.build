conf_data = configuration_data()

include_path = join_paths(meson.project_source_root(), 'include', 'bitwuzla')
header_files = [
  join_paths(include_path, 'c', 'bitwuzla.h'),
  join_paths(include_path, 'c', 'parser.h'),
  join_paths(include_path, 'enums.h'),
  join_paths(include_path, 'option.h'),
]

conf_data.set('PROJECT_NAME', 'Bitwuzla_c')
conf_data.set('PREDEFINED', 'BITWUZLA_API_USE_C_ENUMS')
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
  'enums/bitwuzlakind.rst',
  'enums/bitwuzlaoption.rst',
  'enums/bitwuzlaresult.rst',
  'enums/bitwuzlaroundingmode.rst',
  'structs/bitwuzlaoptioninfo.rst',
  'types/bitwuzla.rst',
  'types/bitwuzlaoptions.rst',
  'types/bitwuzlaparser.rst',
  'types/bitwuzlasort.rst',
  'types/bitwuzlaterm.rst',
]
depend_files += header_files
docs_doxygen_c = custom_target('docs-doxygen-c',
  build_by_default: true,
  output: 'xml',
  command: [doxygen, doxyfile],
  depend_files: depend_files
)
