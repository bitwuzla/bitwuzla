btor2parser_lib = library('btor2parser',
                          'btor2parser/btor2parser.c',
                          override_options: ['c_std=gnu99'],
                          install: true,
                          pic: true)
btor2parser_dep = declare_dependency(
                  include_directories: include_directories('.'),
                  link_with: btor2parser_lib)
