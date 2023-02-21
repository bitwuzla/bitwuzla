bv_sources = [
  'bv/bitvector.cpp'
]

bb_sources = [
  'bitblast/aig/aig_manager.cpp',
  'bitblast/aig/aig_cnf.cpp',
  'bitblast/aig/aig_printer.cpp',
  'bitblast/aig_bitblaster.cpp'
]

ls_sources = [
  'ls/ls.cpp',
  'ls/ls_bv.cpp',
  'ls/bv/bitvector_domain.cpp',
  'ls/bv/bitvector_node.cpp',
  'ls/node/node.cpp',
  'util/wheel_factorizer.cpp'
]

rng_sources = [
  'rng/rng.cpp'
]

gmp_dep = dependency('gmp',
                     version: '>=6.1',
                     required: true,
                     static: build_static)

# RNG support library
rng_lib = static_library('bzlarng',
                  sources: rng_sources,
                  dependencies: gmp_dep)

# Bitwuzla bit-vector, bit-blast and local search libraries
bv_lib = library('bitwuzlabv',
                 sources: bv_sources,
                 link_whole: rng_lib,
                 dependencies: gmp_dep,
                 install: true)
bb_lib = library('bitwuzlabb',
                 sources: bb_sources,
                 link_with: bv_lib,
                 dependencies: gmp_dep,
                 install: true)
ls_lib = library('bitwuzlals',
                 sources: ls_sources,
                 link_with: [bv_lib],
                 link_whole: rng_lib,
                 dependencies: gmp_dep,
                 install: true)

inc = include_directories('.')
bitwuzla_bv_dep = declare_dependency(include_directories: inc,
                                     link_with: bv_lib,
                                     dependencies: gmp_dep)
bitwuzla_bb_dep = declare_dependency(include_directories: inc,
                                     link_with: bb_lib,
                                     dependencies: gmp_dep)
bitwuzla_ls_dep = declare_dependency(include_directories: inc,
                                     link_with: ls_lib,
                                     dependencies: gmp_dep)
