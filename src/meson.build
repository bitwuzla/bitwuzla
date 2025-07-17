fs = import('fs')

c_compiler = meson.get_compiler('c')
cpp_compiler = meson.get_compiler('cpp')

cpp_args = []

# ---
# Bitwuzla library dependencies
# ---

# External dependencies

# GMP is a dependency of MPFR. However, MPFR requires GMP to be available at
# configure time, which prevents us from using the fallback subproject of GMP,
# since the subproject is built in the build stage.
# Thus, we require that GMP is installed on the system or --build-deps was used
# to configure this project.

if get_option('with_gmp') != ''
  gmp_dir = get_option('with_gmp')
  libdir = join_paths(gmp_dir, get_option('libdir'))
  incdir = join_paths(gmp_dir, get_option('includedir'))
  gmp_dep = c_compiler.find_library('gmp',
                                    has_headers: ['gmp.h', 'gmpxx.h'],
                                    static: build_static,
                                    dirs: libdir,
                                    header_args: '-I' + incdir,
                                    required: true)
  cpp_args += ['-I' + incdir]
else
  gmp_dep = dependency('gmp',
                       version: '>=6.3',
                       required: true,
                       static: build_static,
                       allow_fallback: false)
endif

if get_option('with_mpfr') != ''
  mpfr_dir = get_option('with_mpfr')
  libdir = join_paths(mpfr_dir, get_option('libdir'))
  incdir = join_paths(mpfr_dir, get_option('includedir'))
  mpfr_dep = c_compiler.find_library('mpfr',
                                    has_headers: ['mpfr.h'],
                                    static: build_static,
                                    dirs: libdir,
                                    header_args: '-I' + incdir,
                                    required: true)
  cpp_args += ['-I' + incdir]
else
  mpfr_dep = dependency('mpfr',
                        version: '>=4.2.2',
                        required: true,
                        static: build_static)
endif

# CaDiCaL does not provide pkg-config to find dependency
cadical_dep = cpp_compiler.find_library('cadical',
                                        has_headers: 'cadical.hpp',
                                        static: build_static,
                                        required: false)
if not cadical_dep.found()
  cadical_dep = dependency('cadical', required: true)
endif

cms_dep = dependency('cryptominisat5',
                     version: '5.11.21',
                     static: build_static,
                     required: get_option('cryptominisat'))

# Kissat does not provide pkg-config to find dependency
kissat_dep = cpp_compiler.find_library('kissat',
                                        has_headers: 'kissat.h',
                                        static: build_static,
                                        required: false)
if not kissat_dep.found()
  kissat_dep = dependency('kissat', required: get_option('kissat'))
endif

# Using system include type suppresses compile warnings originating from the
# symfpu headers
symfpu_dep = dependency('symfpu', include_type: 'system', required: true)

dependencies = [symfpu_dep, cadical_dep, cms_dep, kissat_dep, gmp_dep, mpfr_dep]

if cms_dep.found()
  cpp_args += ['-DBZLA_USE_CMS']
endif
if kissat_dep.found()
  cpp_args += ['-DBZLA_USE_KISSAT']
endif
if mpfr_dep.found()
  cpp_args += ['-DMPFR_USE_C99_FEATURE=1']
endif

# ---
# Additional build definitions
# ---

if cpp_compiler.has_function('getrusage', prefix: '#include <sys/resource.h>')
  cpp_args += ['-DHAVE_RUSAGE']
endif

if get_option('fpexp')
  cpp_args += ['-DBZLA_USE_FPEXP']
endif

# ---
# Generate config.h
# ---

# Generate license text
license_text = fs.read(join_paths(meson.project_source_root(),
                                  'COPYING')).strip()
license_text += '''\n\n
This version of Bitwuzla is linked against the following
third party libraries. For copyright information of each
library see the corresponding url.'''
license_text += '\n\n  CaDiCaL\n  https://github.com/arminbiere/cadical'
license_text += \
  '\n\n  GMP - GNU Multiple Precision Arithmetic Library\n  https://gmplib.org'
if cms_dep.found()
  license_text += '\n\n  CryptoMiniSat\n  https://github.com/msoos/cryptominisat'
endif
if kissat_dep.found()
  license_text += '\n\n  Kissat\n  https://github.com/arminbiere/kissat'
endif
license_text += '\n\n  SymFPU\n  https://github.com/martin-cs/symfpu'
license_text = license_text.replace('\n', '\\n').replace('"', '\\"')

# Generate header
git_exe = find_program('git', required: false)
if git_exe.found()
  is_git_version = run_command(git_exe, 'rev-parse', '--is-inside-work-tree',
                               check: false).returncode() == 0
  git_id = '@git_id@'
  output_h = 'config.h.in'
else
  is_git_version = false
  git_id = ''
  output_h = 'config.h'
endif

conf_data = configuration_data()
conf_data.set('cc', c_compiler.get_id() + ' ' + c_compiler.version())
conf_data.set('cxx', cpp_compiler.get_id() + ' ' + cpp_compiler.version())
conf_data.set('license', license_text)
conf_data.set('os', build_machine.system())
conf_data.set('git_id', git_id)
conf_data.set('version', meson.project_version())
conf_data.set('is_debug_build', (get_option('buildtype') == 'debug').to_string())
conf_data.set('is_dev_version', meson.project_version().endswith('-dev').to_string())
conf_data.set('is_git_version', is_git_version.to_string())
config_h = configure_file(input: 'config.h.in',
               output: output_h,
               configuration: conf_data)

# Get git information and generate git_config.h
if git_exe.found()
  python_exe = find_program('python3', 'python')
  repo = meson.project_source_root()
  get_git_id = join_paths(repo, 'src', 'get_git_id.py')
  config_input = join_paths(meson.current_build_dir(), 'config.h.in')
  config_h = vcs_tag(
    command: [python_exe, get_git_id, repo],
    input: config_input,
    output: 'config.h',
    replace_string: '@git_id@',
    fallback: ''
  )
endif

# ---
# Build Bitwuzla library
# ---
# Note: For now we keep the util library and support library sources separately
# so that we can easily create libraries in the future if needed.

sources = []

sources_util = files([
  'util/hash.cpp',
  'util/logger.cpp',
  'util/resources.cpp',
  'util/printer.cpp',
  'util/statistics.cpp',
  'util/util.cpp',
  'util/integer.cpp',
  'util/gmp_utils.cpp'
])
sources += sources_util

sources_lib_bv = files([
  'lib/bv/bitvector.cpp',
  'lib/bv/bounds/bitvector_bounds.cpp',
  'lib/bv/domain/bitvector_domain.cpp',
  'lib/bv/domain/wheel_factorizer.cpp'
])
sources += sources_lib_bv

sources_lib_bb = files([
  'lib/bitblast/aig/aig_cnf.cpp',
  'lib/bitblast/aig/aig_manager.cpp',
  'lib/bitblast/aig/aig_node.cpp',
  'lib/bitblast/aig/aig_printer.cpp'
])
sources += sources_lib_bb

sources_lib_ls = files([
  'lib/ls/ls.cpp',
  'lib/ls/ls_bv.cpp',
  'lib/ls/bv/bitvector_node.cpp',
  'lib/ls/node/node.cpp',
])
sources += sources_lib_ls

sources_lib_rng = files([
  'lib/rng/rng.cpp'
])
sources += sources_lib_rng

# AIGER dependency
aiger_dep = dependency('aiger', required: get_option('aiger'))

if aiger_dep.found()
  cpp_args += ['-DBZLA_USE_AIGER']
endif
if enable_unit_testing
  cpp_args += ['-DBZLA_ENABLE_UNIT_TESTING']
endif


sources += files([
  'api/c/bitwuzla.cpp',
  'api/c/bitwuzla_structs.cpp',
  'api/c/parser.cpp',
  'api/checks.cpp',
  'api/cpp/bitwuzla.cpp',
  'api/cpp/parser.cpp',
  'backtrack/assertion_stack.cpp',
  'backtrack/backtrackable.cpp',
  'check/check_model.cpp',
  'check/check_unsat_core.cpp',
  'check/check_term.cpp',
  'env.cpp',
  'node/kind_info.cpp',
  'node/node.cpp',
  'node/node_data.cpp',
  'node/node_kind.cpp',
  'node/node_manager.cpp',
  'node/node_unique_table.cpp',
  'node/node_utils.cpp',
  'option/option.cpp',
  'parser/btor2/lexer.cpp',
  'parser/btor2/parser.cpp',
  'parser/btor2/token.cpp',
  'parser/smt2/lexer.cpp',
  'parser/smt2/parser.cpp',
  'parser/smt2/symbol_table.cpp',
  'parser/smt2/token.cpp',
  'preprocess/assertion_tracker.cpp',
  'preprocess/assertion_vector.cpp',
  'preprocess/pass/contradicting_ands.cpp',
  'preprocess/pass/elim_extract.cpp',
  'preprocess/pass/elim_lambda.cpp',
  'preprocess/pass/elim_udiv.cpp',
  'preprocess/pass/elim_uninterpreted.cpp',
  'preprocess/pass/embedded_constraints.cpp',
  'preprocess/pass/flatten_and.cpp',
  'preprocess/pass/normalize.cpp',
  'preprocess/pass/rewrite.cpp',
  'preprocess/pass/skeleton_preproc.cpp',
  'preprocess/pass/variable_substitution.cpp',
  'preprocess/preprocessing_pass.cpp',
  'preprocess/preprocessor.cpp',
  'printer/btor2_printer.cpp',
  'printer/smt2_printer.cpp',
  'rewrite/evaluator.cpp',
  'rewrite/rewrite_utils.cpp',
  'rewrite/rewriter.cpp',
  'rewrite/rewrites_array.cpp',
  'rewrite/rewrites_bool.cpp',
  'rewrite/rewrites_bv.cpp',
  'rewrite/rewrites_bv_norm.cpp',
  'rewrite/rewrites_core.cpp',
  'rewrite/rewrites_fp.cpp',
  'resource_terminator.cpp',
  'sat/cadical.cpp',
  'sat/cryptominisat.cpp',
  'sat/kissat.cpp',
  'sat/sat_solver_factory.cpp',
  'solver/array/array_solver.cpp',
  'solver/abstract/abstraction_lemmas.cpp',
  'solver/abstract/abstraction_module.cpp',
  'solver/bv/bv_bitblast_solver.cpp',
  'solver/bv/bv_prop_solver.cpp',
  'solver/bv/bv_solver.cpp',
  'solver/bv/aig_bitblaster.cpp',
  'solver/fp/floating_point.cpp',
  'solver/fp/fp_solver.cpp',
  'solver/fp/rounding_mode.cpp',
  'solver/fp/symfpu_nm.cpp',
  'solver/fp/symfpu_floating_point_typeinfo.cpp',
  'solver/fp/symfpu_wrapper.cpp',
  'solver/fp/word_blaster.cpp',
  'solver/fun/fun_solver.cpp',
  'solver/quant/quant_solver.cpp',
  'solver/result.cpp',
  'solver/solver.cpp',
  'solver/solver_engine.cpp',
  'solver/solver_state.cpp',
  'solving_context.cpp',
  'type/type.cpp',
  'type/type_data.cpp',
  'type/type_manager.cpp',
])

# Public header include directory
bitwuzla_inc = include_directories('../include', 'lib')

bitwuzla_lib = library('bitwuzla',
                      sources + config_h,
                      include_directories: bitwuzla_inc,
                      dependencies: dependencies,
                      soversion: bitwuzla_lib_soversion,
                      install_rpath: install_rpath,
                      install: true,
                      cpp_args: cpp_args)

# Create library dependency
bitwuzla_dep = declare_dependency(include_directories: bitwuzla_inc,
                                  dependencies: dependencies,
                                  link_with: bitwuzla_lib)

# Generate pkgconfig file.
pkg = import('pkgconfig')
pkg.generate(bitwuzla_lib)

subdir('main')
