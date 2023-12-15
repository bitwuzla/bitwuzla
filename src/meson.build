c_compiler = meson.get_compiler('c')
cpp_compiler = meson.get_compiler('cpp')

# ---
# Bitwuzla library dependencies
# ---

# External dependencies
gmp_dep = dependency('gmp',
                     version: '>=6.1',
                     required: true,
                     static: build_static)


# Subproject dependencies

# CaDiCaL does not provide pkg-config to find dependency
cadical_dep = cpp_compiler.find_library('cadical',
                                        has_headers: 'cadical.hpp',
                                        static: build_static,
                                        required: false)
if not cadical_dep.found()
  cadical_dep = dependency('cadical', required: true)
endif

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

dependencies = [symfpu_dep, cadical_dep, kissat_dep, gmp_dep]

cpp_args = []
if kissat_dep.found()
  cpp_args += ['-DBZLA_USE_KISSAT']
endif

# ---
# Generate config.h
# ---

# Get git information
git = find_program('git')
git_id = ''
if git.found()
  repo = meson.project_source_root()
  r = run_command(git, '-C', repo, 'rev-parse', '--abbrev-ref', 'HEAD',
                  check: false)
  if r.returncode() == 0
    git_id += r.stdout().strip()
    git_id += '@'
    r = run_command(git, '-C', repo, 'rev-parse', 'HEAD', check: false)
    git_id += r.stdout().strip()
    r = run_command(git, '-C', repo, 'diff-index', '--quiet', 'HEAD',
                    check: false)
    if r.returncode() != 0
      git_id += '-dirty'
    endif
  endif
endif

# Generate license text
fs = import('fs')
license_text = fs.read(join_paths(meson.project_source_root(),
                                  'COPYING')).strip()
license_text += '''\n\n
This version of Bitwuzla is linked against the following
third party libraries. For copyright information of each
library see the corresponding url.'''
license_text += '\n\n  CaDiCaL\n  https://github.com/arminbiere/cadical'
license_text += \
  '\n\n  GMP - GNU Multiple Precision Arithmetic Library\n  https://gmplib.org'
if kissat_dep.found()
  license_text += '\n\n  Kissat\n  https://github.com/arminbiere/kissat'
endif
license_text += '\n\n  SymFPU\n  https://github.com/martin-cs/symfpu'
license_text = license_text.replace('\n', '\\n').replace('"', '\\"')

# Generate header
conf_data = configuration_data()
conf_data.set('cc', c_compiler.get_id() + ' ' + c_compiler.version())
conf_data.set('cxx', cpp_compiler.get_id() + ' ' + cpp_compiler.version())
conf_data.set('git_id', git_id)
conf_data.set('license', license_text)
conf_data.set('os', build_machine.system())
conf_data.set('version', meson.project_version())
conf_data.set('is_debug_build', (get_option('buildtype') == 'debug').to_string())
config_h = configure_file(input: 'config.h.in',
               output: 'config.h',
               configuration: conf_data)

# ---
# Util library used by support and bitwuzla library
# ---

sources_util = files([
  'util/hash_pair.cpp',
  'util/logger.cpp',
  'util/resources.cpp',
  'util/statistics.cpp',
])
util_lib = static_library('bzlautil', sources_util)

# ---
# Add Bitwuzla support libraries
# ---

subdir('lib')
support_libs = [bitblast_lib, bitvector_lib, local_search_lib]

# ---
# Build Bitwuzla library
# ---

sources = files([
  'api/c/bitwuzla.cpp',
  'api/c/parser.cpp',
  'api/checks.cpp',
  'api/cpp/bitwuzla.cpp',
  'api/cpp/parser.cpp',
  'backtrack/assertion_stack.cpp',
  'backtrack/backtrackable.cpp',
  'check/check_model.cpp',
  'check/check_unsat_core.cpp',
  'env.cpp',
  'node/kind_info.cpp',
  'node/node.cpp',
  'node/node_data.cpp',
  'node/node_kind.cpp',
  'node/node_manager.cpp',
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
  'preprocess/pass/elim_uninterpreted.cpp',
  'preprocess/pass/embedded_constraints.cpp',
  'preprocess/pass/flatten_and.cpp',
  'preprocess/pass/normalize.cpp',
  'preprocess/pass/rewrite.cpp',
  'preprocess/pass/skeleton_preproc.cpp',
  'preprocess/pass/variable_substitution.cpp',
  'preprocess/preprocessing_pass.cpp',
  'preprocess/preprocessor.cpp',
  'printer/printer.cpp',
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
  'solver/bv/bv_bitblast_solver.cpp',
  'solver/bv/bv_prop_solver.cpp',
  'solver/bv/bv_solver.cpp',
  'solver/bv/aig_bitblaster.cpp',
  'solver/fp/floating_point.cpp',
  'solver/fp/fp_solver.cpp',
  'solver/fp/rounding_mode.cpp',
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

compiler = meson.get_compiler('cpp')
if compiler.has_function('getrusage', prefix: '#include <sys/resource.h>')
  cpp_args += ['-DHAVE_RUSAGE']
endif

# Public header include directory
bitwuzla_inc = include_directories('../include', 'lib')

bitwuzla_lib = library('bitwuzla',
                      sources,
                      include_directories: bitwuzla_inc,
                      link_with: [support_libs, util_lib],
                      dependencies: dependencies,
                      soversion: bitwuzla_lib_soversion,
                      install_rpath: install_rpath,
                      install: true,
                      cpp_args: cpp_args)

# Create library dependency
bitwuzla_dep = declare_dependency(include_directories: bitwuzla_inc,
                                  link_with: [bitwuzla_lib, support_libs])

# Generate pkgconfig file.
pkg = import('pkgconfig')
pkg.generate(bitwuzla_lib)

subdir('main')
