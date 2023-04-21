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

# Get license text
fs = import('fs')
license_text = fs.read(join_paths(meson.project_source_root(),
                                  'COPYING')).strip()
license_text = license_text.replace('\n', '\\\n').replace('"', '\\"')

# Generate header
c_compiler = meson.get_compiler('c')
cpp_compiler = meson.get_compiler('cpp')
conf_data = configuration_data()
conf_data.set('cc', c_compiler.get_id() + ' ' + c_compiler.version())
conf_data.set('cxx', cpp_compiler.get_id() + ' ' + cpp_compiler.version())
conf_data.set('git_id', git_id)
conf_data.set('license', license_text)
conf_data.set('os', build_machine.system())
conf_data.set('version', meson.project_version())
config_h = configure_file(input: 'config.h.in',
               output: 'config.h',
               configuration: conf_data)

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
  'parser/btor2/parser.cpp',
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
  'sat/cadical.cpp',
  'sat/cryptominisat.cpp',
  'sat/kissat.cpp',
  'solver/array/array_solver.cpp',
  'solver/bv/bv_bitblast_solver.cpp',
  'solver/bv/bv_prop_solver.cpp',
  'solver/bv/bv_solver.cpp',
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
  'util/logger.cpp',
  'util/statistics.cpp',
])

# bitwuzla_lib dependencies
gmp_dep = dependency('gmp',
                     version: '>=6.1',
                     required: true,
                     static: build_static)

# Subproject dependencies
cadical_dep = dependency('cadical', required: true)
symfpu_dep = dependency('symfpu', required: true)
bitwuzla_libs_dep = dependency('bitwuzla_libs', required: true)
btor2parser_dep = dependency('btor2parser', required: true)

dependencies = [symfpu_dep, cadical_dep, gmp_dep, bitwuzla_libs_dep, btor2parser_dep]

# Public header include directory
bitwuzla_inc = include_directories('../include')

bitwuzla_lib = library('bitwuzla',
                      sources,
                      include_directories: bitwuzla_inc,
                      dependencies: dependencies,
                      soversion: bitwuzla_lib_soversion,
                      install: true)

# Create library dependency
bitwuzla_dep = declare_dependency(include_directories: bitwuzla_inc,
                                  dependencies: bitwuzla_libs_dep,
                                  link_with: bitwuzla_lib)

# Generate pkgconfig file.
pkg = import('pkgconfig')
pkg.generate(bitwuzla_lib)

subdir('main')
