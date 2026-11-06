# Names of unit tests without test_ prefix and .cpp suffix
unit_tests = [
  ['api',
    [
      'api',
      'capi'
    ]
  ],

  ['backtrack',
    [
      'assertion_stack',
      'object',
      'unordered_map',
      'unordered_set',
      'vector',
      'vector_map'
    ]
  ],

  ['bitblast',
    [
      'aig_bitblaster',
      'aig_manager',
      'aig_cnf'
    ]
  ],

  ['bv',
    [
      'bv',
      'bvdomain',
      'bvdomaingen',
    ]
  ],

  ['fp',
    [
      'fp',
      'fp_eq_ineq',
      'fp_from',
      'fp_chained',
      'fp_unary',
      'fp_binary',
      'fp_binary_rm',
      'fp_ternary',
    ]
  ],

  ['ls/bv',
    [
      'bvnode',
      'bvnodecons',
      'bvnodeinv',
      'bvnodeiscons',
      'bvnodeisess',
      'bvnodeisinv',
      'bvnodeselpath',
      'local_search_bv',
    ]
  ],

  ['node',
    [
      'node',
      'node_manager',
      'node_utils'
    ]
  ],

  ['option',
    [
      'options'
    ]
  ],

  ['parser',
    [
      'btor2_lexer',
      'smt2_lexer',
      'smt2_symbol_table',
    ]
  ],
  ['preprocess',
    [
      'assertion_tracker',
      'pass_elim_lambda',
      'pass_embedded_constraints',
      'pass_normalize',
      'pass_flatten_and',
      'pass_quant',
      'pass_skeleton_preproc',
      'pass_variable_substitution',
      'preprocessor',
    ]
  ],

  ['printer',
    [
      'btor2_printer',
      'smt2_printer'
    ]
  ],

  ['rewrite',
    [
      'evaluator',
      'rewriter_core',
      'rewriter_utils',
      'rewriter_bool',
      'rewriter_bv',
      'rewriter_bv_norm',
      'rewriter_bv_overflow',
      'rewriter_bv_rotate',
      'rewriter_fp',
      'rewriter_array',
    ]
  ],

  ['solver',
    [
      'array_solver',
      'fun_solver',
      'incremental',
      'bv_solver',
      'bv_interpolation_solver',
      'bv_inverter',
      'bv_prop_solver',
      'fp_solver',
      'fp_word_blaster',
    ]
  ],

  ['type',
    [
      'card',
      'type_manager'
    ]
  ],

  ['util',
    [
      'integer',
      'rng',
      'util',
    ]
  ],

]

gtest_dep = dependency('gtest_main', include_type: 'system', required: true)
test_inc = [include_directories('../../src', '../..')]

# Link-time optimization of each unit test would re-optimize the whole library.
# Unit tests link the machine code of the fat LTO objects instead, from a copy
# of the static library without LTO sections, as installed. Linking the
# original library with -fno-lto fails with some binutils versions, since the
# linker loads the LTO plugin on its own and then links the objects that are
# bundled into multiple libraries more than once. -fno-lto is still required
# for the libraries of subprojects.
override_options = []
link_args = []
bitwuzla_test_dep = bitwuzla_dep
if lto_fat_static
  override_options += ['b_lto=false']
  link_args += meson.get_compiler('cpp').get_supported_link_arguments('-fno-lto')
  static_lib = bitwuzla_lib
  if get_option('default_library') == 'both'
    static_lib = bitwuzla_lib.get_static_lib()
  endif
  libname = import('fs').name(static_lib.full_path())
  test_lib = custom_target('nolto-' + libname,
    input: static_lib,
    output: libname,
    command: [find_program('objcopy'),
              '--remove-section=.gnu.lto_*',
              '--remove-section=.gnu.debuglto_*',
              '--remove-section=.llvm.lto',
              '@INPUT@', '@OUTPUT@'])
  # 'dependencies' are the dependencies of bitwuzla_lib (src/meson.build).
  bitwuzla_test_dep = declare_dependency(include_directories: bitwuzla_inc,
                                         dependencies: dependencies,
                                         link_with: test_lib)
endif
test_deps = [gtest_dep, bitwuzla_test_dep, gmp_dep, mpfr_dep]

# Disable wine debug output if we run the cross-compiled binary
env = []
if meson.is_cross_build() and host_machine.system() == 'windows'
  env += ['WINEDEBUG=fixme-all']
endif

# These tests create many short-lived solvers. With MALLOC_PERTURB_, which meson
# sets to a random value, glibc fills each block of a new AIG manager including
# its alignment padding, which takes most of the run time of these tests if
# transparent huge pages are disabled.
no_malloc_perturb_tests = [
  'bitblast_aig_cnf',
  'solver_bv_inverter',
  'solver_bv_prop_solver',
]

cpp_args = ['-fno-access-control', '-DBZLA_ENABLE_UNIT_TESTING']
if cadical_dep.found()
  cpp_args += ['-DBZLA_USE_CADICAL']
endif
if cms_dep.found()
  cpp_args += ['-DBZLA_USE_CMS']
endif
if kissat_dep.found()
  cpp_args += ['-DBZLA_USE_KISSAT']
endif
if gimsatul_dep.found()
  cpp_args += ['-DBZLA_USE_GIMSATUL']
endif
# Unit tests must not include the generated config.h. It is a source of the
# library only, and Meson does not generate the headers of a linked library
# before compiling the tests. It also embeds the git id, which would recompile
# the tests that include it after every commit. The configuration the tests
# depend on is passed as compile definitions instead, see test.h.
if cadical_patched
  cpp_args += ['-DBZLA_CADICAL_PATCHED']
endif
if kissat_patched
  cpp_args += ['-DBZLA_KISSAT_PATCHED']
endif
if is_sat_solver_configured
  cpp_args += ['-DBZLA_IS_SAT_SOLVER_CONFIGURED']
endif
if get_option('fpexp')
  cpp_args += ['-DBZLA_USE_FPEXP']
endif

# The unit test sources are compiled without optimization, which is much
# faster. Most of the run time of the tests is spent in library code, which
# stays optimized.
test_cpp_args = cpp_args + ['-O0']

# The SymFPU reference implementation is only used by unit tests. Compile it
# once instead of for each unit test.
symfpu_test_lib = static_library('symfpu_test',
  '../../src/fp/floating_point_symfpu.cpp',
  dependencies: test_deps,
  include_directories: test_inc,
  cpp_args: cpp_args,
  override_options: override_options)

# Add unit tests
foreach p : unit_tests
  test_subdir = p[0]
  suite = test_subdir.replace('/', '_')
  foreach name : p[1]
    basename = ''.join('test_', name, '.cpp')
    src = join_paths(test_subdir, basename)
    name = '_'.join(suite, name)
    exename = ''.join('test_', name)

    exe = executable(exename, src,
               link_with: symfpu_test_lib,
               dependencies: test_deps,
               include_directories: test_inc,
               cpp_args: test_cpp_args,
               link_args: link_args,
               override_options: override_options)
    test_env = env
    if name in no_malloc_perturb_tests
      test_env += ['MALLOC_PERTURB_=0']
    endif
    test(name, exe, suite: ['unit', suite], timeout: 0, env: test_env)
  endforeach
endforeach
