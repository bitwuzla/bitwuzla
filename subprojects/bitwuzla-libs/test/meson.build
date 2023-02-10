unit_tests = [
  ['bitblast',
    [
      'aig_bitblaster',
      'aig_manager',
      'aig_cnf'
    ]
  ],

  ['bitvector',
    ['bv']
  ],

  ['ls/bv',
    [
      'bvdomain',
      'bvdomaingen',
      'bvnode',
      'bvnodecons',
      'bvnodeinv',
      'bvnodeiscons',
      'bvnodeisess',
      'bvnodeisinv',
      'bvnodeselpath',
      'local_search_bv',
      'normalize'
      ]
  ]
]

gtest_dep = dependency('gtest_main', required: true)
test_inc = include_directories('../src')
test_deps = [gtest_dep, bitwuzla_bb_dep, bitwuzla_bv_dep, bitwuzla_ls_dep]

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
               dependencies: test_deps,
               include_directories: test_inc,
               cpp_args: ['-fno-access-control'])
    test(name, exe, suite: suite, timeout: 0)
  endforeach
endforeach
