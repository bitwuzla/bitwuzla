examples = [
  'checksatassuming',
  'option_info',
  'options',
  'parse',
  'print',
  'pushpop',
  'quickstart',
  'reset',
  'reset_assertions',
  'terminator',
  'unsatassumptions',
  'unsatcore',
]

bitwuzla_dep = dependency('bitwuzla')
foreach e : examples
  exe = executable(
    e, ''.join(e, '.c'),
    link_args: ['-lstdc++', '-lm'],
    dependencies: [bitwuzla_dep])
    test(e, exe)
endforeach
