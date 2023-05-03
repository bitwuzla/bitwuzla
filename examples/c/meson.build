examples = [
  'checksatassuming',
  'options',
  'parse',
  'pushpop',
  'quickstart',
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
