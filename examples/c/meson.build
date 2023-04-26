examples = [
  'checksatassuming',
  'options',
  'pushpop',
  'quickstart',
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
