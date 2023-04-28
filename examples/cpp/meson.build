examples = [
  'checksatassuming',
  'options',
  'parse',
  'pushpop',
  'quickstart',
  'unsatassumptions',
  'unsatcore',
]

bitwuzla_dep = dependency('bitwuzla')
foreach e : examples
  exe = executable(
    e, ''.join(e, '.cpp'),
    dependencies: [bitwuzla_dep])
    test(e, exe)
endforeach
