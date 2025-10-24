examples = [
  'checksatassuming',
  'interpolants',
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
    e, ''.join(e, '.cpp'),
    dependencies: [bitwuzla_dep],
    implicit_include_directories: false)
    test(e, exe, suite: 'cpp')
endforeach
