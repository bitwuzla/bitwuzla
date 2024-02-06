python = import('python').find_installation()

if python_path != ''
  tests = [
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
    'unsatcore'
    ]

  fs = import('fs')
  env = ['PYTHONPATH=' + python_path]
  foreach t : tests
    file = t + '.py'
    args = [join_paths(meson.current_source_dir(), file)]
    test(t, python, args: args, suite: 'python', env: env)
  endforeach
else
  warning('Python not found, disabling Python examples')
endif

