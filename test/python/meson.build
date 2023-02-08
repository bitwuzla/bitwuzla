pytest = find_program('pytest')

if pytest.found()
  tests = ['test_api']

  fs = import('fs')
  env = ['PYTHONPATH=' + fs.parent(bitwuzla_py_ext.full_path())]
  foreach t : tests
    file = t + '.py'
    args = [join_paths(meson.current_source_dir(), file)]
    test(t, pytest, args: args, suite: 'python', env: env)
  endforeach
else
  warning('pytest not found, disabling python unit tests')
endif
