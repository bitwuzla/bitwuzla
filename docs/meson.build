doxygen = find_program('doxygen', required: true)
python = import('python').find_installation()
sphinx_build = find_program('sphinx-build', required: true)

# Check required Python modules
required_python_modules = ['breathe', 'sphinxcontrib.bibtex', 'sphinx_tabs.tabs']
foreach module : required_python_modules
  if run_command([python, '-c', 'import ' + module], check: false).returncode() != 0
    error('Python module `' + module + '` not found. Skipping c/c++ documentation')
  endif
endforeach

subdir('c')
subdir('cpp')

conf_data = configuration_data()
conf_data.set('bitwuzla_python_dir', join_paths(meson.project_build_root(), 'src', 'api', 'python'))
conf_data.set('current_source_dir', meson.current_source_dir())
conf_data.set('current_build_dir', meson.current_build_dir())
conf_data.set('version', meson.project_version())
conf_py = configure_file(input: 'conf.py.in',
               output: 'conf.py',
               configuration: conf_data)

depends = [docs_doxygen_c, docs_doxygen_cpp]
depend_files = ['index.rst']
if get_option('python')
  depends += [bitwuzla_py_ext]
  depend_files += ['python/api.rst', 'python/interface.rst']
endif

docs_usage = custom_target('cli-usage',
  build_by_default: true,
  build_always_stale: true,
  capture: true,
  output: 'cli_usage.txt',
  command: [bitwuzla_bin, '-h'],
  depends: bitwuzla_bin,
)
depends += [docs_usage]

docs_html = custom_target('docs-html',
  #  build_by_default: true,
  build_always_stale: true,
  command: [sphinx_build, '-b', 'html',
            # Tell breathe where to find the Doxygen output
            '-Dbreathe_projects.Bitwuzla_c=' + docs_doxygen_c.full_path(),
            '-Dbreathe_projects.Bitwuzla_cpp=' + docs_doxygen_cpp.full_path(),
            '-Dbreathe_projects.std=' + docs_doxygen_cpp.full_path(),
            # Tell sphinx where to find conf.py
            '-c', meson.current_build_dir(),
            meson.current_source_dir(), meson.current_build_dir()
           ],
  output: '.',
  depends: depends,
  depend_files: depend_files
)

jekyll_fix = files('jekyll_fix.py')
docs = custom_target('docs',
  build_by_default: true,
  build_always_stale: true,
  command: [python, jekyll_fix, meson.current_build_dir()],
  depends: docs_html,
  output: 'jekyll-fix-fake-output'
)
