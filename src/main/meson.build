# ---
# Build Bitwuzla binary
# ---

# Build static binary
link_args = []
if build_static and host_machine.system() != 'darwin'
  link_args += ['-static']
endif

sources = ['main.cpp', 'options.cpp', 'time_limit.cpp']

mimalloc_dep = []
if get_option('mimalloc')
  mimalloc_dep = dependency('mimalloc-static', include_type: 'system')
endif

thread_dep = dependency('threads')

bitwuzla_bin = executable('bitwuzla', sources,
                          include_directories: include_directories('..'),
                          dependencies: [mimalloc_dep, bitwuzla_dep, thread_dep],
                          link_args: link_args,
                          install_rpath: install_rpath,
                          install: true)
