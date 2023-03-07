# ---
# Build Bitwuzla binary
# ---

# Build static binary
link_args = []
if build_static and host_machine.system() != 'darwin'
  link_args += ['-static']
endif

bitwuzla_bin = executable('bitwuzla', 'main.cpp',
                          include_directories: include_directories('..'),
                          dependencies: [bitwuzla_dep],
                          link_args: link_args,
                          install: true)
