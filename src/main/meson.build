# ---
# Build Bitwuzla binary
# ---

# Build static binary if the toolchain provides static system libraries (e.g.,
# libc.a), otherwise link the binary dynamically against the static libraries.
link_args = []
if build_static and host_machine.system() != 'darwin'
  if cpp_compiler.links('int main() { return 0; }',
                        args: ['-static'],
                        name: 'static executable')
    link_args += ['-static']
  else
    warning('Toolchain does not support static executables, ' +
            'linking Bitwuzla binary dynamically')
  endif
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
                          cpp_args: cpp_args,
                          install_rpath: install_rpath,
                          install: true)
