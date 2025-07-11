project('mpfr',
  'c',
  version: '4.2.2',
  license: ['LGPL-3.0-only']
)

mod = import('unstable-external_project')

host_compiler = meson.get_compiler('c', native: false)
build_compiler = meson.get_compiler('c', native: true)

host = run_command(host_compiler, '-dumpmachine',
                   capture: true, check: true).stdout().strip()
build = run_command(build_compiler, '-dumpmachine',
                   capture: true, check: true).stdout().strip()

configure_options = [
  '--prefix=@PREFIX@',
  '--libdir=@PREFIX@/@LIBDIR@',
  '--includedir=@PREFIX@/@INCLUDEDIR@',
  '--enable-static',
  '--disable-shared',
  '--with-pic',
  '--enable-cxx'
]

if get_option('with_gmp') != ''
  configure_options += ['--with-gmp=' + get_option('with_gmp')]
endif

env = environment()
p = mod.add_project('configure',
  configure_options: configure_options,
  cross_configure_options: [
    '--host=' + host,
    '--build=' + build
  ],
  env: env
)

mpfr_dep = p.dependency('mpfr')
