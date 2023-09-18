project('gmp',
  'c',
  version: '6.3.0',
  license: ['LGPL-3.0-only', 'GPL-2.0-only']
)

mod = import('unstable-external_project')

cc = meson.get_compiler('c')
host = run_command(cc, '-dumpmachine',
                   capture: true, check: true).stdout().strip()

p = mod.add_project('configure',
  configure_options: [
        '--prefix=@PREFIX@',
        '--libdir=@PREFIX@/@LIBDIR@',
        '--includedir=@PREFIX@/@INCLUDEDIR@',
        '--with-pic',
        '--enable-cxx'
  ],
  cross_configure_options: [
    '--host=' + host
  ]
)

gmp_dep = p.dependency('gmp')
