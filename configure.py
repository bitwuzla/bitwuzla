#!/usr/bin/env python3

import argparse
import os
import subprocess
import sys

def info(msg):
    print(f'-- {msg}')

def die(msg):
    sys.exit(f'** configure.py: {msg}')

def configure_build(builddir, opts):
    cmd = ['meson']
    if os.path.exists(os.path.join(builddir, 'meson-private')):
        cmd.append('configure')
        if not opts:
            info(f'{builddir} already up-to-date')
            sys.exit(0)
    else:
        cmd.append('setup')
    cmd.append(builddir)
    cmd.extend(opts)
    info(' '.join(cmd))
    subprocess.run(cmd)

def _feat(val):
    if val is None:
        return 'auto'
    if val:
        return 'enabled'
    return 'disabled'

def _bool(val):
    assert val is bool
    if val:
        return 'true'
    return 'false'


def main():
    if not os.path.exists('src/main/main.cpp'):
        die('not called from Bitwuzla base directory')

    ap = argparse.ArgumentParser()
    ap.add_argument('buildtype', nargs='?',
                    choices=['release', 'debug', 'debugoptimized'])
    ap.add_argument('--build-dir', default='build', metavar='DIR',
                    help='build directory')
    ap.add_argument('--prefix',
                    help='install prefix')
    ap.add_argument('--shared', action='store_true',
                    help='shared library')
    ap.add_argument('--static', action='store_true',
                    help='static library')
    ap.add_argument('--assertions', action=argparse.BooleanOptionalAction,
                    help='enable/disable assertions')
    ap.add_argument('--asan', action='store_true',
                    help='enable address sanitizer')
    ap.add_argument('--ubsan', action='store_true',
                    help='enable undefined behavior sanitizer')
    ap.add_argument('--coverage', action='store_true',
                    help='enable code coverage')
    ap.add_argument('--python', action='store_true',
                    help='build python bindings')
    ap.add_argument('--testing', action=argparse.BooleanOptionalAction,
                    help='regression and unit testing')
    ap.add_argument('--unit-testing', action=argparse.BooleanOptionalAction,
                    help='unit testing')
    ap.add_argument('--docs', action='store_true',
                    help='build documentation')
    args = ap.parse_args()

    build_opts = []
    sanitize = []
    if args.buildtype:
        build_opts.append(f'-Dbuildtype={args.buildtype}')
    if args.prefix:
        build_opts.append(f'-Dprefix={args.prefix}')
    if args.shared:
        build_opts.append(f'-Ddefault_library=shared')
    if args.static:
        build_opts.append(f'-Ddefault_library=static')
    if args.asan:
        sanitize.append('address')
    if args.ubsan:
        sanitize.append('undefined')
    if args.assertions is not None:
        build_opts.append(f'-Db_ndebug={_bool(args.assertions)}')
    if args.testing is not None:
        build_opts.append(f'-Dtesting={_feat(args.testing)}')
    if args.unit_testing is not None:
        build_opts.append(f'-Dtesting={_feat(args.unit_testing)}')
    if args.coverage:
        build_opts.append('-Db_coverage=true')
    if args.python:
        build_opts.append('-Dpython=true')
    if args.docs:
        build_opts.append('-Ddocumentation=true')

    if sanitize:
        build_opts.append(f'-Db_sanitize={",".join(sanitize)}')

    configure_build(args.build_dir, build_opts)

if __name__ == '__main__':
    main()
