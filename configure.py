#!/usr/bin/env python3
###
# Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
#
# Copyright (C) 2023 by the authors listed in the AUTHORS file at
# https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
#
# This file is part of Bitwuzla under the MIT license. See COPYING for more
# information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
##

import argparse
import os
import subprocess
import shutil
import sys

def info(msg):
    print(f'-- {msg}')

def die(msg):
    sys.exit(f'** configure.py: {msg}')

def configure_build(builddir, opts):
    cmd = ['meson']
    if os.path.exists(os.path.join(builddir, 'meson-private', 'build.dat')):
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
    info(f'compile Bitwuzla with: cd {builddir} && meson compile')

def _feat(val):
    if val is None:
        return 'auto'
    if val:
        return 'enabled'
    return 'disabled'

def _bool(val):
    assert isinstance(val, bool)
    if val:
        return 'true'
    return 'false'


def main():
    if not os.path.exists('src/main/main.cpp'):
        die('not called from Bitwuzla base directory')

    if shutil.which('meson') is None:
        die('meson not found on system, please install via pip.')

    ap = argparse.ArgumentParser(
        formatter_class=argparse.ArgumentDefaultsHelpFormatter
    )
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
    ap.add_argument('--assertions', action='store_true', default=None,
                    help='enable assertions')
    ap.add_argument('--no-assertions', action='store_false',
                    dest='assertions', help='disable assertions')
    ap.add_argument('--asan', action='store_true',
                    help='enable address sanitizer')
    ap.add_argument('--ubsan', action='store_true',
                    help='enable undefined behavior sanitizer')
    ap.add_argument('--coverage', action='store_true',
                    help='enable code coverage')
    ap.add_argument('--win64', action='store_true',
                    help='enable cross compilation for 64-bit Windows')
    ap.add_argument('--python', action='store_true',
                    help='build python bindings')
    ap.add_argument('--testing', action='store_true', default=None,
                    help='enable regression and unit testing')
    ap.add_argument('--no-testing', action='store_false', dest='testing',
                    help='disable regression and unit testing')
    ap.add_argument('--unit-testing', action='store_true', default=None,
                    help='enable unit testing')
    ap.add_argument('--no-unit-testing', action='store_false',
                    dest='unit_testing', help='disable unit testing')
    ap.add_argument('--docs', action='store_true',
                    help='build documentation')
    ap.add_argument('--wipe', action='store_true',
                    help='delete build directory if it already exists')
    ap.add_argument('--kissat', action='store_true',
                    help='compile with Kissat')
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
        build_opts.append(f'-Db_ndebug={_bool(not args.assertions)}')
    if args.testing is not None:
        build_opts.append(f'-Dtesting={_feat(args.testing)}')
    if args.unit_testing is not None:
        build_opts.append(f'-Dunit_testing={_feat(args.unit_testing)}')
    if args.coverage:
        build_opts.append('-Db_coverage=true')
    if args.win64:
        build_opts.append('--cross-file=x86_64-w64-mingw32.txt')
    if args.python:
        build_opts.append('-Dpython=true')
    if args.docs:
        build_opts.append('-Ddocs=true')
    if sanitize:
        build_opts.append(f'-Db_sanitize={",".join(sanitize)}')
    if args.wipe and os.path.exists(args.build_dir):
        shutil.rmtree(args.build_dir)
    if args.kissat:
        build_opts.append('-Dkissat=true')

    configure_build(args.build_dir, build_opts)

if __name__ == '__main__':
    main()
