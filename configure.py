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

# Can be replaced with argparse.BooleanOptionalAction when Python 3.8 is EOL.
def bool_opt(ap, name, help):
    dest = name.replace('-', '_')
    ap.add_argument(f'--{name}', action='store_true',
                    help=f'enable {help}', default=None)
    ap.add_argument(f'--no-{name}', action='store_false', dest=dest,
                    help=f'disable {help}', default=None)

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
    ap.add_argument('-b', '--build-dir', default='build', metavar='DIR',
                    help='build directory')
    ap.add_argument('--prefix',
                    help='install prefix')
    ap.add_argument('--shared', action='store_true',
                    help='shared library')
    ap.add_argument('--static', action='store_true',
                    help='static library')
    bool_opt(ap, 'assertions', 'assertions')
    bool_opt(ap, 'asan', 'address sanitizer')
    bool_opt(ap, 'ubsan', 'undefined behavior sanitizer')
    bool_opt(ap, 'coverage', 'code coverage')
    ap.add_argument('--win64', action='store_true',
                    help='enable cross compilation for 64-bit Windows')
    ap.add_argument('--arm64', action='store_true',
                    help='enable cross compilation for 64-bit ARM')
    bool_opt(ap, 'python', 'python bindings')
    bool_opt(ap, 'testing', 'regression and unit testing')
    bool_opt(ap, 'unit-testing', 'unit testing')
    bool_opt(ap, 'docs', 'documentation')
    ap.add_argument('--wipe', action='store_true',
                    help='delete build directory if it already exists')
    bool_opt(ap, 'kissat', 'Kissat support')
    bool_opt(ap, 'ae_kissat', 'AE_Kissat support')
    bool_opt(ap, 'cryptominisat', 'CryptoMiniSat support')
    bool_opt(ap,
             'fpexp',
             'support for experimental floating-point formats, ' +
             'all formats except Float16, Float32, Float64 and Float128 are ' +
             'considered experimental (due to known issues in SymFPU), use ' +
             'at your own risk')
    bool_opt(ap, 'aiger', 'AIGER support to print AIGs')
    args = ap.parse_args()

    build_opts = []
    sanitize = set()
    if args.buildtype:
        build_opts.append(f'-Dbuildtype={args.buildtype}')
    if args.prefix:
        build_opts.append(f'-Dprefix={args.prefix}')
    if args.shared:
        build_opts.append(f'-Ddefault_library=shared')
    if args.static:
        build_opts.append(f'-Ddefault_library=static')
    if args.asan is not None:
        sanitize.add('address' if args.asan else 'none')
    if args.ubsan is not None:
        if args.ubsan:
            sanitize.add('undefined')
        elif 'address' not in sanitize:
            sanitize.add('none')
    if args.assertions is not None:
        build_opts.append(f'-Db_ndebug={_bool(not args.assertions)}')
    if args.testing is not None:
        build_opts.append(f'-Dtesting={_feat(args.testing)}')
    if args.unit_testing is not None:
        build_opts.append(f'-Dunit_testing={_feat(args.unit_testing)}')
    if args.coverage is not None:
        build_opts.append(f'-Db_coverage={_bool(args.coverage)}')
    if args.win64:
        build_opts.append('--cross-file=x86_64-w64-mingw32.txt')
    if args.arm64:
        build_opts.append('--cross-file=x86_64-linux-aarch64.txt')
    if args.python is not None:
        build_opts.append(f'-Dpython={_bool(args.python)}')
    if args.docs is not None:
        build_opts.append(f'-Ddocs={_bool(args.docs)}')
    if sanitize:
        build_opts.append(f'-Db_sanitize={",".join(sanitize)}')
    if args.wipe and os.path.exists(args.build_dir):
        shutil.rmtree(args.build_dir)
    if args.kissat is not None:
        build_opts.append(f'-Dkissat={_bool(args.kissat)}')
    if args.ae_kissat is not None:
        build_opts.append(f'-Dae_kissat={_bool(args.ae_kissat)}')
    if args.cryptominisat is not None:
        build_opts.append(f'-Dcryptominisat={_bool(args.cryptominisat)}')
    if args.fpexp is not None:
        build_opts.append(f'-Dfpexp={_bool(args.fpexp)}')
    else:
        if args.buildtype and args.buildtype != 'release':
            build_opts.append(f'-Dfpexp=true')
        else:
            build_opts.append(f'-Dfpexp=false')
    if args.aiger is not None:
        build_opts.append(f'-Daiger={_bool(args.aiger)}')

    configure_build(args.build_dir, build_opts)

if __name__ == '__main__':
    main()
