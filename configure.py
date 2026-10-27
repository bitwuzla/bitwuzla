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
import configparser
import os
import subprocess
import shutil
import sys
import tempfile

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

def _cxx(cross_file):
    if cross_file:
        cp = configparser.ConfigParser()
        cp.read(cross_file)
        return cp.get('binaries', 'cpp', fallback='c++').strip('\'"')
    return os.environ.get('CXX', 'c++')

def _lto_supported(cxx):
    # Link-time optimization is only enabled by default if the compiler
    # generates fat objects, which also contain machine code and keep
    # installed static libraries linkable by other compilers, and if the linker
    # supports link-time optimization, e.g., Clang requires the LLVM gold
    # plugin unless linking with LLD.
    cmd = cxx.split() + ['-flto', '-ffat-lto-objects']
    with tempfile.TemporaryDirectory() as tmp:
        src = os.path.join(tmp, 'lto.cpp')
        obj = os.path.join(tmp, 'lto.o')
        with open(src, 'w') as f:
            f.write('int main() { return 0; }\n')
        try:
            if subprocess.run(cmd + ['-c', src, '-o', obj],
                              capture_output=True).returncode != 0:
                return False
            # Clang generates plain bitcode for object formats without fat
            # object support, e.g., Mach-O.
            with open(obj, 'rb') as f:
                if f.read(4) in (b'BC\xc0\xde', b'\xde\xc0\x17\x0b'):
                    return False
            return subprocess.run(cmd + [obj, '-o', os.path.join(tmp, 'lto')],
                                  capture_output=True).returncode == 0
        except OSError:
            return False

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
def bool_opt(ap, name, help, dflt=None):
    dest = name.replace('-', '_')
    ap.add_argument(f'--{name}', action='store_true',
                    help=f'enable {help}', default=dflt)
    ap.add_argument(f'--no-{name}', action='store_false', dest=dest,
                    help=f'disable {help}', default=(not dflt))

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
    ap.add_argument('--extra-libdir', action='append', metavar='DIR',
                    help='additional directory to search for libraries that '
                         'provide no pkg-config file (CaDiCaL, Kissat), '
                         'can be given multiple times')
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
    bool_opt(ap, 'cadical', 'CaDiCaL support', True)
    bool_opt(ap, 'kissat', 'Kissat support')
    bool_opt(ap, 'cryptominisat', 'CryptoMiniSat support')
    bool_opt(ap, 'gimsatul', 'Gimsatul support')
    bool_opt(ap,
             'fpexp',
             'support for experimental floating-point formats, ' +
             'all formats except Float16, Float32, Float64 and Float128 are ' +
             'considered experimental (due to known issues in SymFPU), use ' +
             'at your own risk')
    bool_opt(ap, 'aiger', 'AIGER support to print AIGs')
    bool_opt(ap, 'mimalloc',
             'mimalloc memory allocator for the binary, enabled by default ' +
             'for Linux release builds')
    bool_opt(ap, 'mimalloc-thp',
             'transparent huge pages in mimalloc, enabled by default, ' +
             'disable to reduce memory usage at the cost of performance')
    bool_opt(ap, 'lto',
             'link-time optimization, enabled by default for release builds ' +
             'if supported')
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
    cross_file = None
    if args.win64:
        cross_file = 'x86_64-w64-mingw32.txt'
    if args.arm64:
        cross_file = 'x86_64-linux-aarch64.txt'
    if cross_file:
        build_opts.append(f'--cross-file={cross_file}')
    if args.python is not None:
        build_opts.append(f'-Dpython={_bool(args.python)}')
    if args.docs is not None:
        build_opts.append(f'-Ddocs={_bool(args.docs)}')
    if sanitize:
        build_opts.append(f'-Db_sanitize={",".join(sanitize)}')
    if args.wipe and os.path.exists(args.build_dir):
        shutil.rmtree(args.build_dir)
    if args.cadical is not None:
        build_opts.append(f'-Dcadical={_bool(args.cadical)}')
    if args.kissat is not None:
        build_opts.append(f'-Dkissat={_bool(args.kissat)}')
    if args.cryptominisat is not None:
        build_opts.append(f'-Dcryptominisat={_bool(args.cryptominisat)}')
    if args.gimsatul is not None:
        build_opts.append(f'-Dgimsatul={_bool(args.gimsatul)}')
    if args.fpexp is not None:
        build_opts.append(f'-Dfpexp={_bool(args.fpexp)}')
    else:
        if args.buildtype and args.buildtype != 'release':
            build_opts.append(f'-Dfpexp=true')
        else:
            build_opts.append(f'-Dfpexp=false')
    if args.aiger is not None:
        build_opts.append(f'-Daiger={_bool(args.aiger)}')
    if args.mimalloc is not None:
        build_opts.append(f'-Dmimalloc={_feat(args.mimalloc)}')
    if args.mimalloc_thp is not None:
        build_opts.append(f'-Dmimalloc:thp={_bool(args.mimalloc_thp)}')
    lto = args.lto
    # Without a build type, a new build directory defaults to a release build
    # and an existing one keeps its build type and LTO setting.
    if lto is None and (args.buildtype or not os.path.exists(
            os.path.join(args.build_dir, 'meson-private', 'build.dat'))):
        lto = (args.buildtype in (None, 'release')
               and _lto_supported(_cxx(cross_file)))
    if lto is not None:
        build_opts.append(f'-Db_lto={_bool(lto)}')
    if args.extra_libdir:
        dirs = ','.join(os.path.abspath(d) for d in args.extra_libdir)
        build_opts.append(f'-Dextra_libdirs={dirs}')

    configure_build(args.build_dir, build_opts)

if __name__ == '__main__':
    main()
