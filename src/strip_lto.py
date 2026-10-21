###
# Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
#
# Copyright (C) 2026 by the authors listed in the AUTHORS file at
# https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
#
# This file is part of Bitwuzla under the MIT license. See COPYING for more
# information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
##

# Meson install script that removes the link-time optimization sections of GCC
# and Clang from installed static libraries, which keeps their machine code
# only.

import argparse
import os
import subprocess

ap = argparse.ArgumentParser(
    description='Remove link-time optimization sections from installed ' +
                'static libraries.'
)
ap.add_argument('objcopy', help='the objcopy program')
ap.add_argument('libdir', help='the library installation directory')
ap.add_argument('libs', nargs='+', help='the static libraries in the build '
                                        'directory')
args = ap.parse_args()

if os.path.isabs(args.libdir):
    libdir = os.environ.get('DESTDIR', '') + args.libdir
else:
    libdir = os.path.join(os.environ['MESON_INSTALL_DESTDIR_PREFIX'],
                          args.libdir)

for lib in args.libs:
    path = os.path.join(libdir, os.path.basename(lib))
    # Not installed, e.g., if only a subset of install tags is installed.
    if not os.path.exists(path):
        continue
    subprocess.run([args.objcopy,
                    '--remove-section=.gnu.lto_*',
                    '--remove-section=.gnu.debuglto_*',
                    '--remove-section=.llvm.lto',
                    path],
                   check=True)
