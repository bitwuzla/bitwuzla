#!/usr/bin/env python3
###
# Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
#
# This file is part of Bitwuzla.
#
# Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
#
# See COPYING for more information on using this software.
##

import argparse
import sys
import subprocess

ap = argparse.ArgumentParser()
ap.add_argument('files', nargs='*')
args = ap.parse_args()

EXCLUDE_FILES = [
    'cmake/targetLinkLibrariesWithDynamicLookup.cmake',
    'cmake/UseCython.cmake',
    'cmake/FindPythonExtensions.cmake',
    'cmake/FindCython.cmake',
    'cmake/CodeCoverage.cmake',
    'contrib/windows_patches/',
    'contrib/smtcomp/',
    'docs/conf.py.in'
]

C_HEADER_TEMPLATE="""/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */
"""

PY_HEADER_TEMPLATE="""###
# Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
#
# This file is part of Bitwuzla.
#
# Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
#
# See COPYING for more information on using this software.
##
"""


def update_header(filename):

    if requires_c_header(filename):
        HEADER_TEMPLATE = C_HEADER_TEMPLATE
    else:
        HEADER_TEMPLATE = PY_HEADER_TEMPLATE

    HEADER_START = HEADER_TEMPLATE.splitlines(keepends=True)[0]
    HEADER_END = HEADER_TEMPLATE.splitlines(keepends=True)[-1]

    status = 'updating'
    new_lines = []
    with open(filename, 'r') as infile:
        lines = infile.readlines()

        if len(lines) == 0:
            print('empty file')
            sys.exit(1)

        idx = 0
        # Check if first line is shebang
        if lines[idx].startswith('#!'):
            new_lines.append(lines[idx])
            idx += 1

        new_lines.extend(HEADER_TEMPLATE.splitlines(keepends=True))

        if lines[idx] != HEADER_START:
            status = 'adding'
            new_lines.extend(lines[idx:])
        else:
            header_end = len(new_lines) - 1
            if lines[header_end] != HEADER_END:
                print(f'Header not found for {filename}')
                sys.exit(1)
            new_lines.extend(lines[header_end+1:])

    if lines != new_lines:
        print(f'{status:9} ... {filename}')
        with open(filename, 'w') as outfile:
            outfile.write(''.join(new_lines))


def requires_c_header(filename):
    suffixes = ('.c', '.h', '.cpp', '.h.in')
    for suffix in suffixes:
        if filename.endswith(suffix):
            return True
    return False


def supported_suffix(filename):
    suffixes = ('.c', '.h', '.cpp', 'CMakeLists.txt', '.py', '.py.in', '.h.in',
                '.pyx', '.pxd', '.cmake', '.sh')
    for suffix in suffixes:
        if filename.endswith(suffix):
            return True
    return False


def main():

    filenames = []
    if args.files:
        filenames = args.files
    else:
        proc = subprocess.run(['git', 'ls-files'], capture_output=True, check=True)
        if proc.stdout:
            filenames = [f.decode() for f in proc.stdout.split()]

    for filename in filenames:

        skip = False
        for exclude in EXCLUDE_FILES:
            if filename.startswith(exclude):
                skip = True
                break

        if skip:
            continue

        if supported_suffix(filename):
            update_header(filename)

if __name__ == '__main__':
    main()
