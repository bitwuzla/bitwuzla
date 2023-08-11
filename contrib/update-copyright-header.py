#!/usr/bin/env python3
###
# Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
#
# Copyright (C) 2021 by the authors listed in the AUTHORS file at
# https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
#
# This file is part of Bitwuzla under the MIT license. See COPYING for more
# information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
##

import argparse
import datetime
import subprocess
import sys

ap = argparse.ArgumentParser()
ap.add_argument('files', nargs='*')
args = ap.parse_args()

EXCLUDE_FILES = [
    'docs/conf.py.in'
]

C_HEADER_TEMPLATE="""/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) {year} by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */
"""

PY_HEADER_TEMPLATE ="""###
# Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
#
# Copyright (C) {year} by the authors listed in the AUTHORS file at
# https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
#
# This file is part of Bitwuzla under the MIT license. See COPYING for more
# information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
##
"""

def get_year(filename):
    cmd = ['git', 'log', '--follow', '--format=%ad', '--date=format:%Y',
           filename]
    proc = subprocess.run(cmd, capture_output=True, check=True)
    if not proc.stdout:
        return datetime.date.today().year
    return proc.stdout.split()[-1].decode()

def update_header(filename):

    year = get_year(filename)
    if requires_c_header(filename):
        HEADER_TEMPLATE = C_HEADER_TEMPLATE.format(year=year)
    else:
        HEADER_TEMPLATE = PY_HEADER_TEMPLATE.format(year=year)

    HEADER_START = HEADER_TEMPLATE.splitlines(keepends=True)[0]
    HEADER_END = HEADER_TEMPLATE.splitlines(keepends=True)[-1]

    status = 'updating'
    new_lines = []
    end_of_header = None
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
        end_of_header = len(new_lines)

        if lines[idx] != HEADER_START:
            status = 'adding'
            new_lines.extend(lines[idx:])
        else:
            header_end = len(new_lines) - 1
            if lines[header_end] != HEADER_END:
                print(f'Header not found for {filename}')
                sys.exit(1)
            new_lines.extend(lines[header_end+1:])

    # Only add newline after header if there is none
    if new_lines[end_of_header] != '\n':
        new_lines.insert(end_of_header, '\n')

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
    suffixes = ('.c', '.h', '.cpp', '.py', '.py.in', '.h.in',
                '.pyx', '.pxd', '.sh')
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
