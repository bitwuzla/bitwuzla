#!/usr/bin/env python3

import argparse
import os
import sys

ap = argparse.ArgumentParser()
ap.add_argument('dirs', nargs='*')
args = ap.parse_args()

HEADER_TEMPLATE="""/**
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2021 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */
"""


def update_header(source_file):
    print(f'Updating file: {source_file}')

    new_lines = [HEADER_TEMPLATE]
    with open(source_file, 'r') as infile:
        lines = infile.readlines()

        if len(lines) == 0:
            print(f'Found empty file: {source_file}')
            sys.exit(1)

        header_start = lines[0]

        if not header_start.startswith('/*'):
            print(f'No header found for {source_file}... Adding new header.')
            new_lines.extend(lines)
        else:
            header_end = 0
            for i, line in enumerate(lines):
                if '#include' in line:
                    break
                if line.endswith('*/\n'):
                    header_end = i
                    break
            if header_end == 0:
                print(f'Header not found for {source_file}')
                sys.exit(1)

            new_lines.extend(lines[header_end+1:])

    with open(source_file, 'w') as outfile:
        outfile.write(''.join(new_lines))



source_files = []
for dir in args.dirs:
    for root, dirs, files in os.walk(dir):
        for file in files:
            if file.endswith('.c') or file.endswith('.h') or file.endswith('.cpp'):
                update_header(os.path.join(root, file))
