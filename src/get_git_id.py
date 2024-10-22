###
# Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
#
# Copyright (C) 2024 by the authors listed in the AUTHORS file at
# https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
#
# This file is part of Bitwuzla under the MIT license. See COPYING for more
# information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
##

import argparse
import os
import subprocess

ap = argparse.ArgumentParser(
    description='Extract git information for a given repository. '
)
ap.add_argument('path', help='the path of the git repository')
args = ap.parse_args()
if not os.path.isdir(args.path):
    raise RuntimeError(f'Directory `{args.path}` does not exist.')

git_id = ''

cmd = ['git', '-C', args.path, 'rev-parse', '--abbrev-ref', 'HEAD']
proc = subprocess.run(cmd, capture_output=True, check=False)
if proc.returncode == 0 and proc.stdout:
    git_id += proc.stdout.decode().strip()
    git_id += '@'
    cmd = ['git', '-C', args.path, 'rev-parse', '--short', 'HEAD']
    proc = subprocess.run(cmd, capture_output=True, check=False)
    git_id += proc.stdout.decode().strip()
    cmd = ['git', '-C', args.path, 'diff-index', '--quiet', 'HEAD']
    proc = subprocess.run(cmd, capture_output=True, check=False)
    if proc.returncode != 0:
        git_id += '-dirty'

print(git_id)
