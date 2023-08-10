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
import shutil

ap = argparse.ArgumentParser()
ap.add_argument('output')
args = ap.parse_args()

if not os.path.isdir(args.output):
    raise RuntimeError(f'Directory `{args.output}` does not exist.')

# Rename _static to static since Jekyll ignores directory with _ prefix.
src = os.path.join(args.output, '_static')
dst = os.path.join(args.output, 'static')
if os.path.exists(src):
    if os.path.exists(dst):
        shutil.rmtree(dst)
    os.rename(src, dst)

if not os.path.exists(dst):
    raise RuntimeError(f'Directory `{dst}` not found after rename.')

# Rename _static to static in all documentation files
for root, dirs, files in os.walk(args.output):
    for file in files:
        if not file.endswith('.html'):
            continue
        with open(os.path.join(root, file), 'r+') as file:
            contents = file.read()
            file.seek(0)
            file.write(contents.replace('_static', 'static'))
            file.truncate()
