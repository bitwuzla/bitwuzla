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

docs_dir = f'{args.output}-gh'
# Delete directory if it already exists
if os.path.exists(docs_dir):
    print(f'[jekyll-fix] delete {docs_dir}')
    shutil.rmtree(docs_dir)
# Copy directory
print(f'[jekyll-fix] copy {args.output} to {docs_dir}')
src = shutil.copytree(args.output, docs_dir)

# Rename _static to static since Jekyll ignores directory with _ prefix.
src = os.path.join(docs_dir, '_static')
dst = os.path.join(docs_dir, 'static')
if os.path.exists(src):
    if os.path.exists(dst):
        shutil.rmtree(dst)
    print(f'[jekyll-fix] rename {src} to {dst}')
    os.rename(src, dst)
if not os.path.exists(dst):
    raise RuntimeError(f'Directory `{dst}` not found after rename.')

# Rename static/sphinx_javascript_frameworks_compat.js to
# static/sphinx_javascript_frameworks_compat.js
src = os.path.join(dst, '_sphinx_javascript_frameworks_compat.js')
dst = os.path.join(dst, 'sphinx_javascript_frameworks_compat.js')
if os.path.exists(src):
    if os.path.exists(dst):
        shutil.rmtree(dst)
    print(f'[jekyll-fix] rename {src} to {dst}')
    os.rename(src, dst)
if not os.path.exists(dst):
    raise RuntimeError(f'File `{dst}` not found after rename.')


# Delete _sources
src = os.path.join(docs_dir, '_sources')
if os.path.exists(src):
    print(f'[jekyll-fix] delete {src}')
    shutil.rmtree(src)
# Delete conf.py
src = os.path.join(docs_dir, 'conf.py')
if os.path.exists(src):
    print(f'[jekyll-fix] delete {src}')
    os.remove(src)
# Delete objects.inv
src = os.path.join(docs_dir, 'objects.inv')
if os.path.exists(src):
    print(f'[jekyll-fix] delete {src}')
    os.remove(src)
# Delete c/Doxyfile
src = os.path.join(docs_dir, 'c/Doxyfile')
if os.path.exists(src):
    print(f'[jekyll-fix] delete {src}')
    os.remove(src)
# Delete c/xml
src = os.path.join(docs_dir, 'c/xml')
if os.path.exists(src):
    print(f'[jekyll-fix] delete {src}')
    shutil.rmtree(src)
# Delete cpp/Doxyfile
src = os.path.join(docs_dir, 'cpp/Doxyfile')
if os.path.exists(src):
    print(f'[jekyll-fix] delete {src}')
    os.remove(src)
# Delete cpp/xml
src = os.path.join(docs_dir, 'cpp/xml')
if os.path.exists(src):
    print(f'[jekyll-fix] delete {src}')
    shutil.rmtree(src)

# Rename _static to static and _sphinx_javascript_frameworks_compat.js to
# sphinx_javascript_frameworks_compat.js in all documentation files
print(f'[jekyll-fix] rename "_static" and ' +
       '"_sphinx_javascript_frameworks_compat.js" in files')
for root, dirs, files in os.walk(docs_dir):
    for file in files:
        if not file.endswith('.html'):
            continue
        filename = os.path.join(root, file)
        with open(filename, 'r+') as file:
            contents = file.read()
            file.seek(0)
            file.write(contents.replace('_static', 'static').
                replace(
                    '_sphinx_javascript_frameworks_compat.js',
                    'sphinx_javascript_frameworks_compat.js'))
            file.truncate()
