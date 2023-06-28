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
import re
import subprocess

def get_version():
    major = 0
    minor = 0
    patch = 0
    prerelease = None
    with open('meson.build', 'r') as infile:
        content = infile.read()
        m = re.search(r'  version:\s\'(.*)\',', content)
        if m is None:
            raise ValueError('version string not found in `meson.build`')

        try:
            version, prerelease = m.group(1).split('-', 1)
        except ValueError:
            version, prerelease = m.group(1), None

        version = version.split('.')

        if len(version) != 3:
            raise ValueError('invalid format for version string, ' +
                             'expected `format major.minor.patch[-prerelease]`')
        major, minor, patch = version

    return int(major),int(minor),int(patch),prerelease

def update_version(major, minor, patch, prerelease):
    version = f'{major}.{minor}.{patch}'
    if prerelease:
        version += '-' + prerelease
    with open('meson.build', 'r') as infile:
        content = infile.read()
        content = re.sub(r'  version:\s\'(.*)\'', f'  version: \'{version}\'', content)
    with open('meson.build', 'w') as outfile:
        outfile.write(content)

def create_commit(msg):
    subprocess.check_call(['git', 'commit', 'meson.build', '-m', msg])

def create_git_tag(tag):
    subprocess.check_call(['git', 'tag', tag])

def get_commit_id():
    proc = subprocess.run(['git', 'rev-parse', 'HEAD'],
                          capture_output=True, check=True)
    return proc.stdout.decode().strip()

def print_diff(commit_id):
    subprocess.check_call(['git', 'show', f'{commit_id}..HEAD'])

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('bump', choices=['major', 'minor', 'patch'])
    args = ap.parse_args()

    major, minor, patch, prerelease = get_version()
    commit_id = get_commit_id()

    # Bump specified version
    if args.bump == 'major':
        major, minor, patch = major + 1, 0, 0
    elif args.bump == 'minor':
        minor, patch = minor + 1, 0
    else:
        assert args.bump == 'patch'
        patch = patch + 1

    update_version(major, minor, patch, None)
    create_commit(f'Bump version to {major}.{minor}.{patch}.')
    tag = f'{major}.{minor}.{patch}'
    create_git_tag(tag)
    update_version(major, minor, patch, 'dev')
    create_commit(f'Start post-release version {major}.{minor}.{patch}-{prerelease}.')

    print_diff(commit_id)
    print(f'Push commits and tag with: `git push && git push origin {tag}`')

if __name__ == '__main__':
    main()
