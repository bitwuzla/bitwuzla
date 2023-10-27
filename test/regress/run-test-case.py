#!/usr/bin/env python3
###
# Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
#
# Copyright (C) 2020 by the authors listed in the AUTHORS file at
# https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
#
# This file is part of Bitwuzla under the MIT license. See COPYING for more
# information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
##

import argparse
import os
import subprocess
import sys

def check(testfile, expected, out, err, output_dir):
    out = out.decode()
    err = err.decode()
    if err:
        try:
            pos = err.index('regress/')
            err = err[pos:]
        except ValueError:
            pass

    # Remove \r from output of cross-compiled Windows binaries
    if out:
        out = out.replace('\r', '')

    cmp = '{}{}'.format(out, err)
    if not expected:
        n_check_sat = 0
        n_status = 0
        with open(testfile, 'r') as infile:
            for line in infile:
                line = line.strip()
                if line.startswith("(set-info :status"):
                    n_status += 1
                    l = line.split()[-1][:-1].strip()
                    assert l == "sat" or l == "unsat"
                    expected = l if not expected else expected + l
                    expected += "\n"
                elif line.startswith("(check-sat"):
                    n_check_sat += 1
        assert n_check_sat == n_status

    if expected.strip() != cmp.strip():
        print("Expected:\n{}".format(expected.encode()), file=sys.stderr)
        print('-' * 80, file=sys.stderr)
        outfile_name = os.path.join(output_dir, 'expected.log')
        print("see {}".format(outfile_name), file=sys.stderr)
        print('-' * 80, file=sys.stderr)
        outfile = open(outfile_name, 'w')
        outfile.write(expected)
        outfile.close()
        print('=' * 80, file=sys.stderr)
        print("Got:\n{}".format(cmp.encode()), file=sys.stderr)
        print('-' * 80, file=sys.stderr)
        outfile_name = os.path.join(output_dir, 'got.log')
        print("see {}".format(outfile_name), file=sys.stderr)
        print('-' * 80, file=sys.stderr)
        outfile = open(outfile_name, 'w')
        outfile.write(cmp)
        outfile.close()
        sys.exit(1)


def main():
    #print(sys.argv)
    ap = argparse.ArgumentParser()
    ap.add_argument('binary')
    ap.add_argument('testcase')
    ap.add_argument('output_dir')
    ap.add_argument('--check-sat', action='store_true', default=False)
    ap.add_argument('--check-unsat', action='store_true', default=False)
    args = ap.parse_args()

    bzla_args = args.testcase.split()
    cmd_args = [args.binary]
    cmd_args.extend(bzla_args)

    testname, _ = os.path.splitext(bzla_args[0])
    outfilename = '{}.expect'.format(testname)
    #print(outfilename)
    #print(bzla_args)

    print("Running test case '{}'".format(' '.join(cmd_args)))

    proc = subprocess.Popen(cmd_args,
                            stdin=subprocess.PIPE,
                            stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE)

    out, err = proc.communicate()

    expected = None
    if args.check_sat:
        expected = 'sat'
    elif args.check_unsat:
        expected = 'unsat'
    if os.path.exists(outfilename):
        with open(outfilename, 'r') as outfile:
            expected = outfile.read()
    check(bzla_args[0], expected, out, err, args.output_dir)


if __name__ == '__main__':
    main()
