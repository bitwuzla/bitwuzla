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
import os
import subprocess
import sys

def check(expected, out, err, output_dir):
    out = out.decode()
    err = err.decode()
    if err:
        try:
            pos = err.index('log/')
            err = err[pos:]
        except ValueError:
            pass
    cmp = '{}{}'.format(out, err)
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
    ap.add_argument('--check-output', action='store_true', default=False)
    args = ap.parse_args()

    bzla_args = args.testcase.split()
    cmd_args = [args.binary]
    cmd_args.extend(bzla_args)

    testname, _ = os.path.splitext(bzla_args[0])
    outfilename = '{}.out'.format(testname)
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
    else:
        assert args.check_output
        with open(outfilename, 'r') as outfile:
            expected = outfile.read()
    check(expected, out, err, args.output_dir)


if __name__ == '__main__':
    main()
