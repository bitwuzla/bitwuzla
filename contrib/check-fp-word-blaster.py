#!/usr/bin/env python3
###
# Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
#
# Copyright (C) 2026 by the authors listed in the AUTHORS file at
# https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
#
# This file is part of Bitwuzla under the MIT license. See COPYING for more
# information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
##

"""
Exhaustively check the word-blasted encodings of floating-point operations
in small formats against the results of constant folding (MPFR).

For each instance, i.e., an operation on a format or a pair of formats, the
script

  1. asks the given Bitwuzla binary for the value of the operation applied
     to every constant input under every rounding mode, which is computed via
     constant folding, and
  2. checks that (distinct (op rm b) table) is unsat, where rm and b are
     symbolic and table is a decision tree over rm and the bits of b with the
     values from 1.

With --self-check, one entry of each table is changed and the query is
expected to be sat, to make sure the check detects incorrect encodings.

The unit test test/unit/solver/test_fp_word_blaster.cpp performs the same
check for smaller formats. Run this script with a build configured with
experimental floating-point formats (-Dfpexp=true) after changing the
patches applied to SymFPU or updating SymFPU, e.g.:

  contrib/check-fp-word-blaster.py build/src/main/bitwuzla
"""

import argparse
import concurrent.futures
import os
import random
import re
import subprocess
import sys
import tempfile
import time

RMS = ['RNE', 'RNA', 'RTP', 'RTN', 'RTZ']


def formats(max_size):
    """All formats of at most max_size bits supported by the word blaster."""
    # SymFPU does not support formats with significand size <= 3 and formats
    # with exponent size 2 and a significand size that is a power of two.
    return [(e, s) for e in range(2, max_size) for s in range(4, max_size)
            if e + s <= max_size and (e > 2 or s & (s - 1) != 0)]


def bv_value(size, value):
    return '#b' + format(value, f'0{size}b')


def parse_sexprs(text):
    stack = [[]]
    for tok in re.findall(r'\(|\)|[^\s()]+', text):
        if tok == '(':
            stack.append([])
        elif tok == ')':
            top = stack.pop()
            stack[-1].append(top)
        else:
            stack[-1].append(tok)
    if len(stack) != 1:
        raise ValueError('unbalanced parentheses')
    return stack[0]


def sexpr_str(sexpr):
    if isinstance(sexpr, list):
        return '(' + ' '.join(sexpr_str(x) for x in sexpr) + ')'
    return sexpr


class Instance:
    """
    An operation instance. For rti and fp2fp, src is the input format,
    for sbv2fp and ubv2fp the size of the bit-vector input.
    """

    def __init__(self, kind, src, dst):
        self.kind = kind
        self.src = src
        self.dst = src if kind == 'rti' else dst

    @property
    def name(self):
        fmt = lambda f: f'{f[0]}_{f[1]}'
        if self.kind == 'rti':
            return f'rti_{fmt(self.src)}'
        if self.kind == 'fp2fp':
            return f'fp2fp_{fmt(self.src)}_to_{fmt(self.dst)}'
        return f'{self.kind}_bv{self.src}_to_{fmt(self.dst)}'

    @property
    def bv_size(self):
        return sum(self.src) if self.kind in ('rti', 'fp2fp') else self.src

    def term(self, rm, b):
        x = b
        if self.kind in ('rti', 'fp2fp'):
            x = f'((_ to_fp {self.src[0]} {self.src[1]}) {b})'
        e, s = self.dst
        if self.kind == 'rti':
            return f'(fp.roundToIntegral {rm} {x})'
        if self.kind == 'ubv2fp':
            return f'((_ to_fp_unsigned {e} {s}) {rm} {x})'
        return f'((_ to_fp {e} {s}) {rm} {x})'


def run(binary, args, smt2, path, timeout):
    with open(path, 'w') as outfile:
        outfile.write(smt2)
    try:
        proc = subprocess.run([binary] + args + [path],
                              capture_output=True,
                              text=True,
                              timeout=timeout)
    except subprocess.TimeoutExpired:
        return 'timeout', ''
    out = proc.stdout + proc.stderr
    if proc.returncode not in (0, 10, 20):
        return f'error({proc.returncode})', out
    return 'ok', out


def compute_values(inst, binary, outdir, timeout):
    """Get {rm: [value of input i]} via constant folding."""
    n = inst.bv_size
    terms = [inst.term(rm, bv_value(n, i)) for rm in RMS for i in range(1 << n)]
    smt2 = ('(set-option :produce-models true)\n(set-logic QF_FP)\n'
            '(check-sat)\n(get-value (' + '\n'.join(terms) + '))\n')
    status, out = run(binary, [], smt2,
                      os.path.join(outdir, inst.name + '.values.smt2'), timeout)
    out = out.strip()
    if status != 'ok' or not out.startswith('sat'):
        raise RuntimeError(f'computing values failed ({status}): {out[-500:]}')
    pairs = parse_sexprs(out[len('sat'):])
    if len(pairs) != 1 or len(pairs[0]) != len(terms):
        raise RuntimeError('unexpected get-value output')
    values = [sexpr_str(p[1]) for p in pairs[0]]
    for v in values:
        if 'to_fp' in v or 'roundToIntegral' in v:
            raise RuntimeError(f'value not constant folded: {v}')
    return {rm: values[k << n:(k + 1) << n] for k, rm in enumerate(RMS)}


def mk_tree(values):
    """Decision tree over the bits of b, collapses equal subtrees."""
    if len(values) == 1:
        return values[0]
    bit = len(values).bit_length() - 2
    half = len(values) // 2
    lo, hi = mk_tree(values[:half]), mk_tree(values[half:])
    if lo == hi:
        return lo
    return f'(ite (= ((_ extract {bit} {bit}) b) #b1) {hi} {lo})'


def mk_query(inst, values):
    table = mk_tree(values[RMS[-1]])
    for rm in reversed(RMS[:-1]):
        table = f'(ite (= rm {rm}) {mk_tree(values[rm])} {table})'
    return ('(set-logic QF_BVFP)\n'
            '(declare-const rm RoundingMode)\n'
            f'(declare-const b (_ BitVec {inst.bv_size}))\n'
            f'(assert (distinct {inst.term("rm", "b")}\n{table}))\n'
            '(check-sat)\n')


def mutate(values, rng):
    """Replace one value by a different value of the same sort."""
    values = {rm: list(v) for rm, v in values.items()}
    candidates = sorted({v for vs in values.values() for v in vs})
    rm = rng.choice(RMS)
    i = rng.randrange(len(values[rm]))
    others = [v for v in candidates if v != values[rm][i]]
    if not others:
        return None
    values[rm][i] = rng.choice(others)
    return values


def check(inst, binary, outdir, timeout, self_check, seed):
    try:
        values = compute_values(inst, binary, outdir, timeout)
    except Exception as e:
        return 'error', str(e)
    # Disable model checking to report incorrect encodings as sat.
    args = ['--check-model=false']
    status, out = run(binary, args, mk_query(inst, values),
                      os.path.join(outdir, inst.name + '.smt2'), timeout)
    if status != 'ok':
        return status, out[-500:]
    result = out.split()[0] if out.split() else ''
    if result == 'unknown' and 'not supported' in out:
        return 'skipped', ''
    if result != 'unsat':
        return 'fail', f'expected unsat, got {result}'
    if self_check:
        mutated = mutate(values, random.Random(seed))
        if mutated is not None:
            status, out = run(binary, args, mk_query(inst, mutated),
                              os.path.join(outdir, inst.name + '.mutated.smt2'),
                              timeout)
            if status != 'ok' or out.split()[:1] != ['sat']:
                return 'fail', f'mutated table not detected: {out[-500:]}'
    return 'pass', ''


def main():
    ap = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawTextHelpFormatter)
    ap.add_argument('binary', help='path to the Bitwuzla binary')
    ap.add_argument('--ops',
                    default='rti,fp2fp,sbv2fp,ubv2fp',
                    help='comma-separated list of operations (default: %(default)s)')
    ap.add_argument('--rti-size', type=int, default=13,
                    help='max. format size for rti (default: %(default)s)')
    ap.add_argument('--src-size', type=int, default=10,
                    help='max. source format size for fp2fp (default: %(default)s)')
    ap.add_argument('--dst-size', type=int, default=13,
                    help='max. target format size for conversions (default: %(default)s)')
    ap.add_argument('--bv-size', type=int, default=10,
                    help='max. bit-vector size for sbv2fp, ubv2fp (default: %(default)s)')
    ap.add_argument('--filter', help='only check instances matching this regex')
    ap.add_argument('--self-check', action='store_true',
                    help='also check that a mutated table is detected')
    ap.add_argument('--jobs', '-j', type=int, default=os.cpu_count(),
                    help='number of parallel jobs (default: %(default)s)')
    ap.add_argument('--timeout', type=float, default=600,
                    help='time limit per query in seconds (default: %(default)s)')
    ap.add_argument('--outdir',
                    help='directory for the generated queries (default: temporary)')
    args = ap.parse_args()

    ops = args.ops.split(',')
    instances = []
    if 'rti' in ops:
        instances += [Instance('rti', f, None) for f in formats(args.rti_size)]
    if 'fp2fp' in ops:
        instances += [Instance('fp2fp', f1, f2)
                      for f1 in formats(args.src_size)
                      for f2 in formats(args.dst_size)]
    for kind in ('sbv2fp', 'ubv2fp'):
        if kind in ops:
            instances += [Instance(kind, size, f)
                          for size in range(1, args.bv_size + 1)
                          for f in formats(args.dst_size)]
    if args.filter:
        instances = [i for i in instances if re.search(args.filter, i.name)]
    # Start with the largest instances for better load balancing.
    instances.sort(key=lambda i: -i.bv_size)

    outdir = args.outdir or tempfile.mkdtemp(prefix='check-fp-word-blaster-')
    os.makedirs(outdir, exist_ok=True)
    print(f'checking {len(instances)} instances, queries in {outdir}', flush=True)

    counts = {}
    start = time.time()
    with concurrent.futures.ThreadPoolExecutor(args.jobs) as executor:
        futures = {
            executor.submit(check, inst, args.binary, outdir, args.timeout,
                            args.self_check, k): inst
            for k, inst in enumerate(instances)
        }
        for k, future in enumerate(concurrent.futures.as_completed(futures), 1):
            inst = futures[future]
            status, msg = future.result()
            counts[status] = counts.get(status, 0) + 1
            if status not in ('pass', 'skipped'):
                print(f'{status}: {inst.name}: {msg.strip()}', flush=True)
            if k % 100 == 0:
                print(f'[{k}/{len(instances)}] {counts}', flush=True)
    print(f'{len(instances)} instances in {time.time() - start:.0f}s: {counts}')
    return 0 if set(counts) <= {'pass', 'skipped'} else 1


if __name__ == '__main__':
    sys.exit(main())
