###
# Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
#
# Copyright (C) 2023 by the authors listed in the AUTHORS file at
# https:#github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
#
# This file is part of Bitwuzla under the MIT license. See COPYING for more
# information at https:#github.com/bitwuzla/bitwuzla/blob/main/COPYING
##

import pytest
import time

from bitwuzla import *

class TestTerminator:
    def __init__(self, time_limit):
        self.start_time = time.time()
        self.time_limit = time_limit

    def __call__(self):
        # Terminate after self.time_limit ms passed
        return (time.time() - self.start_time) * 1000 > self.time_limit

if __name__ == '__main__':

    # No options configured, create Bitwuzla instance with default options.
    bitwuzla = Bitwuzla()

    bv = mk_bv_sort(32)

    x = mk_const(bv)
    s = mk_const(bv)
    t = mk_const(bv)

    a = mk_term(Kind.DISTINCT,
                     [mk_term(Kind.BV_MUL, [s, mk_term(Kind.BV_MUL, [x, t])]),
                      mk_term(Kind.BV_MUL, [mk_term(Kind.BV_MUL, [s, x]), t])])

    # Now, we check that the following formula is unsat.
    # (assert (distinct (bvmul s (bvmul x t)) (bvmul (bvmul s x) t)))
    print('> Without terminator (with preprocessing):')
    print('Expect: unsat')
    print(f'Bitwuzla: {bitwuzla.check_sat(a)}')

    # Now, for illustration purposes, we disable preprocessing, which will
    # significantly increase solving time, and connect a terminator instance
    # that terminates after a certain time limit.
    options = Options()
    options.set(Option.PREPROCESS, False)
    # Create new Bitwuzla instance with reconfigured options.
    bitwuzla2 = Bitwuzla(options)
    # Configure and connect terminator.
    tt = TestTerminator(1)
    bitwuzla2.configure_terminator(tt)

    # Now, we expect Bitwuzla to be terminated during the check-sat call.
    print('> With terminator (no preprocessing):')
    print('Expect: unsat')
    print(f'Bitwuzla: {bitwuzla2.check_sat(a)}')
