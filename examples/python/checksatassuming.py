###
# Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
#
# Copyright (C) 2023 by the authors listed in the AUTHORS file at
# https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
#
# This file is part of Bitwuzla under the MIT license. See COPYING for more
# information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
##

import pytest

from bitwuzla import *

if __name__ == "__main__":

    # No options configured, create Bitwuzla instance with default options.
    bitwuzla = Bitwuzla()

    # Create a bit-vector sort of size 1.
    sortbv1 = mk_bv_sort(1)
    # Create a bit-vector sort of size 2
    sortbv2 = mk_bv_sort(2)

    # Create bit-vector variables.
    # (declare-const o0 (_ BitVec 1))
    o0 = mk_const(sortbv1, 'o0')
    # (declare-const o1 (_ BitVec 1))
    o1 = mk_const(sortbv1, 'o1')
    # (declare-const s0 (_ BitVec 2))
    s0 = mk_const(sortbv2, 's0')
    # (declare-const s1 (_ BitVec 2))
    s1 = mk_const(sortbv2, 's1')
    # (declare-const s2 (_ BitVec 2))
    s2 = mk_const(sortbv2, 's2')
    # (declare-const goal (_ BitVec 2))
    goal = mk_const(sortbv2, 'goal')

    # Create bit-vector values zero, one, three.
    zero  = mk_bv_zero(sortbv2)
    one1  = mk_bv_one(sortbv1)
    one2  = mk_bv_one(sortbv2)
    three = mk_bv_value(sortbv2, 3)

    # Add some assertions.
    bitwuzla.assert_formula(mk_term(Kind.EQUAL, [s0, zero]))
    bitwuzla.assert_formula(mk_term(Kind.EQUAL, [goal, three]))

    # (check-sat-assuming ((= s0 goal)))
    result = bitwuzla.check_sat(mk_term(Kind.EQUAL, [s0, goal]))
    print('Expect: unsat')
    print(f'Bitwuzla: {result}')

    # (assert (= s1 (ite (= o0 (_ sortbv1 1)) (bvadd s0 one) s0)))
    bitwuzla.assert_formula(mk_term(Kind.EQUAL,
                                    [s1,
                                     mk_term(Kind.ITE,
                                             [mk_term(Kind.EQUAL, [o0, one1]),
                                              mk_term(Kind.BV_ADD, [s0, one2]),
                                              s0])]))

    # (check-sat-assuming ((= s1 goal)))
    result = bitwuzla.check_sat(mk_term(Kind.EQUAL, [s1, goal]))
    print('Expect: unsat')
    print(f'Bitwuzla: {result}')

    # (assert (= s2 (ite (= o1 (_ sortbv1 1)) (bvadd s1 one) s1)))
    bitwuzla.assert_formula(mk_term(Kind.EQUAL,
                                     [s2,
                                      mk_term(Kind.ITE,
                                              [mk_term(Kind.EQUAL, [o1, one1]),
                                               mk_term(Kind.BV_ADD, [s1, one2]),
                                               s1])]))

    # (check-sat-assuming ((= s2 goal)))
    result = bitwuzla.check_sat(mk_term(Kind.EQUAL, [s2, goal]))
    print('Expect: unsat')
    print(f'Bitwuzla: {result}')
